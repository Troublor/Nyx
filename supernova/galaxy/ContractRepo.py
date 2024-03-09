import json
from abc import ABC
from functools import cached_property
from pathlib import Path
from typing import TypedDict

from crytic_compile import CryticCompile, CompilationUnit
from slither import Slither
from slither.core.declarations import Contract

from lib.solc_ast import AstWalker
from lib.solidity import get_solc_path
from lib.types import *


class ContractMetadataMain(TypedDict):
    file: Path
    contract: str


class ContractMetadata(TypedDict):
    address: Address
    codeHash: Hash
    main: ContractMetadataMain


class ContractRepo(ABC):
    @property
    def slither(self) -> Slither:
        raise NotImplementedError()

    @property
    def name(self) -> str:
        raise NotImplementedError()

    @property
    def root(self) -> Path:
        raise NotImplementedError()


class CryticCompileRepo(ContractRepo):
    def __init__(self, root: Path):
        self._root = root
        self._crytic_compile = None
        self._slither = None

    @property
    def root(self) -> Path:
        return self._root

    @property
    def name(self) -> str:
        return self.root.name

    @cached_property
    def crytic_compile(self) -> CryticCompile:
        if self._crytic_compile is None:
            # noinspection PyTypeChecker
            self._crytic_compile = CryticCompile(
                self.root.__str__(),
                # foundry_out_directory="forge-out",
                # foundry_ignore_compile=True,
            )
            for _, file in self._crytic_compile.compilation_units.items():
                AstTransformer(file).transform()
        return self._crytic_compile

    @cached_property
    def slither(self) -> Slither:
        if self._slither is None:
            self._slither = Slither(self.crytic_compile)
        return self._slither


class ContractRepoRaw(ContractRepo):
    def __init__(self, root: Path, addr: Address = None):
        self._crytic_compile = None
        self._slither = None
        self._root = root
        self.address = addr if addr else self.source_address

    @property
    def root(self) -> Path:
        return self._root

    @cached_property
    def source_address(self) -> Address:
        return self.metadata["address"]

    @cached_property
    def config(self) -> dict:
        with open(self.root.joinpath("config.json")) as f:
            return json.load(f)

    @cached_property
    def compiler_input(self) -> dict:
        with open(self.root.joinpath("compiler-input.json")) as f:
            return json.load(f)

    @cached_property
    def metadata(self) -> ContractMetadata:
        with open(self.root.joinpath("metadata.json")) as f:
            return json.load(f)

    @cached_property
    def compiler_version(self) -> str:
        return self.config["version"]

    @cached_property
    def main_file(self) -> Path:
        return self.root.joinpath("src", self.metadata["main"]["file"])

    @cached_property
    def name(self) -> str:
        return self.metadata["main"]["contract"]

    @cached_property
    def crytic_compile(self) -> CryticCompile:
        if self._crytic_compile is None:
            # noinspection PyTypeChecker
            self._crytic_compile = CryticCompile(
                self.metadata["main"]["file"].__str__(),
                solc=get_solc_path(self.compiler_version).__str__(),
                solc_args="--optimize",  # enable optimizer (especially YulOptimizer) to avoid stack too deep errors
                solc_working_dir=self.root.joinpath("src").__str__(),
                solc_disable_warnings=True,
            )
            for _, file in self._crytic_compile.compilation_units.items():
                AstTransformer(file).transform()
        return self._crytic_compile

    @cached_property
    def slither(self) -> Slither:
        if self._slither is None:
            self._slither = Slither(self.crytic_compile)
        return self._slither

    @cached_property
    def main_contract(self) -> Contract:
        return self.slither.get_contract_from_name(self.name)[0]


tmp_var_idx = 1000000
ast_node_idx = 1000000


class AstTransformer(AstWalker):
    def __init__(self, compilation_unit: CompilationUnit):
        self.compilation_unit = compilation_unit
        assert len(self.compilation_unit.asts) > 0
        super().__init__("nodeType" in next(iter(self.compilation_unit.asts.values())))
        self.round = 0
        # round 0
        self._max_node_id = 0
        self.fn_decl_node_map: dict[int, dict] = {}
        # round 1
        self.last_block: dict | None = None
        self.blk_stmt_idx: int = -1

    def transform(self):
        self.round = 0
        for _, ast in self.compilation_unit.asts.items():
            self._walk(ast)
        # global ast_node_idx
        # ast_node_idx = self._max_node_id + 1
        self.round = 1
        for _, ast in self.compilation_unit.asts.items():
            self._walk(ast)

    def _visit(
        self, node: dict, parent: dict = None, field: str = None, idx: int = None
    ) -> None:
        if self.round == 0:
            if "id" in node:
                node_id = node["id"]
                if node_id > self._max_node_id:
                    self._max_node_id = node_id
                if node[self._type_key] == "FunctionDefinition":
                    self.fn_decl_node_map[node_id] = node
        elif self.round == 1:
            if parent is self.last_block and field == "statements":
                self.blk_stmt_idx = idx
            node_type = node[self._type_key]
            if node_type == "Block":
                self.last_block = node
            elif node_type == "FunctionCall" and node["kind"] == "functionCall":
                key = self._get_child_key("arguments")
                arguments = node[key]
                for arg_idx, argument in enumerate(arguments):
                    if argument[self._type_key] == "Conditional":
                        self._transform_conditional_call_arg(node, argument, arg_idx)

    def _transform_conditional_call_arg(self, call: dict, arg: dict, arg_idx: int):
        assert self.last_block is not None
        if self.blk_stmt_idx < 0:
            print()
        assert self.blk_stmt_idx >= 0
        global tmp_var_idx, ast_node_idx
        decl_idx = ast_node_idx
        ast_node_idx += 1
        typeName_node_idx = ast_node_idx
        ast_node_idx += 1
        decl_stmt_idx = ast_node_idx
        ast_node_idx += 1
        var_name = f"__tmp{tmp_var_idx}"
        tmp_var_idx += 1
        src = arg["src"]
        scope = self.last_block["id"]
        fn_decl_id = call["expression"]["referencedDeclaration"]
        if fn_decl_id is None or fn_decl_id < 0:
            # solidity builtin functions
            return
        assert fn_decl_id in self.fn_decl_node_map
        fn_decl = self.fn_decl_node_map[fn_decl_id]
        parameter_decl = fn_decl["parameters"]["parameters"][arg_idx]
        typeName = parameter_decl["typeName"]
        typeName["id"] = typeName_node_idx
        tmp_var_decl_stmt = {
            "assignments": [decl_idx],
            "declarations": [
                {
                    "constant": False,
                    "id": decl_idx,
                    "mutability": "mutable",
                    "name": var_name,
                    "nameLocation": src,
                    "nodeType": "VariableDeclaration",
                    "scope": scope,
                    "src": src,
                    "stateVariable": False,
                    "storageLocation": "default",
                    "typeDescriptions": arg["typeDescriptions"],
                    "typeName": typeName,
                    "visibility": "internal",
                }
            ],
            "id": decl_stmt_idx,
            "initialValue": arg,
            "nodeType": "VariableDeclarationStatement",
            "src": arg["src"],
        }
        self.last_block["statements"].insert(self.blk_stmt_idx, tmp_var_decl_stmt)

        identifier_node_idx = ast_node_idx
        ast_node_idx += 1
        tmp_var_identifier = {
            "id": identifier_node_idx,
            "name": var_name,
            "nodeType": "Identifier",
            "overloadedDeclarations": [],
            "referencedDeclaration": decl_idx,
            "src": src,
            "typeDescriptions": arg["typeDescriptions"],
        }
        call["arguments"][arg_idx] = tmp_var_identifier
