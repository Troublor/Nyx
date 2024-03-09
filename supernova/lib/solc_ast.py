from abc import ABC, abstractmethod
from typing import Iterable


class AstWalker(ABC):
    def __init__(self, is_compact: bool):
        self._is_compact = is_compact

    def _walk(
        self, node: dict, parent: dict = None, field: str = None, idx: int = None
    ):
        self._visit(node, parent, field, idx)
        # node_type = node[self._type_key]
        # if node_type == "SourceUnit":
        #     for child in node["nodes"]:
        #         self._walk(child, node, "nodes", 0)
        # elif node_type == "ContractDefinition":
        #     for child in node["nodes"]:
        #         self._walk(child, node, "nodes", 0)
        # elif node_type == "FunctionDefinition":
        #     if "body" in node:
        #         self._walk(node["body"], node, "body", 0)
        # elif node_type == "Block":
        #     key = self._get_child_key("statements")
        #     for i, statement in enumerate(node[key]):
        #         self._walk(statement, node, key, i)
        # elif node_type == "ExpressionStatement":
        #     key = self._get_child_key("expression")
        #     self._walk(node[key], node, key, -1)
        # elif node_type == "Assignment":
        #     key = self._get_child_key("leftHandSide")
        #     self._walk(node[key], node, key, -1)
        #     self._walk(node[key], node, key, -1)
        # elif node_type == "FunctionCall":
        #     key = self._get_child_key("expression")
        #     self._walk(node[key], node, key, -1)
        #     key = self._get_child_key("arguments")
        #     for i, arg in enumerate(node[key]):
        #         self._walk(arg, node, key, -1)
        # elif node_type == "IfStatement":
        #     key = self._get_child_key("trueBody")
        #     self._walk(node[key], node, key, -1)
        #     key = self._get_child_key("falseBody")
        #     if key in node:
        #         self._walk(node[key], node, key, -1)
        # else:
        children = list(self._get_all_possible_child_nodes(node))
        for (
            child,
            parent,
            key,
            idx,
        ) in children:
            self._walk(child, parent, key, idx)

    @abstractmethod
    def _visit(
        self, node: dict, parent: dict = None, field: str = None, idx: int = None
    ):
        pass

    @property
    def _type_key(self) -> str:
        return "name" if not self._is_compact else "nodeType"

    def _get_child_key(self, key: str) -> str:
        return key if self._is_compact else "children"

    def _get_all_possible_child_nodes(
        self, node: dict
    ) -> Iterable[tuple[dict, dict, str, int]]:
        for key, val in node.items():
            if isinstance(val, dict) and ("nodeType" in val or "children" in val):
                yield (val, node, key, -1)
            elif isinstance(val, list):
                for i, item in enumerate(val):
                    if isinstance(item, dict) and (
                        "nodeType" in item or "children" in item
                    ):
                        yield (item, node, key, i)
