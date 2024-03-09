from __future__ import annotations

from typing import List, Tuple, Dict, Union

from slither.core.declarations import FunctionContract, Modifier, SolidityFunction
from slither.core.declarations.function_top_level import FunctionTopLevel

from lib.graph import LabelledGraph
from supernova.lib.token import is_token_transfer_fn


class MsgCallGraph(LabelledGraph[FunctionContract, str]):
    """
    The message call graph (MCG) between public functions.
    The nodes in MCG are all public functions in the contract group.
    The graph nodes are labelled with the Slither function object.
     node in SlithIR.

    Proxy contracts are inferred and skipped in the MCG.
    """

    def __init__(self):
        super().__init__()

    @staticmethod
    def from_contract_group(contract_group) -> MsgCallGraph:
        """
        Build the message call graph (MCG) between public functions using ContractGroup.
        :param contract_group:
        :return:
        """
        g = MsgCallGraph()
        contracts = [repo.main_contract for repo in contract_group.contract_repos]

        def infer_high_level_callee_fns(
            callee: FunctionContract,
        ) -> List[FunctionContract]:
            # Find the functions with same signature in all contracts
            return [
                f
                for c in contracts
                for f in c.functions
                if f.full_name == callee.full_name
                and f.is_implemented  # the function must be implemented
                and f.visibility in ["public", "external"]
                and not is_token_transfer_fn(
                    f
                )  # we don't trace message call to token transfer functions
            ]

        def infer_low_level_callee_fns(
            caller: FunctionContract,
        ) -> List[FunctionContract]:
            # TODO
            return []

        def infer_asm_callee_fns(caller: FunctionContract) -> List[FunctionContract]:
            # TODO
            return []

        def infer_call_edges(
            _fn: FunctionContract,
        ) -> List[Tuple[FunctionContract, ""]]:
            _edges = []

            # Internal calls
            for callee in _fn.internal_calls:
                _edges.append((callee, ""))

            # High level calls
            for c, f in _fn.high_level_calls:
                if c.is_library:
                    # library calls are not message calls
                    # TODO what if the library is a dynamic library?
                    continue
                callees = infer_high_level_callee_fns(f)
                _edges.extend([(callee, "") for callee in callees])

            # Low level calls
            callees = infer_low_level_callee_fns(_fn)
            _edges.extend([(callee, "") for callee in callees])

            # Assembly calls
            callees = infer_asm_callee_fns(_fn)
            _edges.extend([(callee, "") for callee in callees])

            return _edges

        for contract in contracts:
            all_fns = contract.functions + contract.modifiers
            fn_call_edges: Dict[
                Union[FunctionContract, Modifier],
                List[Union[FunctionContract, Modifier]],
            ] = {
                # this contains internal functions
                fn: infer_call_edges(fn)
                for fn in all_fns
            }

            def aggregate_call_edges(
                fn: FunctionContract,
            ) -> List[Tuple[FunctionContract, ""]]:
                _edges = []
                if fn not in fn_call_edges:
                    print()
                for callee, label in fn_call_edges[fn]:
                    if isinstance(callee, FunctionContract) and callee.visibility in [
                        "public",
                        "external",
                    ]:
                        _edges.append((callee, label))
                        continue
                    if isinstance(callee, FunctionContract) and callee.is_constructor:
                        continue
                    if isinstance(callee, SolidityFunction):
                        continue
                    if isinstance(callee, FunctionTopLevel):
                        continue
                    _edges.extend(aggregate_call_edges(callee))
                return _edges

            fns = [
                f
                for f in contract.functions
                if isinstance(f, FunctionContract)
                and f.visibility in ["public", "external"]
            ]
            g.add_nodes(*fns)
            for fn in fns:
                edges = aggregate_call_edges(fn)
                g.add_edges(*[(fn, callee, label) for callee, label in edges])

        return g
