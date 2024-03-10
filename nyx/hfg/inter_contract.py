from typing import Set, Iterable

from slither.core.declarations import Function, Contract
from slither.slithir.operations import (
    Operation,
    HighLevelCall,
    LowLevelCall,
    SolidityCall,
)

from lib.assets import is_token_function_call

# In the context of an operation, this key is used to store the set of functions that are called by this operation
INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY = "intra_procedural_external_call_edge"

# In the context of a function, this key is used to store the set of operations that calls this function
INTRA_PROCEDURAL_EXTERNAL_CALLER_KEY = "intra_procedural+external_caller"

InterContractCallees = Set[Function]


def summarize_intra_procedural_external_call_edges(
    contracts: Iterable[Contract], fn: Function
):
    """
    Summarize the inter_contract call graph:
    :param contracts:
    :param fn:
    :return:
    """

    def infer_high_level_callee_fns(
        call_site: Operation,
    ) -> Set[Function]:
        return {
            f
            for c in contracts
            for f in c.functions
            if call_site.function is not None
            and isinstance(call_site.function, Function)
            and f.signature_str == call_site.function.signature_str
            and f.is_implemented  # the function must be implemented
            and not f.is_shadowed
            and f.visibility in ["public", "external"]
        }

    def infer_low_level_callee_fns(call_site: Operation) -> Set[Function]:
        # TODO
        return set()

    def infer_asm_callee_fns(call_site: Operation) -> Set[Function]:
        # TODO
        return set()

    for op in fn.slithir_ssa_operations + fn.slithir_operations:
        if (
            isinstance(op, (HighLevelCall, LowLevelCall))
            or isinstance(op, SolidityCall)
            and op.function.full_name
            in [
                "call(uint256,uint256,uint256,uint256,uint256,uint256,uint256)",
                "callcode(uint256,uint256,uint256,uint256,uint256,uint256,uint256)",
                "delegatecall(uint256,uint256,uint256,uint256,uint256,uint256)",
                "staticcall(uint256,uint256,uint256,uint256,uint256,uint256)",
            ]
        ):
            if is_token_function_call(op):
                # we don't trace message call to token transfer functions
                continue
            callees: InterContractCallees = set()
            op.context[INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY] = callees

            # High level calls
            callees |= infer_high_level_callee_fns(op)

            # Low level calls
            callees |= infer_low_level_callee_fns(op)

            # Assembly calls
            callees |= infer_asm_callee_fns(op)

            # set INTER_CONTRACT_CALLER_KEY for each callee function
            for callee in callees:
                if INTRA_PROCEDURAL_EXTERNAL_CALLER_KEY not in callee.context:
                    callee.context[INTRA_PROCEDURAL_EXTERNAL_CALLER_KEY] = set()
                callee.context[INTRA_PROCEDURAL_EXTERNAL_CALLER_KEY].add(op)
