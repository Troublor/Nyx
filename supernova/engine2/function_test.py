import unittest

import z3
from slither import Slither
from slither.analyses.data_dependency.data_dependency import compute_dependency_function

from engine2.summary_builder import FunctionSummaryBuilder
from engine2.msg_call import MsgCall
from engine2.state import State
from hfg.inter_contract import summarize_intra_procedural_external_call_edges
from hfg.intra_contract import (
    summarize_intra_procedural_profits,
    summarize_intra_procedural_data_flow,
    summarize_intra_procedural_internal_call_edges,
)
from lib.test_util import TestSourceCode


class FunctionTest(unittest.TestCase):
    def preprocess(self, slither: Slither):
        for contract in slither.contracts:
            for fn in contract.functions:
                compute_dependency_function(fn)
                summarize_intra_procedural_profits(fn)
                summarize_intra_procedural_data_flow(fn)
                summarize_intra_procedural_internal_call_edges(fn)
                summarize_intra_procedural_external_call_edges(slither.contracts, fn)

    def test_simple_function(self):
        code = """
        contract A {
            uint x;
            function foo(uint y) public returns (uint) {
                uint i = 1;
                if (x > 0) {
                    x = x + 1;
                } else {
                    x = y + i;
                }
                payable(msg.sender).transfer(x);
                return y + 1;
            }

            function bar(uint y) public returns (uint) {
                y = foo(y);
                y = foo(y);
                return y;
            }

        }
        """
        with TestSourceCode(code) as slither:
            self.preprocess(slither)
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            summary = FunctionSummaryBuilder(foo, slither.contracts)
            summaries = dict()
            visited = set()
            summary.build(summaries, visited)

            state = State(slither.contracts)
            state.load_contract(a).load("x").val = z3.Int("x")
            msg_call = MsgCall(
                z3.BitVec("sender", 160), z3.BitVec("value", 32), z3.BitVec("this", 160)
            )
            r = summary.apply(
                state,
                msg_call,
                (
                    z3.Int(
                        "y",
                    ),
                ),
            )
            print()

            bar = a.get_function_from_signature("bar(uint256)")
            summary_bar = FunctionSummaryBuilder(bar, slither.contracts)
            summary_bar.build(summaries, visited)
            print()


if __name__ == "__main__":
    unittest.main()
