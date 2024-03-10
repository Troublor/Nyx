import unittest

from hfg.inter_contract import (
    summarize_intra_procedural_external_call_edges,
    INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY,
)
from lib.test_util import TestSourceCode


class InterContractTest(unittest.TestCase):
    def test_call_edges(self):
        code = """
        contract A {
            function foo(uint x) public returns (uint) {
                return x;
            }
        }
        contract B {
            A a;
            function bar(uint x) public returns (uint) {
                return a.foo(x);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            b = slither.get_contract_from_name("B")[0]
            bar = b.get_function_from_signature("bar(uint256)")
            summarize_intra_procedural_external_call_edges(slither.contracts, bar)
            self.assertEqual(
                {foo},
                bar.slithir_ssa_operations[1].context[
                    INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY
                ],
            )

    def test_ignore_token_function_call(self):
        code = """
        contract Token {
            function transfer(address to, uint256 value) public returns (bool) {
                return true;
            }
        }
        contract A {
            Token token;
            function foo(uint x) public {
                token.transfer(msg.sender, x);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            summarize_intra_procedural_external_call_edges(slither.contracts, foo)
            for op in foo.slithir_ssa_operations:
                self.assertNotIn(INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY, op.context)


if __name__ == "__main__":
    unittest.main()
