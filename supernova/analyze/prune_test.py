import unittest

from analyze.prune import collect_candidate_pairs
from hfg.hybrid_flow_graph import HybridFlowGraph
from lib.test_util import TestSourceCode


class PruneTest(unittest.TestCase):
    def test_pure_functions(self):
        code = """
        contract A {
            function foo(uint x) public returns (uint) {
                return x;
            }
            function bar(uint y) public returns (uint) {
                return foo(y);
            }
        }
        """
        with TestSourceCode(code) as slither:
            cs = slither.contracts
            hfg = HybridFlowGraph(cs)
            paris = collect_candidate_pairs(hfg)
            self.assertEqual(len(paris), 0)

    def test_simple_one_directional_dependency(self):
        code = """
        contract A {
            uint x;
            function foo() public returns (uint) {
                payable(msg.sender).send(x);
            }
            function bar(uint y) public returns (uint) {
                x = y;
            }
        }
        """
        with TestSourceCode(code) as slither:
            cs = slither.contracts
            hfg = HybridFlowGraph(cs)
            paris = collect_candidate_pairs(hfg)
            self.assertEqual(len(paris), 0)

    def test_simple_bidirectional_dependency(self):
        code = """
        contract A {
            uint x;
            function foo() public returns (uint) {
                payable(msg.sender).send(x);
                x = 0;
            }
            function bar(uint y) public returns (uint) {
                payable(msg.sender).send(x + y);
                x = y;
            }
        }
        """
        with TestSourceCode(code) as slither:
            cs = slither.contracts
            hfg = HybridFlowGraph(cs)
            paris = collect_candidate_pairs(hfg)
            self.assertEqual(len(paris), 3)


if __name__ == "__main__":
    unittest.main()
