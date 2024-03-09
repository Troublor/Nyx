import unittest

import networkx as nx

from hfg.hybrid_flow_graph import HybridFlowGraph, Blackhole, Whitehole
from lib.test_util import TestSourceCode


class BasicBlockTest(unittest.TestCase):
    def test_singleton(self):
        w1 = Whitehole()
        w2 = Whitehole()
        b1 = Blackhole()
        b2 = Blackhole()
        self.assertIs(w1, w2)
        self.assertIs(b1, b2)


class HFGTest(unittest.TestCase):
    def test_intra_procedural_control_flow(self):
        code = """
        contract A {
            function bar(uint y) public returns (uint) {
                require(payable(msg.sender).send(y));
                return y + 1;
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            bar = a.get_function_from_signature("bar(uint256)")
            hfg = HybridFlowGraph(slither.contracts)
            whitehole = Whitehole()
            blackhole = Blackhole()

    def test_inter_procedural_call(self):
        code = """
        contract A {
            function foo(uint x) public returns (uint y) {
                y = x + 1;
            }
            function bar(uint y) public returns (uint) {
                return foo(y);
            }
        }
        contract B {
            A a;
            function baz(uint z) public returns (uint) {
                return a.foo(z);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            bar = a.get_function_from_signature("bar(uint256)")
            b = slither.get_contract_from_name("B")[0]
            baz = b.get_function_from_signature("baz(uint256)")
            hfg = HybridFlowGraph(slither.contracts)
            nx.nx_agraph.write_dot(hfg.graph, "hfg.dot")


if __name__ == "__main__":
    unittest.main()
