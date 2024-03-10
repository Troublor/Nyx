import unittest
from copy import copy

from networkx import DiGraph

from lib.abstract_interpretation import abstractly_interpret


class AbstractInterpretationTest(unittest.TestCase):
    def test_simple_souffle_example(self):
        """
        .decl edge(x:number, y:number)
        .input edge

        .decl path(x:number, y:number)
        .output path

        path(x, y) :- edge(x, y).
        path(x, y) :- path(x, z), edge(z, y).
        """
        g = DiGraph()
        g.add_node("edge", relations={(1, 2), (2, 3)})  # relation edge
        g.add_node("path", relations=set())  # relation path
        g.add_edge("edge", "path")
        g.add_edge("path", "path")

        def transfer_fn(deps, n):
            paths = g.nodes["path"]["relations"]
            l1 = len(paths)
            edges = g.nodes["edge"]["relations"]
            l2 = len(edges)
            for edge in copy(edges):
                paths.add(edge)
            for path in copy(paths):
                for edge in edges:
                    if path[1] == edge[0]:
                        paths.add((path[0], edge[1]))
            return l1 != len(paths) or l2 != len(edges)

        abstractly_interpret(g, transfer_fn)
        self.assertEqual({(1, 2), (2, 3), (1, 3)}, g.nodes["path"]["relations"])

        if __name__ == "__main__":
            unittest.main()
