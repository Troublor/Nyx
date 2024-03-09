# The worklist algorithm to do abstract interpretation.
from typing import Callable, TypeVar, Iterable

from networkx import DiGraph

N = TypeVar("N")


def abstractly_interpret(
    interpretation_flow_graph: DiGraph,
    transfer_fn: Callable[[Iterable[N], N], bool],
):
    """
    Use worklist algorithm to abstractly interpret a graph.
    The function takes a graph which specifies the interpretation flow between nodes, and a transfer function.
    The flow graph is directed and each edge (n1, n2) means to interpret n2 requires data from n1.
    The transfer function takes all the dependency nodes and the current node,
        and returns whether the current node is changed.
    :param interpretation_flow_graph: a graph in the form of adjacency matrix, specifying the interpretation dependency between nodes.
    :param transfer_fn: the transfer function for interpretation on each node
    :return: None when reaching a fixpoint.
    """
    # The worklist is a list of nodes that need to be interpreted.
    worklist = set(interpretation_flow_graph.nodes)

    while len(worklist) > 0:
        n = worklist.pop()
        dependencies = interpretation_flow_graph.predecessors(n)
        changed = transfer_fn(dependencies, n)
        if changed:
            for m in interpretation_flow_graph.successors(n):
                worklist.add(m)
