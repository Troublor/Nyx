from __future__ import annotations

import functools
import itertools
from collections import defaultdict

import networkx as nx
from networkx import DiGraph
from slither.analyses.data_dependency.data_dependency import compute_dependency_function
from slither.core.cfg.node import NodeType
from slither.core.context.context import Context
from slither.core.declarations import FunctionContract, Modifier

from hfg.flow import *
from hfg.flow import CallReturnVariable
from hfg.inter_contract import *
from hfg.intra_contract import *
from lib.assets import AssetTransfer, resolve_asset_transfer_op

OUTGOING_KEY = "outgoing"
INCOMING_KEY = "incoming"

ignore_data_flow_in_modifier = True


class AbstractBasicBlock(Context):
    pass


class Blackhole(AbstractBasicBlock):
    singleton = None

    def __new__(cls, *args, **kwargs):
        if not Blackhole.singleton:
            Blackhole.singleton = super().__new__(cls)
        return Blackhole.singleton

    def __str__(self):
        return "Blackhole"


class Whitehole(AbstractBasicBlock):
    singleton = None

    def __new__(cls, *args, **kwargs):
        if not Whitehole.singleton:
            Whitehole.singleton = super().__new__(cls)
        return Whitehole.singleton

    def __str__(self):
        return "Whitehole"


class StorageSlot(AbstractBasicBlock):
    storage_map: Dict[StateVariable, StorageSlot] = {}

    def __new__(cls, state: StateVariable):
        if state in StorageSlot.storage_map:
            return StorageSlot.storage_map[state]
        else:
            return super().__new__(cls)

    def __init__(self, state: StateVariable):
        """
        Same state variable will always result in the same storage slot.
        :param state:
        """
        super().__init__()
        self.state = state
        StorageSlot.storage_map[state] = self

    def __eq__(self, other):
        return isinstance(other, StorageSlot) and self.state == other.state

    def __hash__(self):
        return hash(("StorageSlot", self.state))

    def __str__(self):
        return f"StorageSlot({self.state})"


class NodeBlock(AbstractBasicBlock):
    node_duplicate_map: Dict[Node, int] = defaultdict(int)

    def __init__(self, node: Node):
        """
        Initializing a basic block with the same node twice will result in a different basic block.
        :param node:
        """
        super().__init__()
        self.node = node
        # context-sensitive index
        self.cs_index = NodeBlock.node_duplicate_map[node]
        NodeBlock.node_duplicate_map[node] += 1
        self.op_transfers_map: Dict[Operation, List[AssetTransfer]] = {
            op: resolve_asset_transfer_op(op) for op in node.irs_ssa
        }

    @property
    def transfers(self) -> Iterable[AssetTransfer]:
        return itertools.chain.from_iterable(self.op_transfers_map.values())

    @property
    def is_transfer(self) -> bool:
        return len(list(self.transfers)) > 0

    def __eq__(self, other):
        return (
            isinstance(other, NodeBlock)
            and self.node == other.node
            and self.cs_index == other.cs_index
        )

    def __hash__(self):
        return hash(("BasicBlock", self.node, self.cs_index))

    def __str__(self):
        fn = self.node.function
        if isinstance(fn, FunctionContract):
            c = fn.contract.name
        else:
            c = "Solidity"
        node = (
            str(self.node)
            if self.node.type in [NodeType.ENTRYPOINT, NodeType.OTHER_ENTRYPOINT]
            else "L" + ",".join(map(str, self.node.source_mapping.lines))
        )
        return f'"{c}.{fn}: {node} ({self.cs_index})"'


class Flows(Set[Flow]):
    def __init__(self, *flows: Flow):
        super().__init__()
        for flow in flows:
            self.add(flow)

    def __str__(self):
        return " | ".join({f'"{str(f)}"' for f in self})

    def add_flow(self, *flow: Flow) -> Flows:
        for f in flow:
            self.add(f)
        return self


class HybridFlowGraph(object):
    """
    A hybrid flow graph is a graph that contains both control flow and data flow.
    Each node is a GraphNode and each edge is associated with a Flows object as attribute.
    The graph should be flow sensitive, intra-contract context-sensitive.
    """

    def __init__(
        self,
        all_contracts: Iterable[Contract],
        analyze_contracts: Iterable[Contract] = None,
    ):
        super().__init__()
        self.__summarized_functions = set()
        self.all_contracts = all_contracts
        self.analyze_contracts = analyze_contracts or all_contracts
        self._g = DiGraph()
        # blackhole is a pseudo block that represents the single entry point of all transactions
        self.blackhole = Blackhole()
        self._g.add_node(self.blackhole)
        # whitehole is a pseudo block that represents the single exit point of all transactions
        self.whitehole = Whitehole()
        self._g.add_node(self.whitehole)

        for contract in self.analyze_contracts:
            for fn in contract.functions + contract.modifiers:
                if fn.visibility in ["public", "external"] and fn.is_implemented:
                    entry, returns, _, _ = self.__process_fn([], fn)
                    # add entry edge
                    self.__add_flows(
                        self.whitehole,
                        entry,
                        IntraProceduralControlFlow(),
                    )
                    # add return edge
                    for ret in returns:
                        self.__add_flows(
                            ret,
                            self.blackhole,
                            IntraProceduralControlFlow(),
                        )

        for edge in self._g.edges:
            lbls = set()
            for flow in self._g.edges[edge]["flows"]:
                if isinstance(flow, IntraProceduralControlFlow):
                    lbls.add("c")
                elif isinstance(flow, InterProceduralCallFlow):
                    lbls.add("C")
                elif isinstance(flow, IntraTransactionDataFlow):
                    lbls.add("d")
                elif isinstance(flow, InterTransactionDataFlow):
                    lbls.add("D")
            self._g.edges[edge]["label"] = ",".join(lbls)

        for node in self._g.nodes:
            assert isinstance(node, AbstractBasicBlock)
            node.context[INCOMING_KEY] = [
                (src, self._g.edges[src, node]["flows"])
                for src in self._g.predecessors(node)
            ]
            node.context[OUTGOING_KEY] = [
                (self._g.edges[node, dst]["flows"], dst)
                for dst in self._g.successors(node)
            ]

    def __summarize_fn(self, fn: Function):
        compute_dependency_function(fn)
        summarize_intra_procedural_profits(fn)
        summarize_intra_procedural_data_flow(fn)
        summarize_intra_procedural_internal_call_edges(fn)
        summarize_intra_procedural_external_call_edges(self.all_contracts, fn)

    def __add_flows(self, src: AbstractBasicBlock, dst: AbstractBasicBlock, flow: Flow):
        if self._g.has_edge(src, dst):
            self._g.edges[src, dst]["flows"].add_flow(flow)
        else:
            self._g.add_edge(src, dst, flows=Flows(flow))

    def __process_fn_df_summary_source(
        self,
        _fn: Function,
        bbs: Dict[Node, NodeBlock],
        _dst: AbstractBasicBlock,
        _dst_var: Union[StateVariable, PseudoVariable],
        source: IntraProceduralDataFlowSource,
    ):
        # source is function parameter
        _src = bbs[_fn.entry_point]
        for idx in source["parameters"]:
            _src_var = FunctionParamVariable(_fn, idx)
            if isinstance(_dst, StorageSlot):
                _flow = InterTransactionDataFlow(_src_var, _dst_var)
            else:
                _flow = IntraTransactionDataFlow(_src_var, _dst_var)
            self.__add_flows(_src, _dst, _flow)

        # source is state read
        for state in source["states"]:
            _src = StorageSlot(state.non_ssa_version)
            _flow = InterTransactionDataFlow(
                state.non_ssa_version,
                _dst_var,
            )
            self.__add_flows(_src, _dst, _flow)

        # source is call return
        for call, idx in source["call_returns"]:
            _src = bbs[call.node]
            _src_var = CallReturnVariable(call, idx)
            if isinstance(_dst, StorageSlot):
                _flow = InterTransactionDataFlow(_src_var, _dst_var)
            else:
                _flow = IntraTransactionDataFlow(_src_var, _dst_var)
            self.__add_flows(_src, _dst, _flow)

    def __process_fn_sink_summary(
        self,
        _fn: Function,
        bbs: Dict[Node, NodeBlock],
        summary: IntraProceduralDataFlowSinkSummary,
    ):
        """
        Process a data flow sink summary, add flows to the graph.
        :param _fn:
        :param bbs:
        :param summary:
        :return:
        """

        # various kinds of sinks
        if isinstance(summary, StateSinkSummary):
            dst = StorageSlot(summary.state.non_ssa_version)
            self.__process_fn_df_summary_source(
                _fn, bbs, dst, summary.state.non_ssa_version, summary.sources
            )
            # special case when assigning to a state variable does not use any local variables
            # We usually need not worry about constants since there always exists a control flow.
            # But for storage writes, there is no control flow to StorageSlot (the abstract block)
            # So we need to add a flow from assignment to StorageSlot
            src = bbs[summary.store.node]
            src_var = summary.state
            self.__add_flows(
                src,
                dst,
                InterTransactionDataFlow(src_var, summary.state.non_ssa_version),
            )
        elif isinstance(summary, ReturnSinkSummary):
            dst = bbs[summary.node]
            _dst_var = FunctionReturnVariable(_fn, summary.idx)
            self.__process_fn_df_summary_source(
                _fn, bbs, dst, _dst_var, summary.sources
            )
        elif isinstance(summary, ConditionSinkSummary):
            dst = bbs[summary.node]
            self.__process_fn_df_summary_source(
                _fn, bbs, dst, WrappedSlithIRVariable(summary.var), summary.sources
            )
        elif isinstance(summary, CallArgSinkSummary):
            dst = bbs[summary.node]
            _dst_var = CallArgVariable(summary.call, summary.idx)
            self.__process_fn_df_summary_source(
                _fn, bbs, dst, _dst_var, summary.sources
            )
        elif isinstance(summary, ProfitSinkSummary):
            dst = bbs[summary.node]
            self.__process_fn_df_summary_source(
                _fn, bbs, dst, WrappedSlithIRVariable(summary.var), summary.sources
            )

    def __process_fn(
        self, call_stack: List[Function], _fn: Function
    ) -> Tuple[
        AbstractBasicBlock,
        List[AbstractBasicBlock],
        List[AbstractBasicBlock],
        Dict[Node, NodeBlock],
    ]:
        """
        Add one public function to the HFG.
        Note that we will go nested into callee functions and inline them
        to make the graph as context-sensitive as possible.
        Recursive calls are not inlined.
        :param call_stack: all callers
        :param _fn:
        :return: entry node, return nodes, throw nodes, map from node to node block
        """
        if _fn not in self.__summarized_functions:
            self.__summarize_fn(_fn)
            self.__summarized_functions.add(_fn)

        bbs: Dict[Node, NodeBlock] = {node: NodeBlock(node) for node in _fn.nodes}
        return_nodes: List[Node] = []
        inherited_return_bbs: List[AbstractBasicBlock] = []
        throw_nodes: List[Node] = []

        for n, bb in bbs.items():
            # intra-procedural control flow
            if any(
                map(
                    lambda _op: isinstance(_op, SolidityCall)
                    and ("throw" in _op.function.name or "revert" in _op.function.name),
                    n.irs_ssa,
                )
            ):
                self.__add_flows(bb, self.blackhole, IntraProceduralControlFlow())
                throw_nodes.append(n)
            elif len(n.sons) == 0:
                return_nodes.append(n)
            else:
                for son in n.sons:
                    succ = bbs[son]
                    self.__add_flows(bb, succ, IntraProceduralControlFlow())

            # special handle for require: one more edge to blackhole
            if any(
                map(
                    lambda _op: isinstance(_op, SolidityCall)
                    and (
                        "require" in _op.function.name or "assert" in _op.function.name
                    ),
                    n.irs_ssa,
                )
            ):
                self.__add_flows(bb, self.blackhole, IntraProceduralControlFlow())
                throw_nodes.append(n)

            # intra-procedural data flow
            for op in n.irs_ssa:
                for sink_summary in op.context[DATA_FLOW_SINK_KEY]:
                    self.__process_fn_sink_summary(_fn, bbs, sink_summary)

            # inter-procedural call and inter-procedural data flow
            for op in n.irs_ssa:
                callees: Set[Function] = set()
                if INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY in op.context:
                    callees |= op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY]
                if INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY in op.context:
                    callees |= op.context[INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY]
                for callee in callees:
                    if callee in call_stack:
                        # don't inline recursive calls
                        continue
                    entry, return_bbs, _, callee_bbs = self.__process_fn(
                        call_stack + [_fn], callee
                    )  # context-sensitive inlining
                    if ignore_data_flow_in_modifier and isinstance(callee, Modifier):
                        # don't analyze modifiers
                        continue
                    # call control flow
                    self.__add_flows(bb, entry, InterProceduralCallFlow(op, callee))
                    # return control flow
                    for return_bb in return_bbs:
                        if len(bb.node.sons) > 0:
                            for son in bb.node.sons:
                                self.__add_flows(
                                    return_bb,
                                    bbs[son],
                                    InterProceduralReturnFlow(op, callee),
                                )
                        else:
                            inherited_return_bbs.append(return_bb)
                    # call argument data flow
                    for i in range(len(callee.parameters_ssa)):
                        src_var = CallArgVariable(op, i + 1)
                        dst_var = FunctionParamVariable(callee, i + 1)
                        flow = IntraTransactionDataFlow(src_var, dst_var)
                        self.__add_flows(bb, entry, flow)
                    # call return data flow
                    # find all nodes with ReturnSinkSummary (return index (starting from 1) => set of nodes)
                    returns: Dict[int, Set[Node]] = {
                        i + 1: set() for i in range(len(callee.returns))
                    }
                    for _op in callee.slithir_ssa_operations:
                        return_summaries: List[ReturnSinkSummary] = [
                            summary
                            for summary in _op.context[DATA_FLOW_SINK_KEY]
                            if isinstance(summary, ReturnSinkSummary)
                        ]
                        for summary in return_summaries:
                            returns[summary.idx].add(_op.node)
                    for idx, ns in returns.items():
                        for _n in ns:
                            src_var = FunctionReturnVariable(callee, idx)
                            dst_var = CallReturnVariable(op, idx)
                            flow = IntraTransactionDataFlow(src_var, dst_var)
                            self.__add_flows(callee_bbs[_n], bb, flow)

        if _fn.entry_point is None:
            print(_fn.canonical_name)

        return (
            bbs[_fn.entry_point],
            inherited_return_bbs + [bbs[r] for r in return_nodes],
            [bbs[t] for t in throw_nodes],
            bbs,
        )

    @functools.cached_property
    def public_entries(self) -> List[NodeBlock]:
        """
        Get all public entry nodes.
        :return:
        """
        return [
            n
            for n in self._g.successors(self.whitehole)
            if isinstance(n, NodeBlock)
            and isinstance(n.node.function, FunctionContract)
            and n.node.function.contract in self.analyze_contracts
            and n.node.type == NodeType.ENTRYPOINT
            and n.node.function.visibility in ["public", "external"]
            and n.node.function.is_implemented
            and not n.node.function.is_shadowed
            and not n.node.function.is_constructor
        ]

    @property
    def graph(self) -> DiGraph:
        """
        Get the underlying graph.
        :return:
        """
        return self._g

    @property
    def transfer_blocks(self) -> Iterable[NodeBlock]:
        return filter(
            lambda b: isinstance(b, NodeBlock) and b.is_transfer, self.graph.nodes
        )

    @property
    def transfer_control_dependencies(self) -> dict[NodeBlock, set[NodeBlock]]:
        """
        Given an entry point, get all control dependencies of a node.
        :return: a dict: control dependency node => set of transfer nodes
        """
        # control dependency node => set of transfer nodes
        deps: dict[NodeBlock, set[NodeBlock]] = defaultdict(set)
        edges = []
        for e in self.graph.edges:
            f, t = e
            for flow in self._g.edges[e]["flows"]:
                if (
                    isinstance(
                        flow,
                        (
                            IntraProceduralControlFlow,
                            InterProceduralCallFlow,
                            InterProceduralReturnFlow,
                        ),
                    )
                    and not isinstance(t, StorageSlot)
                    and not isinstance(f, StorageSlot)
                ):
                    edges.append(e)
        # subgraph with only control flow edges and without StorageSlot nodes
        sub_graph = self.graph.edge_subgraph(edges)
        post_dom_frontiers = nx.dominance_frontiers(
            sub_graph.reverse(copy=False), self.blackhole
        )

        def transitive_dep(
            _n: NodeBlock, _transfer: NodeBlock, _visited: set[NodeBlock] = None
        ):
            if _visited is None:
                _visited = set()
            _visited.add(_n)
            if _n not in post_dom_frontiers:
                return
            frontiers = post_dom_frontiers[_n]
            for frontier in frontiers:
                if not isinstance(frontier, NodeBlock) or frontier in _visited:
                    continue
                deps[frontier].add(_transfer)
                transitive_dep(frontier, _transfer, _visited)

        for transfer_node in self.transfer_blocks:
            # n control-depends on m if m is a post-dominance frontier of n
            # we also transitively considers the control dependency of control dependency
            transitive_dep(transfer_node, transfer_node)

        return deps
