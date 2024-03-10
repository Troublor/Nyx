"""
This module uses abstract interpretation to select pairs of public functions
that may be vulnerable to front-running attacks.
"""
from __future__ import annotations

import functools
import itertools
from collections import defaultdict
from copy import copy
from typing import Tuple, Dict, Set, List, Iterable

from slither.core.cfg.node import NodeType
from slither.core.declarations import FunctionContract

from hfg.flow import *
from hfg.hybrid_flow_graph import (
    HybridFlowGraph,
    AbstractBasicBlock,
    NodeBlock,
    StorageSlot,
)
from hfg.intra_contract import (
    DATA_FLOW_SINK_KEY,
    ProfitSinkSummary,
    ConditionSinkSummary,
)
from lib.abstract_interpretation import abstractly_interpret


def set_merge(x: Set, y: Set) -> Set:
    return x | y


class NodeSummary(object):
    """
    -- c: control flow edge (intra-procedural)
    -- C: function call graph edge (both external/internal)
    -- d: intra-transaction data flow edge
    -- D: inter-transaction data flow edge

    """

    def __init__(self, n: AbstractBasicBlock):
        self.block = n

        """
        N: set of nodes in the control flow graph
        V: set of variable in the contract
        S: set of state variable in the contract
        """

        # w -> { u | w, u ∈ N, u ∈ ⊕ (n, w) ~ [cC], path(n, u) ~ [cC]* } (sc)
        self.sc: Dict[AbstractBasicBlock, Set[AbstractBasicBlock]] = defaultdict(set)

        # v -> { u | u ∈ N, v ∈ V, u ∈ ⊕ (n, v) ~ d, path(n, u) ~ d[Dd]* } (sd)
        self.sd: Dict[PseudoVariable, Set[AbstractBasicBlock]] = defaultdict(set)

        # s -> { u | u ∈ N, s ∈ S, u ∈ ⊕ (n, s) ~ D, path(n, u) ~ D[Dd]* } (sD)
        self.sD: Dict[StateVariable, Set[AbstractBasicBlock]] = defaultdict(set)

        # w -> { u | w, u ∈ N, u ∈ ⊕ (n, w) ~ [cC], path(n, u) ~ [cC]+D[Dd]*} (sC)
        self.sC: Dict[AbstractBasicBlock, Set[AbstractBasicBlock]] = defaultdict(set)

        self._init_summary()

    def _init_summary(self):
        if isinstance(self.block, NodeBlock):
            if self.block.is_transfer:
                self.sc[self.block].add(self.block)
                sink_summaries = [
                    summary
                    for summary in itertools.chain.from_iterable(
                        op.context[DATA_FLOW_SINK_KEY] for op in self.block.node.irs_ssa
                    )
                    if isinstance(summary, ProfitSinkSummary)
                ]
                for summary in sink_summaries:
                    self.sd[WrappedSlithIRVariable(summary.var)].add(self.block)

    def set_as_control_dependency(self, transfer_blocks: set[NodeBlock]):
        if len(transfer_blocks) == 0 or not isinstance(self.block, NodeBlock):
            return

        for transfer_block in transfer_blocks:
            self.sc[self.block].add(transfer_block)

        sink_summaries = [
            summary
            for summary in itertools.chain.from_iterable(
                op.context[DATA_FLOW_SINK_KEY] for op in self.block.node.irs_ssa
            )
            if isinstance(summary, ConditionSinkSummary)
        ]
        for summary in sink_summaries:
            for transfer_block in transfer_blocks:
                self.sd[WrappedSlithIRVariable(summary.var)].add(transfer_block)

    def __str__(self):
        return f"NodeSummary: {self.block}"

    @property
    def saf(self) -> Set[AbstractBasicBlock]:
        """
        Set of transfer nodes that are reachable from the current node via control flow
        -- saf = sc U sC
        :return:
        """
        sc = functools.reduce(set_merge, self.sc.values(), set())
        return sc

    @property
    def sa(self) -> Set[AbstractBasicBlock]:
        """
        Set of transfer nodes that can be influenced via inter-transaction data flow
        -- sa = sD U sC
        :return:
        """
        sD = functools.reduce(set_merge, self.sD.values(), set())
        sC = functools.reduce(set_merge, self.sC.values(), set())
        return sD | sC

    # noinspection DuplicatedCode
    def transfer_c(self, w_sum: NodeSummary) -> bool:
        """
        -- Transfer on a control flow edge: (n, w) ~ c
        -- sc_n U= sc_w
        -- sC_n U= sC_w U sD_w
        :param w_sum:
        :return: whether the current node summary is changed
        """
        # We will merge the control flow summaries from any successor node.
        w = w_sum.block
        sc = functools.reduce(set_merge, w_sum.sc.values(), copy(self.sc[w]))
        sC = functools.reduce(
            set_merge,
            itertools.chain(w_sum.sC.values(), w_sum.sD.values()),
            copy(self.sC[w]),
        )
        changed = len(sc) != len(self.sc[w]) or len(sC) != len(self.sC[w])
        if changed:
            self.sc[w] = sc
            self.sC[w] = sC
        return changed

    # noinspection PyPep8Naming,DuplicatedCode
    def transfer_C(self, w_sum: NodeSummary) -> bool:
        """
        -- Transfer on a function call graph edge: (n, w) ~ C
        -- sc_n U= sc_w
        -- sC_n U= sC_w U sD_w
        :param w_sum:
        :return: whether the current node summary is changed
        """
        # We will merge the control flow summaries from any successor node.
        w = w_sum.block
        sc = functools.reduce(set_merge, w_sum.sc.values(), copy(self.sc[w]))
        sC = functools.reduce(
            set_merge,
            itertools.chain(w_sum.sC.values(), w_sum.sD.values()),
            copy(self.sC[w]),
        )
        changed = len(sc) != len(self.sc[w]) or len(sC) != len(self.sC[w])
        if changed:
            self.sc[w] = sc
            self.sC[w] = sC
        return changed

    def transfer_d(self, w_sum: NodeSummary, flow: IntraTransactionDataFlow) -> bool:
        """
        -- Transfer on a data flow edge: (n, w) ~ d
        -- sd_n U= sd_w U sD_w
        :param w_sum: the summary of the w node
        :param flow: the intra-transaction data flow edge (n, w) to transfer
        :return: whether the current node summary is changed
        """
        # We will distinguish flows to different variable.
        sd = copy(self.sd[flow.source])
        sd |= w_sum.sd[flow.sink]
        if isinstance(flow.sink, StateVariable):
            sd |= w_sum.sD[flow.sink]

        changed = len(sd) != len(self.sd[flow.source])
        if changed:
            self.sd[flow.source] = sd
        return changed

    # noinspection PyPep8Naming
    def transfer_D(self, w_sum: NodeSummary, flow: InterTransactionDataFlow) -> bool:
        """
        -- Transfer on a data flow edge: (n, w) ~ D
        -- sD_n U= sD_w U sd_w
        :param w_sum: the summary of the w node
        :param flow: the inter-transaction data flow edge (n, w) to transfer
        :return: whether the current node summary is changed
        """
        # We will merge the state variable summaries from any successor node.
        sD = copy(self.sD[flow.source])
        sD |= w_sum.sD[flow.sink] | w_sum.sd[flow.sink]
        if isinstance(w_sum.block, StorageSlot):
            for s in itertools.chain(w_sum.sd.values(), w_sum.sD.values()):
                sD |= s

        changed = len(sD) != len(self.sD[flow.source])
        if changed:
            self.sD[flow.source] = sD
        return changed


NODE_SUMMARY_KEY = "node_summary"


def summarize_influence_set(
    hfg: HybridFlowGraph,
):
    graph = hfg.graph
    control_deps = hfg.transfer_control_dependencies
    for node in graph.nodes:
        summary = NodeSummary(node)
        node.context[NODE_SUMMARY_KEY] = summary
        if not isinstance(node, NodeBlock):
            continue
        if node.node.type not in [
            NodeType.IF,
            NodeType.IFLOOP,
        ] and "require(" not in str(node.node):
            # only require or if statements are control dependency
            continue
        if node in control_deps:
            transfers = control_deps[node]
            summary.set_as_control_dependency(transfers)

    def transfer_fn(
        dependencies: Iterable[AbstractBasicBlock], current: AbstractBasicBlock
    ) -> bool:
        changed = False
        deps = {dep: dep.context[NODE_SUMMARY_KEY] for dep in dependencies}
        curr = current.context[NODE_SUMMARY_KEY]
        for predecessor, dep in deps.items():
            edge = graph.edges[current, predecessor]["flows"]
            for flow in edge:
                if isinstance(flow, IntraProceduralControlFlow):
                    changed |= curr.transfer_c(dep)
                elif isinstance(flow, InterProceduralCallFlow):
                    changed |= curr.transfer_C(dep)
                elif isinstance(flow, IntraTransactionDataFlow):
                    changed |= curr.transfer_d(dep, flow)
                elif isinstance(flow, InterTransactionDataFlow):
                    changed |= curr.transfer_D(dep, flow)
        return changed

    abstractly_interpret(graph.reverse(copy=False), transfer_fn)


def collect_candidate_pairs(
    hfg: HybridFlowGraph,
) -> List[Tuple[FunctionContract, FunctionContract]]:
    """
    Collect candidate pairs of public functions that may be vulnerable to front-running attacks.
    :param hfg:
    :return:
    """
    summarize_influence_set(hfg)

    # find candidate pairs
    # candidates are all public functions
    candidates: List[NodeSummary] = [
        b.context[NODE_SUMMARY_KEY] for b in hfg.public_entries
    ]
    pairs = []
    for i in range(len(candidates)):
        for j in range(i, len(candidates)):
            n1 = candidates[i]
            n2 = candidates[j]
            if len(n1.sa & n2.saf) > 0 and len(n1.saf & n2.sa) > 0:
                assert isinstance(n1.block, NodeBlock)
                assert isinstance(n2.block, NodeBlock)
                fn1 = n1.block.node.function
                fn2 = n2.block.node.function
                if isinstance(fn1, FunctionContract) and isinstance(
                    fn2, FunctionContract
                ):
                    pairs.append((fn1, fn2))

    return pairs
