from __future__ import annotations
from typing import List, Generator

from slither.core.declarations import FunctionContract

from hfg.hybrid_flow_graph import HybridFlowGraph
from supernova.galaxy.ContractRepo import ContractRepoRaw
from supernova.hfg.msg_call_graph import MsgCallGraph


class ContractGroup(object):
    def __init__(self, contract_repos: List[ContractRepoRaw]):
        self._hfg = None
        self._mcg = None
        self.contract_repos: List[ContractRepoRaw] = contract_repos

    @property
    def functions(self) -> Generator[FunctionContract, None, None]:
        for repo in self.contract_repos:
            for fn in repo.main_contract.functions:
                yield fn

    @property
    def msg_call_graph(self) -> MsgCallGraph:
        """
        Get the message call graph (MCG) between public functions.
        The nodes in MCG are all public functions in the contract group.
        The graph nodes are labelled with the Slither function object.
        The edges in MCG are labelled with the HIGH_LEVEL_CALL expression
         node in SlithIR.
        :return:
        """
        if self._mcg is None:
            self._mcg = MsgCallGraph.from_contract_group(self)
        return self._mcg

    @property
    def hybrid_flow_graph(self) -> HybridFlowGraph:
        """
        Get the hybrid flow graph (HFG) of the contract group.
        :return:
        """
        if self._hfg is None:
            self._hfg = HybridFlowGraph.from_contract_group(self)
        return self._hfg
