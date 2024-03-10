from slither.core.declarations import Contract

from analyze.observe import Observer
from galaxy.ContractRepo import ContractRepo


class AnalyzeGroup:
    def __init__(self, name: str, *contract_repos: ContractRepo):
        self.name = name
        self.result_file = "result.json"
        self.profiling_file = "profiling.json"
        self.contract_repos: set[ContractRepo] = set(contract_repos)
        self._analyze: set[Contract] | None = None
        self._select_cache: list[Contract | str] = []

    @property
    def all_contracts(self) -> set[Contract]:
        cs = set()
        for repo in self.contract_repos:
            for c in repo.slither.contracts:
                cs.add(c)
        return cs

    @property
    def analyze_contracts(self) -> set[Contract]:
        self._select(*self._select_cache)
        if self._analyze is None:
            return self.all_contracts
        else:
            return self._analyze

    def focus(self, *contracts: Contract | str):
        self._select_cache.extend(contracts)

    def _select(self, *contracts: Contract | str):
        for c in contracts:
            self._select_one(c)

    def _select_one(self, contract: Contract | str):
        def add(*_cs: Contract):
            if self._analyze is None:
                self._analyze = set()
            for _c in _cs:
                self._analyze.add(_c)

        if isinstance(contract, str):
            for repo in self.contract_repos:
                cs = repo.slither.get_contract_from_name(contract)
                add(*cs)
        elif isinstance(contract, Contract):
            add(contract)
        else:
            raise TypeError(f"Unsupported type: {type(contract)}")
