import z3
from slither.core.declarations import Contract, SolidityVariableComposed
from slither.core.solidity_types import ElementaryType
from slither.core.variables.variable import Variable

from engine2.transfer import ResolvedTransfer
from engine2.variable import ContractVar, AccountVar, TokenContractVar, Var


class State:
    """
    State represents blockchain state, including:
    1. account data,
    2. contract storage
    """

    def __init__(self, contracts: set[Contract]):
        self.all_contracts = contracts
        # contract => contract variable,
        # (use Contract instead of name since there could be contract with the same name in different repos)
        self.contracts: dict[Contract, ContractVar] = dict()
        # str(address symbolic value) => account variable
        self.accounts: dict[z3.ExprRef, AccountVar] = dict()
        for c in contracts:
            cvar = ContractVar(c)
            self.contracts[c] = cvar
            self.accounts[cvar.val] = cvar

        # initialize constant state variables in contracts
        for contract in self.contracts.keys():
            for var in contract.state_variables:
                if (
                    var.is_constant
                    or var.is_immutable
                    and var.node_initialization is not None
                ):
                    # initialize constant state variables
                    init_node = var.node_initialization
                    from engine2.summary_builder import FunctionSummaryBuilder

                    builder = FunctionSummaryBuilder(
                        init_node.function, {contract}, {}, state=self
                    )
                    builder.build()

        # token contract modeling
        # str(token contract address symbolic value)  => token contract variable
        self.token_contracts: dict[z3.ExprRef, TokenContractVar] = dict()

        self.timestamp = Var(SolidityVariableComposed("block.timestamp"), free=True)
        self.block_number = Var(SolidityVariableComposed("block.number"), free=True)

    @property
    def constraints(self) -> list[z3.BoolRef]:
        constraints = []
        for c_var in self.contracts.values():
            for var in c_var.storage.values():
                constraints.extend(var.constraints)
        return constraints

    def copy(self) -> "State":
        st = State(self.all_contracts)
        for c_var, st_c_var in zip(self.contracts.values(), st.contracts.values()):
            for key, var in c_var.storage.items():
                st_c_var.storage[key] = var.copy()
        for acc, st_acc in zip(self.accounts.values(), st.accounts.values()):
            st_acc.balance = acc.balance.copy()
            st_acc.code = acc.code.copy()
            st_acc.codehash = acc.codehash.copy()
        for addr, token_c_var in self.token_contracts.items():
            st.token_contracts[addr] = token_c_var.copy()
        st.timestamp = self.timestamp.copy()
        st.block_number = self.block_number.copy()
        return st

    def substitute_strategy(self, st: "State") -> list[tuple[z3.ExprRef, z3.ExprRef]]:
        """
        Return a list of (old, new) pairs to be used in z3 substitute.
        """
        strategy = []
        for c_var, st_c_var in zip(self.contracts.values(), st.contracts.values()):
            for key, var in c_var.storage.items():
                strategy.append((var.symbol, st_c_var.load(key).val))
        for acc, st_acc in zip(self.accounts.values(), st.accounts.values()):
            strategy.append((acc.balance.symbol, st.balance_of(st_acc.val)))
            strategy.append((acc.code.symbol, st.code_of(st_acc.val)))
            strategy.append((acc.codehash.symbol, st.codehash_of(st_acc.val)))
        return strategy

    def _account_of(self, address: z3.ExprRef) -> AccountVar:
        for c_var in self.accounts.values():
            if c_var.val.eq(address):
                return c_var
        var = Variable()
        var.name = f"address({address})"
        var.type = ElementaryType("address")
        acc = AccountVar(var)
        # self.accounts[str(address)] = acc
        return acc

    def balance_of(self, address: z3.ExprRef) -> z3.ExprRef:
        acc = self._account_of(address)
        return acc.balance.val

    def add_balance(self, address: z3.ExprRef, amount: z3.ExprRef) -> None:
        acc = self._account_of(address)
        acc.balance.val = acc.balance.val + amount

    def code_of(self, address: z3.ExprRef) -> z3.ExprRef:
        acc = self._account_of(address)
        return acc.code.val

    def codehash_of(self, address: z3.ExprRef) -> z3.ExprRef:
        acc = self._account_of(address)
        return acc.codehash.val

    def get_storage(self, contract: Contract, key: str) -> z3.ExprRef | None:
        c_var = self.contracts[contract]
        var = c_var.load(key)
        if var is None:
            return None
        return var.val

    def set_storage(
        self,
        contract: Contract,
        key: str,
        val: z3.ExprRef,
        path_condition: z3.BoolRef = None,
    ) -> None:
        c_var = self.contracts[contract]
        c_var.load(key).assign(val, path_condition)

    def load_contract(self, contract: Contract) -> ContractVar:
        return self.contracts[contract]

    def apply_storage_writes(
        self,
        writes: dict[tuple[Contract, str], z3.ExprRef],
        path_condition: z3.BoolRef = None,
    ):
        for (contract, key), val in writes.items():
            self.set_storage(contract, key, val, path_condition)

    def token_transfer(self, address: z3.ExprRef, transfer: ResolvedTransfer) -> None:
        if address not in self.token_contracts:
            self.token_contracts[address] = TokenContractVar(
                address, str(hash(address))
            )
        self.token_contracts[address].transfer(transfer)

    def token_balance_of(
        self, address: z3.ExprRef, account: z3.ExprRef, token: z3.ExprRef | None = None
    ) -> z3.ExprRef:
        if address not in self.token_contracts:
            self.token_contracts[address] = TokenContractVar(
                address, str(hash(address))
            )
        return self.token_contracts[address].balance_of(account, token)

    def token_owner_of(self, address: z3.ExprRef, token_id: z3.ExprRef) -> z3.ExprRef:
        if address not in self.token_contracts:
            self.token_contracts[address] = TokenContractVar(
                address, str(hash(address))
            )
        return self.token_contracts[address].owner_of(token_id)

    def owner(self, address: z3.ExprRef) -> z3.ExprRef:
        if address not in self.token_contracts:
            self.token_contracts[address] = TokenContractVar(
                address, str(hash(address))
            )
        return self.token_contracts[address].owner()
