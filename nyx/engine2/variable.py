import z3
from slither.core.declarations import SolidityVariable, Structure, Contract
from slither.core.solidity_types import UserDefinedType, ElementaryType, Type
from slither.core.solidity_types.elementary_type import Uint, Int
from slither.core.variables.variable import Variable
from slither.slithir.variables import (
    TupleVariable,
    ReferenceVariable,
)

from engine2.transfer import ResolvedTransfer
from engine2.value import (
    type_to_sort,
    zero_value,
    structure_accessor,
    structure_accessors,
    unique_name,
    sort_conversion,
)


class AbsVar:
    @property
    def constraints(self) -> list[z3.BoolRef]:
        var_type = self.var.type
        if isinstance(var_type, ElementaryType) and var_type.type in Uint:
            val = self.val
            if isinstance(val, z3.ArithRef):
                return [val >= 0]
            elif isinstance(val, z3.BitVecRef):
                return [z3.UGE(val, 0)]
        return []

    @property
    def signed(self):
        var_type = self.var.type
        if isinstance(var_type, ElementaryType) and var_type.type in Int:
            return True
        return False

    @property
    def var(self) -> Variable | SolidityVariable:
        raise NotImplementedError()

    @property
    def type(self) -> Type:
        return self.var.type

    @property
    def val(self) -> z3.ExprRef:
        raise NotImplementedError()

    @property
    def simplified_val(self) -> z3.ExprRef:
        val = z3.simplify(self.val)
        return val

    @val.setter
    def val(self, val: z3.ExprRef) -> None:
        raise NotImplementedError()

    def free(self) -> None:
        """Discard current val, set to free variable"""
        raise NotImplementedError()

    def assign(self, val: z3.ExprRef, cond: z3.BoolRef = None) -> None:
        val = sort_conversion(self.val.sort(), val, self.signed)
        if cond is None:
            self.val = val
        else:
            self.val = z3.If(cond, val, self.val)

    def copy(self) -> "AbsVar":
        raise NotImplementedError()

    def __str__(self):
        return f"{self.var.name} = {self.val}"


class Var(AbsVar):
    """
    Local variables have scope within a function.
    Assigning local variables will not have side effects.
    """

    def __init__(self, var: Variable | SolidityVariable, free: bool = True):
        self._var = var
        var_type = var.type
        if isinstance(var_type, list):
            # FIXME: KittyCore:this.balance
            var_type = var.type[0]
        sort = type_to_sort(var_type)
        self._symbol = z3.Const(unique_name(var.name), sort)
        self._val = self._symbol if free else zero_value(sort)

    @property
    def symbol(self) -> z3.ExprRef:
        return self._symbol

    def free(self) -> None:
        self.val = self.symbol

    @property
    def var(self) -> Variable | SolidityVariable:
        return self._var

    @property
    def val(self) -> z3.ExprRef:
        return self._val

    @property
    def sort(self) -> z3.SortRef:
        return self._val.sort()

    @val.setter
    def val(self, val: z3.ExprRef) -> None:
        self._val = val

    def copy(self) -> "Var":
        var = Var(self._var, free=False)
        var._symbol = self._symbol
        var._val = self._val
        return var


class TupleVar(AbsVar):
    def __init__(self, var: TupleVariable):
        self._var = var
        sorts = [type_to_sort(t) for t in var.type]
        self._vals: tuple[z3.ExprRef, ...] = tuple(
            z3.Const(unique_name(), s) for s in sorts
        )

    @property
    def constraints(self) -> list[z3.BoolRef]:
        cs = []
        for i, var_type in enumerate(self.var.type):
            if isinstance(var_type, ElementaryType) and var_type.type in Uint:
                val = self.val[i]
                assert isinstance(val, (z3.ArithRef, z3.BitVecRef))
                cs.append(val >= 0)
        return cs

    @property
    def var(self) -> TupleVariable:
        return self._var

    def free(self) -> None:
        sorts = [type_to_sort(t) for t in self.var.type]
        self._vals: tuple[z3.ExprRef, ...] = tuple(
            z3.Const(unique_name(), s) for s in sorts
        )

    @property
    def val(self) -> tuple[z3.ExprRef, ...]:
        return self._vals

    @val.setter
    def val(self, val: tuple[z3.ExprRef, ...]) -> None:
        self._vals = val

    def assign(self, vals: tuple[z3.ExprRef], cond: z3.BoolRef = None) -> None:
        assert len(vals) == len(self._vals)
        if cond is None:
            self._vals = vals
        else:
            self._vals = tuple(
                z3.If(cond, v, self._vals[i]) for i, v in enumerate(vals)
            )

    def copy(self) -> "TupleVar":
        var = TupleVar(self._var)
        var._vals = self._vals
        return var


class RefVar(AbsVar):
    """
    Reference variable is a pointer to a some other variable.
    Assigning reference variable will have side effects, i.e., updating the variable it points to.
    The value of a reference variable should be computed dynamically.
    """

    def __init__(self, var: Variable, base: AbsVar, key: AbsVar | str = None):
        self._var = var
        self.base = base
        self.key = key
        self.symbol = None

        var_type = self.base.var.type
        if (
            key is not None
            and isinstance(var_type, UserDefinedType)
            and isinstance(var_type.type, Structure)
        ):
            self.structure = var_type.type
            self.accessor = structure_accessor(self.structure, key)
            self.accessors = structure_accessors(self.structure)

    @property
    def var(self) -> Variable | SolidityVariable:
        return self._var

    def free(self) -> None:
        sort = type_to_sort(self.var.type)
        self.val = z3.Const(unique_name(), sort)

    @property
    def val(self) -> z3.ExprRef:
        if self.key is None:
            return self.base.val

        base_val = self.base.val
        if isinstance(base_val, z3.ArrayRef):
            assert isinstance(self.key, AbsVar)
            key = sort_conversion(base_val.sort().domain(), self.key.val, False)
            return z3.Select(base_val, key)
        elif isinstance(base_val, z3.DatatypeRef):
            assert self.accessor is not None
            return self.accessor(base_val)
        elif isinstance(base_val, z3.BitVecRef):
            assert isinstance(self.key, AbsVar)
            self.symbol = z3.BitVec(unique_name(self.var.name), 8)
            return self.symbol
        else:
            raise NotImplementedError(base_val.sort())

    @val.setter
    def val(self, val: z3.ExprRef) -> None:
        if self.key is None:
            self.base.val = val
            return

        base_val = self.base.val
        if isinstance(base_val, z3.ArrayRef):
            assert isinstance(self.key, AbsVar)
            key = sort_conversion(base_val.sort().domain(), self.key.val, False)
            self.base.val = z3.Update(base_val, key, val)
        elif isinstance(base_val, z3.DatatypeRef):
            assert isinstance(self.key, str)
            self.base.val = self._update_datatype(base_val, self.key, val)
        else:
            raise NotImplementedError(base_val.sort())

    def _update_datatype(
        self, val: z3.DatatypeRef, key: str, field: z3.ExprRef
    ) -> z3.DatatypeRef:
        fields = []
        for k, accessor in self.accessors.items():
            if k == key:
                fields.append(field)
            else:
                fields.append(accessor(val))
        return val.sort().constructor(0)(*fields)

    def copy(self) -> "RefVar":
        var = RefVar(self._var, self.base, self.key)
        var.structure = self.structure
        var.accessor = self.accessor
        var.accessors = self.accessors
        return var


class TypeRefVar(AbsVar):
    def __init__(self, var: ReferenceVariable, typ: Type):
        self._var = var
        self.typ = typ

    @property
    def var(self) -> Variable | SolidityVariable:
        return self._var

    @property
    def val(self) -> Type:
        return self.typ

    @val.setter
    def val(self, val: Type) -> None:
        self.typ = val

    @property
    def type(self) -> Type:
        return self.typ

    @property
    def simplified_val(self) -> Type:
        return self.typ

    def free(self) -> None:
        pass

    def assign(self, val: Type, cond: z3.BoolRef = None) -> None:
        self.val = val

    def copy(self) -> "TypeRefVar":
        var = TypeRefVar(self._var, self.typ)
        return var


class AccountVar(AbsVar):
    """
    Special LocalVar that represents an account
    Its value is the address of the account.
    """

    def __init__(self, var: Variable | SolidityVariable):
        self._var = var
        sort = type_to_sort(var.type)
        self._val = z3.Const(unique_name(var.name), sort)

        balance_var = Variable()
        balance_var.name = f"{var.name}_balance"
        balance_var.type = ElementaryType("uint")
        self.balance = Var(balance_var, free=True)

        code_var = Variable()
        code_var.name = f"{var.name}_code"
        code_var.type = ElementaryType("bytes")
        self.code = Var(code_var, free=True)

        codehash_var = Variable()
        codehash_var.name = f"{var.name}_codehash"
        codehash_var.type = ElementaryType("bytes32")
        self.codehash = Var(codehash_var, free=True)

    @property
    def var(self) -> Variable | SolidityVariable:
        return self._var

    def free(self) -> None:
        pass

    @property
    def val(self) -> z3.ExprRef:
        return self._val

    @val.setter
    def val(self, val: z3.ExprRef) -> None:
        self._val = val

    def copy(self) -> "AccountVar":
        var = AccountVar(self._var)
        var._val = self._val
        var.balance = self.balance.copy()
        var.code = self.code.copy()
        var.codehash = self.codehash.copy()
        return var


class ContractVar(AccountVar):
    """
    Special LocalVar that represents the contract itself.
    Its value is the contract address.
    """

    def __init__(self, contract: Contract):
        var = Variable()
        var.name = contract.name
        var.type = UserDefinedType(contract)
        super().__init__(var)
        self.contract = contract
        self.storage: dict[str, Var] = dict()
        for var in contract.state_variables:
            self.storage[var.name] = Var(var, free=True)

    def load(self, key: str) -> Var | None:
        if key not in self.storage:
            return None
        return self.storage[key]

    def store(self, key: str, val: "Var") -> None:
        self.storage[key] = val

    def copy(self) -> "AccountVar":
        var = ContractVar(self.contract)
        var._var = self._var
        var._val = self._val
        var.balance = self.balance.copy()
        var.code = self.code.copy()
        var.codehash = self.codehash.copy()
        var.storage = {k: v.copy() for k, v in self.storage.items()}
        return var


class TokenContractVar(AccountVar):
    def __init__(self, address: z3.ExprRef, unique_key: str):
        self.unique_key = unique_key
        var = Variable()
        var.name = unique_key + "token_contract"
        var.type = ElementaryType("address")
        super().__init__(var)
        self.val = address
        """token contract modeling"""
        # mapping(address => uint) // owner => balance
        self.fungible_tokens: z3.ArrayRef = z3.Array(
            unique_key + "fungible_tokens",
            type_to_sort("address"),
            type_to_sort("uint"),
        )
        # mapping(uint => address) // token_id => owner
        self.nonfungible_tokens: z3.ArrayRef = z3.Array(
            unique_key + "nonfungible_tokens",
            type_to_sort("uint"),
            type_to_sort("address"),
        )
        # mapping(uint => address => uint) // token_id => owner => balance
        self.fungible_tokens_erc1155: z3.ArrayRef = z3.Array(
            unique_key + "nonfungible_tokens_balance",
            type_to_sort("uint"),
            z3.ArraySort(type_to_sort("address"), type_to_sort("uint")),
        )
        # owner
        self._owner = z3.Const(unique_key + "owner", type_to_sort("address"))

    """ ownerable """

    def owner(self) -> z3.ExprRef:
        return self._owner

    """ token contract modeling """

    def balance_of(
        self, account: z3.ExprRef, token_id: z3.ExprRef | None = None
    ) -> z3.ExprRef:
        if token_id is None:
            return self.fungible_tokens[account]
        else:
            return self.fungible_tokens_erc1155[token_id][account]

    def owner_of(self, token_id: z3.ExprRef) -> z3.ExprRef:
        return self.nonfungible_tokens[token_id]

    def transfer(
        self,
        transfer: ResolvedTransfer,
    ) -> None:
        if transfer.typ in ["ERC20", "ERC777"]:
            self.fungible_tokens = z3.Update(
                self.fungible_tokens,
                transfer.sender,
                self.fungible_tokens[transfer.sender] - transfer.amount,
            )
            self.fungible_tokens = z3.Update(
                self.fungible_tokens,
                transfer.receiver,
                self.fungible_tokens[transfer.receiver] + transfer.amount,
            )
        elif transfer.typ == "ERC721":
            self.nonfungible_tokens = z3.Update(
                self.nonfungible_tokens,
                transfer.token_id,
                transfer.receiver,
            )
        elif transfer.typ == "ERC1155":
            token_balances = self.fungible_tokens_erc1155[transfer.token_id]
            balance_fr = token_balances[transfer.sender]
            balance_to = token_balances[transfer.receiver]
            token_balances = z3.Update(
                token_balances,
                transfer.sender,
                balance_fr - transfer.amount,
            )
            token_balances = z3.Update(
                token_balances,
                transfer.receiver,
                balance_to + transfer.amount,
            )
            self.fungible_tokens_erc1155 = z3.Update(
                self.fungible_tokens_erc1155,
                transfer.token_id,
                token_balances,
            )

    def copy(self) -> "TokenContractVar":
        var = TokenContractVar(self.val, self.unique_key)
        var._var = self._var
        var._val = self._val
        var.balance = self.balance.copy()
        var.code = self.code.copy()
        var.codehash = self.codehash.copy()
        var.fungible_tokens = self.fungible_tokens
        var.nonfungible_tokens = self.nonfungible_tokens
        var.fungible_tokens_erc1155 = self.fungible_tokens_erc1155
        var._owner = self._owner
        return var
