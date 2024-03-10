import z3
from eth_typing import HexStr
from slither.core.declarations import SolidityVariable, Contract, Enum
from slither.core.solidity_types import ArrayType, ElementaryType, UserDefinedType
from slither.core.variables.local_variable import LocalVariable
from slither.core.variables.state_variable import StateVariable
from slither.core.variables.top_level_variable import TopLevelVariable
from slither.core.variables.variable import Variable
from slither.slithir.operations import (
    Member,
    Index,
    Length,
    SolidityCall,
    Assignment,
    HighLevelCall,
)
from slither.slithir.variables import (
    ReferenceVariable,
    Constant,
    TemporaryVariable,
    TupleVariable,
)
from web3 import Web3

from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.transfer import ResolvedTransfer
from engine2.value import unique_name, sort_value, type_to_sort, is_signed_type
from engine2.variable import AbsVar, Var, RefVar, TupleVar, TypeRefVar


class Env:
    """
    Env is the execution environment of one call to internal/external function
    """

    def __init__(self, state: State, call: MsgCall):
        self.state = state
        self.call = call

        self.variables: dict[Variable | SolidityVariable, AbsVar] = dict()

    def copy(self, msg_call: MsgCall = None) -> "Env":
        env = Env(self.state.copy(), msg_call or self.call)
        env.variables = {k: v.copy() for k, v in self.variables.items()}
        return env

    @property
    def constraints(self) -> list[z3.BoolRef]:
        cs = []
        for v in self.variables.values():
            cs.extend(v.constraints)
        return cs

    def use_solidity_variable(self, var: SolidityVariable) -> AbsVar:
        if var in self.variables:
            return self.variables[var]

        v = Var(var)
        if var.name == "msg.sender":
            v.val = self.call.sender.val
        elif var.name == "msg.value":
            v.val = self.call.value.val
        elif var.name == "this":
            v.val = self.call.this.val
        elif var.name == "tx.origin":
            v.val = self.call.origin.val
        elif var.name == "block.timestamp":
            v.val = self.state.timestamp.val
        elif var.name == "now":
            v.val = self.state.timestamp.val
        elif var.name == "block.number":
            v.val = self.state.block_number.val

        self.variables[var] = v
        return v

    def use_state_variable(self, var: StateVariable) -> AbsVar:
        if var in self.variables:
            return self.variables[var]

        c = self.state.load_contract(var.contract)
        v = c.load(var.name)

        self.variables[var] = v
        return v

    def use_constant_variable(self, var: Constant) -> AbsVar:
        if not isinstance(var, Constant):
            if var in self.variables:
                return self.variables[var]

        v = Var(var)
        value = var.value
        v_sort = v.sort
        if isinstance(v_sort, z3.BitVecSortRef):
            if isinstance(value, str):
                value = Web3.toInt(hexstr=HexStr(value))
            elif isinstance(value, bool):
                value = int(value)
            elif isinstance(value, int):
                value = value
            else:
                raise NotImplementedError(value)
            max_val = (
                2 ** (v_sort.size() - 1) - 1
                if is_signed_type(v.type)
                else 2 ** v_sort.size() - 1
            )
            if value > max_val:
                # since we have shrinked the bitsize of integers,
                # we need to check if the constant value is out of range
                # in such cases, we approximate using a free symbolic value
                v.val = z3.Const(unique_name("approx"), v_sort)
            else:
                v.val = sort_value(value, v_sort)
        elif isinstance(v_sort, z3.BoolSortRef):
            assert isinstance(value, bool)
            v.val = sort_value(value, v_sort)
        elif isinstance(v_sort, z3.ArithSortRef):
            if isinstance(value, str):
                value = Web3.toInt(hexstr=HexStr(value))
            elif isinstance(value, bool):
                value = int(value)
            elif isinstance(value, int):
                value = value
            else:
                raise NotImplementedError(value)
            v.val = sort_value(value, v_sort)
        elif isinstance(v_sort, z3.SeqSortRef):
            assert isinstance(value, str)
            v.val = sort_value(value, v_sort)
        else:
            raise NotImplementedError(v_sort)

        self.variables[var] = v
        return v

    def use_reference_variable(
        self,
        var: ReferenceVariable,
        op: Member | Index | Length | SolidityCall,
    ) -> AbsVar:
        if var in self.variables:
            return self.variables[var]

        if isinstance(op, Member):
            if isinstance(op.variable_left, Contract):
                # accessing the field of a contract directly using contract declaration
                assert isinstance(op.variable_right, Constant)
                field = op.variable_right.value
                assert isinstance(field, str)
                c = self.state.load_contract(op.variable_left)
                v = c.load(field)
                if v is None:
                    # workaround for issue Crytic/slither#566
                    # the field being accessed is not a state variable
                    # it could be an enum declaration or struct declaration
                    key = f"{c.contract.name}.{field}"
                    if key in c.contract.enums_as_dict:
                        val = c.contract.enums_as_dict[key]
                    elif key in c.contract.structures_as_dict:
                        val = c.contract.structures_as_dict[key]
                    else:
                        raise ValueError(f"Unknown field {key}")
                    typ = UserDefinedType(val)
                    v = TypeRefVar(var, typ)
            elif isinstance(op.variable_left, Enum):
                # accessing the field of an enum directly using enum declaration
                assert isinstance(op.variable_right, Constant)
                field = op.variable_right.value
                assert isinstance(field, str)
                val = op.variable_left.values.index(field)
                v = Var(var)
                v.val = sort_value(val, v.sort)
            else:
                key = op.variable_right.value
                assert isinstance(key, str)
                base = self.use(op.variable_left)
                if isinstance(base, TypeRefVar):
                    # accessing the field of a user defined type (typically enum elements)
                    # construct the enum value
                    base_type = base.type
                    assert isinstance(base_type, UserDefinedType)
                    base_type_type = base_type.type
                    assert isinstance(base_type_type, Enum)
                    val = base_type_type.values.index(key)
                    val_var = Variable()
                    val_var.name = var.name
                    val_var.type = base_type
                    v = Var(val_var)
                    v.val = sort_value(val, v.sort)
                else:
                    v = RefVar(var, base, key)
        elif isinstance(op, Index):
            key_var = self.use(op.variable_right)
            key = key_var.val
            assert isinstance(key, z3.ExprRef)
            base = self.use(op.variable_left)
            v = RefVar(var, base, key_var)
        elif isinstance(op, Length):
            typ = op.value.type
            if isinstance(typ, (ArrayType)):
                v = Var(var)
                if not typ.is_dynamic:
                    v.val = self.use_constant_variable(
                        Constant(
                            str(typ.length_value.value),
                            constant_type=ElementaryType("uint256"),
                        )
                    ).val
                else:
                    sort = type_to_sort("uint")
                    v.val = z3.Const(f"{var.name}_length", sort)
            elif isinstance(typ, ElementaryType):
                assert typ.is_dynamic
                v = Var(var)
                sort = type_to_sort("uint")
                v.val = z3.Const(f"{var.name}_length", sort)
            else:
                raise NotImplementedError(typ)
        elif isinstance(op, SolidityCall) and op.function.name in [
            "type()",
            "type(address)",
        ]:
            v = Var(var, free=True)
        elif isinstance(op, Assignment):
            # special case, when assigning a function selector to a variable
            v = Var(var, free=True)
        else:
            raise NotImplementedError(op.node.source_mapping)

        self.variables[var] = v
        return v

    def use(
        self,
        var: Variable | SolidityVariable | Contract,
        op: Member | Index | Length | SolidityCall | Assignment = None,
    ) -> AbsVar:
        if not isinstance(var, Constant):
            if var in self.variables:
                return self.variables[var]

        if isinstance(var, SolidityVariable):
            return self.use_solidity_variable(var)
        elif isinstance(var, Constant):
            return self.use_constant_variable(var)
        elif isinstance(var, StateVariable):
            return self.use_state_variable(var)
        elif isinstance(var, ReferenceVariable):
            if op is None:
                v = Var(var, free=True)
            else:
                return self.use_reference_variable(var, op)
        elif isinstance(var, LocalVariable):
            if var.is_storage and op is not None:
                # FIXME: function parameter, calldata variable will be falsely set is_storage to True
                # Since when dealing with function parameter variable, op is None,
                # We add (op is not None) as a temporary fix
                rv = self.use(op.rvalue)
                if isinstance(rv, RefVar):
                    # reference to a storage variable
                    v = RefVar(var, rv.base, rv.key)
                else:
                    # directly equal to a storage variable
                    v = RefVar(var, rv, None)
            else:
                v = Var(var)
        elif isinstance(var, TemporaryVariable):
            v = Var(var)
        elif isinstance(var, TupleVariable):
            v = TupleVar(var)
        elif isinstance(var, Contract):
            v = self.state.load_contract(var)
        elif isinstance(var, TopLevelVariable):
            v = Var(var)
        else:
            print(type(var))
            raise NotImplementedError(var)

        self.variables[var] = v
        return v

    def delete(self, var: Variable):
        if var in self.variables:
            del self.variables[var]

    def simulate_token_transfer(self, call: HighLevelCall, transfer: ResolvedTransfer):
        dest = self.use(call.destination).val
        self.state.token_transfer(dest, transfer)

    def simulate_token_balance_of(
        self,
        call: HighLevelCall,
        account: z3.ExprRef,
        token_id: z3.ExprRef | None = None,
    ) -> z3.ExprRef:
        dest = self.use(call.destination).val
        return self.state.token_balance_of(dest, account, token_id)

    def simulate_token_owner_of(
        self,
        call: HighLevelCall,
        token_id: z3.ExprRef,
    ) -> z3.ExprRef:
        dest = self.use(call.destination).val
        return self.state.token_owner_of(dest, token_id)

    def simulate_owner(self, call: HighLevelCall) -> z3.ExprRef:
        dest = self.use(call.destination).val
        return self.state.owner(dest)
