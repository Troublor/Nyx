from abc import ABC, abstractmethod
from collections import defaultdict
from copy import copy
from typing import Optional

import z3
from slither import Slither
from slither.core.declarations import (
    SolidityVariable,
    Contract,
    Structure,
    FunctionContract,
    Function,
)
from slither.core.solidity_types import UserDefinedType, ElementaryType, ArrayType, Type
from slither.core.solidity_types.elementary_type import Uint
from slither.core.variables.state_variable import StateVariable
from slither.core.variables.variable import Variable
from slither.slithir.operations import Member, Index, Length, SolidityCall
from slither.slithir.variables import ReferenceVariable, Constant

from engine.sym_value import type_to_expr, ACCESSOR_MAP, DATATYPE_SORT, gen_unique_name


class AbstractEnv(ABC):
    def __init__(self):
        self.constraints: list[z3.BoolRef] = []

    def _type_to_expr(
        self,
        typ: Type | list[Type],
        value: str | int | bool = None,
        identifier: str = None,
        zero: bool = False,
    ) -> z3.ExprRef | list[z3.ExprRef]:
        val, constraints = AbstractEnv.type_to_expr_with_constraints(
            typ, value, identifier, zero
        )
        self.constraints.extend(constraints)
        return val

    @staticmethod
    def type_to_expr_with_constraints(
        typ: Type | list[Type],
        value: str | int | bool = None,
        identifier: str = None,
        zero: bool = False,
    ) -> tuple[z3.ExprRef | list[z3.ExprRef], list[z3.BoolRef]]:
        val = type_to_expr(typ, value, identifier, zero)
        constraints = []
        if isinstance(typ, ElementaryType):
            if typ.type in Uint:
                assert isinstance(val, (z3.ArithRef, z3.BitVecRef))
                constraints.append(val >= 0)
        return val, constraints

    @abstractmethod
    def access_var(self, var: Variable | SolidityVariable) -> z3.ExprRef:
        pass

    @abstractmethod
    def assign_var(self, var: Variable, val: z3.ExprRef) -> None:
        pass


class StateEnv(AbstractEnv):
    def __init__(self, contracts: list[Contract]):
        super().__init__()
        self.contracts = contracts
        # contract => storage(state) name => symbolic value
        self.storage: dict[str, dict[str, z3.ExprRef]] = {
            c.name: {
                v.name: self._type_to_expr(v.type, identifier=f"{v.canonical_name}")
                for v in c.state_variables
            }
            for c in contracts
        }
        self.contract_states: dict[str, dict[str, z3.ExprRef]] = {}
        for c in self.contracts:
            self._prepare_contract(c)

        # for external call to functions that is not in the given contract group,
        # we model them as pure functions, i.e., same input always gives the same output
        # abstract function => input => output
        self.interface_stereotypes: dict[
            str, dict[tuple[z3.ExprRef, ...], tuple[z3.ExprRef]]
        ] = defaultdict(dict)

    def _prepare_contract(self, c: Contract):
        self.contract_states[c.name] = {
            "address": self._type_to_expr(
                ElementaryType("address"),
                identifier=gen_unique_name(f"{c.name}_address"),
            ),
            "balance": self._type_to_expr(
                ElementaryType("uint"), identifier=gen_unique_name(f"{c.name}_balance")
            ),
            "code": self._type_to_expr(
                ElementaryType("bytes"), identifier=gen_unique_name(f"{c.name}_code")
            ),
            "codehash": self._type_to_expr(
                ElementaryType("bytes32"),
                identifier=gen_unique_name(f"{c.name}_codehash"),
            ),
        }

    def access_var(self, state_var: StateVariable) -> z3.ExprRef:
        cs = self.storage[state_var.contract.name]
        assert state_var.name in cs
        return cs[state_var.name]

    def get_storage(self, c: Contract, field: str) -> z3.ExprRef | None:
        c = self.storage[c.name]
        if field not in c:
            # When accessing the Enum declaration of a contract
            return None
        return c[field]

    def assign_var(self, state_var: StateVariable, val: z3.ExprRef) -> None:
        cs = self.storage[state_var.contract.name]
        cs[state_var.name] = val

    def get_address(self, c: Contract) -> z3.ExprRef:
        return self.contract_states[c.name]["address"]

    def call_to_abstract_function(
        self, f: Function, inputs: list[z3.ExprRef]
    ) -> tuple[z3.ExprRef]:
        assert not f.is_implemented
        assert f.return_type is not None
        stereotype = self.interface_stereotypes[f.canonical_name]
        rets = self._type_to_expr(
            f.return_type, identifier=gen_unique_name(f"{f.name}_ret")
        )
        # for ins, outs in stereotype.items():
        #     for i, ret in enumerate(rets):
        #         out = outs[i]
        #         rets[i] = z3.If(
        #             z3.And(*[i == o for i, o in zip(inputs, ins)]), out, ret
        #         )

        stereotype[tuple(inputs)] = tuple(rets)
        return tuple(rets)

    def copy(self) -> "StateEnv":
        cp = copy(self)
        cp.constraints = [c for c in self.constraints]
        cp.storage = {c: {k: v for k, v in d.items()} for c, d in self.storage.items()}
        cp.contract_states = {
            c: {k: v for k, v in d.items()} for c, d in self.contract_states.items()
        }
        return cp


class TxEnv(AbstractEnv):
    def __init__(self, origin: z3.ExprRef = None):
        super().__init__()
        self.origin = (
            origin
            if origin is not None
            else self._type_to_expr(ElementaryType("address"), identifier="tx_origin")
        )

    def access_var(self, var: SolidityVariable) -> z3.ExprRef:
        assert isinstance(var, SolidityVariable)
        if var.name == "tx.origin":
            return self.origin
        else:
            return type_to_expr(var.type, identifier=var.name)

    def assign_var(self, var: Variable, val: z3.ExprRef) -> None:
        raise AssertionError("readonly variable")


class MsgCallEnv(TxEnv):
    def __init__(
        self,
        origin: z3.ExprRef = None,
        sender: z3.ExprRef = None,
        value: z3.ExprRef = None,
        this: z3.ExprRef = None,
    ):
        super().__init__(origin)
        self.sender = (
            sender
            if sender is not None
            else self._type_to_expr(
                ElementaryType("address"), identifier=gen_unique_name("msg_sender")
            )
        )
        self.msg_value = (
            value
            if value is not None
            else self._type_to_expr(
                ElementaryType("uint"), identifier=gen_unique_name("msg_value")
            )
        )
        self.this = (
            this
            if this is not None
            else self._type_to_expr(
                ElementaryType("address"), identifier=gen_unique_name("this")
            )
        )

    def access_var(self, var: SolidityVariable) -> z3.ExprRef:
        assert isinstance(var, SolidityVariable)
        if var.name == "msg.sender":
            return self.sender
        elif var.name == "msg.value":
            return self.msg_value
        elif var.name == "this":
            return self.this
        else:
            return TxEnv.access_var(self, var)

    def assign_var(self, var: Variable, val: z3.ExprRef) -> None:
        raise AssertionError("readonly variable")


class LocalEnv(AbstractEnv):
    def __init__(self, state_env: StateEnv, call_env: MsgCallEnv):
        super().__init__()
        self.state_env = state_env
        self.call_env = call_env
        self.variables: dict[str, z3.ExprRef] = dict()
        # reference variable => (base variable, reference key)
        self.ref_info: dict[str, tuple[Variable, str | z3.ExprRef]] = dict()
        # variable => set of reference variables that use this variable as base
        self.refers: dict[str, set[ReferenceVariable]] = defaultdict(set)
        # reference variable => whether it is pseudo reference (reference variable but treated as normal variable)
        self.pseudo_refs: dict[str, bool] = defaultdict(lambda: False)

    def access_var(
        self, var: Variable | SolidityVariable
    ) -> z3.ExprRef | tuple[z3.ExprRef, ...]:
        if isinstance(var, StateVariable):
            return self.state_env.access_var(var)
        elif isinstance(var, SolidityVariable):
            return self.call_env.access_var(var)
            # raise AssertionError("solidity variable not supported: " + var.name)
        else:
            if var.type is None:
                return None  # FIXME this is bug in SlithIR
            if var.name not in self.variables or self.variables[var.name] is None:
                val = self._type_to_expr(
                    var.type,
                    value=var.value if isinstance(var, Constant) else None,
                    identifier=gen_unique_name(var.name),
                )
                self._assign_var(var, val)
            return self.variables[var.name]

    def assign_var(
        self,
        var: Variable,
        val: z3.ExprRef | tuple[z3.ExprRef, ...],
    ) -> None:
        root = var
        expr = val
        if isinstance(var, ReferenceVariable) and var.points_to is None:
            self.pseudo_refs[var.name] = True
        if isinstance(var, ReferenceVariable) and var.name not in self.pseudo_refs:
            root, expr = self._compute_root(var, val)
        self._update_forward(root, expr)

    def _assign_var(self, var: Variable, val: z3.ExprRef | tuple[z3.ExprRef, ...]):
        if isinstance(var, StateVariable):
            self.state_env.assign_var(var, val)
        else:
            self.variables[var.name] = val

    def _update_array(
        self, _val: z3.ArrayRef, key: z3.ExprRef, _value: z3.ExprRef
    ) -> z3.ArrayRef:
        return z3.Store(_val, key, _value)

    def _update_datatype(
        self,
        structure: Structure,
        _val: z3.DatatypeRef,
        key: str,
        _value: z3.ExprRef,
    ) -> z3.DatatypeRef:
        assert ACCESSOR_MAP in structure.context and DATATYPE_SORT in structure.context
        args = []
        for k, accessor in structure.context[ACCESSOR_MAP].items():
            if k == key:
                args.append(_value)
            else:
                args.append(accessor(_val))
        return _val.sort().constructor(0)(*args)

    def _update_forward(self, _var: Variable, _val: z3.ExprRef) -> None:
        self._assign_var(_var, _val)
        _refers = self.refers[_var.name]
        for _refer in _refers:
            assert isinstance(_refer, ReferenceVariable)
            _ref_path = self.ref_info[_refer.name]
            assert _ref_path is not None
            assert _ref_path[0] is _var
            _ref_key = _ref_path[1]
            if isinstance(_val, z3.ArrayRef):
                assert isinstance(_ref_key, z3.ExprRef)
                _refer_new_val = z3.Select(_val, _ref_key)
            elif isinstance(_val, z3.DatatypeRef):
                assert isinstance(_ref_key, str)
                _var_type = _var.type
                assert isinstance(_var_type, UserDefinedType)
                structure = _var_type.type
                assert isinstance(structure, Structure)
                assert ACCESSOR_MAP in structure.context
                _accessor = structure.context[ACCESSOR_MAP][_ref_key]
                _refer_new_val = _accessor(_val)
            else:
                raise ValueError()

            self._update_forward(_refer, _refer_new_val)

    def _compute_root(
        self, _var: Variable, _val: z3.ExprRef
    ) -> tuple[Variable, z3.ExprRef]:
        if isinstance(_var, ReferenceVariable) and not self.pseudo_refs[_var.name]:
            _base, _key = self.ref_info[_var.name]
            _base_val = self.access_var(_base)
            if isinstance(_base_val, z3.ArrayRef):
                assert isinstance(_key, z3.ExprRef)
                _base_new_val = self._update_array(_base_val, _key, _val)
            elif isinstance(_base_val, z3.DatatypeRef):
                assert isinstance(_key, str)
                base_type = _base.type
                assert isinstance(base_type, UserDefinedType)
                structure = base_type.type
                assert isinstance(structure, Structure)
                _base_new_val = self._update_datatype(structure, _base_val, _key, _val)
            else:
                raise ValueError()
            return self._compute_root(_base, _base_new_val)
        else:
            return _var, _val

    def def_ref(self, var: ReferenceVariable, op: Member | Index) -> None:
        """
        Called whenever a reference variable is defined.
        It prepares the REF_PATH_KEY and REF_ROOT_KEY in the variable context.
        :param var:
        :param op:
        :return:
        """
        base = op.variable_left
        base_val = self.access_var(base)
        assert isinstance(base_val, (z3.ArrayRef, z3.DatatypeRef)), base_val.sort()

        if isinstance(op, Member):
            ref_key = op.variable_right.value
            assert isinstance(ref_key, str)
        elif isinstance(op, Index):
            ref_key = self.access_var(op.variable_right)
            assert isinstance(ref_key, z3.ExprRef)
        else:
            raise ValueError()

        ref_path = (base, ref_key)
        self.ref_info[var.name] = ref_path
        if isinstance(base_val, z3.ArrayRef):
            assert isinstance(ref_key, z3.ExprRef)
            field_value = z3.Select(base_val, ref_key)
        elif isinstance(base_val, z3.DatatypeRef):
            assert isinstance(ref_key, str)
            structure = base.type.type
            assert isinstance(structure, Structure)
            assert (
                ACCESSOR_MAP in structure.context and DATATYPE_SORT in structure.context
            )
            accessor = structure.context[ACCESSOR_MAP][ref_key]
            try:
                field_value = accessor(base_val)
            except Exception as e:
                print(ref_key)
                print(var.node.source_mapping.lines)
                raise e
        else:
            raise ValueError()

        self._assign_var(var, field_value)

        # update base
        self.refers[base.name].add(var)


class Env(AbstractEnv):
    @staticmethod
    def from_slither(
        slither: Slither,
        fn: Function,
        sender: z3.ExprRef = None,
        value: z3.ExprRef = None,
    ) -> "Env":
        assert isinstance(fn, FunctionContract)
        state = StateEnv(slither.contracts)
        if sender is None:
            sender = type_to_expr(
                ElementaryType("address"), identifier=gen_unique_name("from")
            )
        assert isinstance(sender, (z3.ArithRef, z3.BitVecRef))
        if value is None:
            value = type_to_expr(
                ElementaryType("uint256"), identifier=gen_unique_name("value")
            )
        assert isinstance(value, (z3.ArithRef, z3.BitVecRef))
        this = state.contract_states[fn.contract.name]["address"]
        call = MsgCallEnv(sender, sender, value, this)
        local = LocalEnv(state, call)
        env = Env(state, call, local)
        env.constraints.append(sender > 0)
        env.constraints.append(value > 0)
        return env

    def __init__(self, state: StateEnv, call: MsgCallEnv, local: LocalEnv):
        super().__init__()
        self.state = state
        self.call = call
        self.local = local

    def access_var(self, var: Variable | SolidityVariable) -> z3.ExprRef:
        if isinstance(var, SolidityVariable):
            return self.call.access_var(var)
        elif isinstance(var, StateVariable):
            return self.state.access_var(var)
        else:
            return self.local.access_var(var)

    def assign_var(self, var: Variable, val: z3.ExprRef) -> None:
        if isinstance(var, StateVariable):
            return self.state.assign_var(var, val)
        else:
            return self.local.assign_var(var, val)

    def def_ref(
        self, var: ReferenceVariable, op: Member | Index | Length | SolidityCall
    ) -> None:
        if isinstance(op, Length):
            arr = self.access_var(op.value)
            assert isinstance(arr, z3.ArrayRef) or isinstance(arr, z3.BitVecRef)
            typ = op.value.type
            assert (
                isinstance(typ, ArrayType)
                or isinstance(typ, ElementaryType)
                and typ.is_dynamic
            )
            if typ.is_dynamic:
                _length = self._type_to_expr(ElementaryType("uint"))
            else:
                _length = self._type_to_expr(
                    ElementaryType("uint"), value=typ.length_value
                )
            self.local.pseudo_refs[var.name] = True
            self.local.assign_var(var, _length)
        elif isinstance(op, Member) and isinstance(op.variable_left, Contract):
            # special case when accessing a constant in a library
            assert isinstance(op.variable_right, Constant)
            field = op.variable_right.value
            assert isinstance(field, str)
            self.local.pseudo_refs[var.name] = True
            val = self.state.get_storage(op.variable_left, field)
            if val is not None:
                self.assign_var(op.lvalue, val)
        elif isinstance(op, SolidityCall) and op.function.name in [
            "type()",
            "type(address)",
        ]:
            self.local.pseudo_refs[var.name] = True
        else:
            if op.variable_left.type is None:
                return
            self.local.def_ref(var, op)

    @property
    def contract_states(self) -> dict:
        return self.state.contract_states

    def _find_contract_name_with_addr(
        self, addr: z3.ExprRef | Contract
    ) -> Optional[str]:
        if isinstance(addr, Contract):
            return addr.name
        for c, state in self.contract_states.items():
            if str(state["address"]) == str(addr):
                return c
        return None

    def get_balance(self, account: Contract | z3.ExprRef) -> z3.ExprRef:
        c = self._find_contract_name_with_addr(account)
        if isinstance(c, str):
            return self.contract_states[c]["balance"]
        else:
            return self._type_to_expr(ElementaryType("uint"))

    def get_code(self, account: Contract | z3.ExprRef) -> z3.ExprRef:
        c = self._find_contract_name_with_addr(account)
        if isinstance(c, str):
            return self.contract_states[c]["code"]
        else:
            return self._type_to_expr(ElementaryType("bytes"))

    def get_codehash(self, account: Contract | z3.ExprRef) -> z3.ExprRef:
        c = self._find_contract_name_with_addr(account)
        if isinstance(c, str):
            return self.contract_states[c]["codehash"]
        else:
            return self._type_to_expr(ElementaryType("bytes32"))

    def get_address(self, contract: Contract) -> z3.ExprRef:
        assert contract.name in self.contract_states
        return self.contract_states[contract.name]["address"]

    def external_call(
        self,
        callee: z3.ExprRef = None,
        msg_sender: z3.ExprRef = None,
        msg_value: z3.ExprRef = None,
    ) -> "Env":
        cp = copy(self)
        call = MsgCallEnv(self.call.origin, msg_sender, msg_value, callee)
        cp.call = call
        cp.local = LocalEnv(cp.state, call)
        return cp

    def internal_call(self) -> "Env":
        cp = copy(self)
        cp.local = LocalEnv(cp.state, cp.call)
        return cp

    def call_to_abstract_function(
        self, callee: Function, args: list[z3.ExprRef]
    ) -> tuple[z3.ExprRef, ...] | None:
        assert not callee.is_implemented
        if callee.return_type is None:
            return None
        else:
            return self.state.call_to_abstract_function(callee, args)
