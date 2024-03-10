from abc import ABC, abstractmethod
from typing import *

import z3
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations import FunctionContract, Function, Contract
from slither.core.declarations.solidity_variables import (
    SOLIDITY_FUNCTIONS,
    SolidityVariable,
)
from slither.core.expressions import UnaryOperationType
from slither.core.solidity_types import UserDefinedType, ElementaryType, ArrayType
from slither.core.variables.state_variable import StateVariable
from slither.core.variables.variable import Variable
from slither.slithir.operations import *
from slither.slithir.variables import ReferenceVariable, TupleVariable, Constant

from engine.env import Env
from engine.sym_value import is_signed_type, type_to_expr, gen_unique_name
from hfg.inter_contract import INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY
from hfg.intra_contract import INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY

""" Hyper Parameters """
MAX_PATH_CONDITIONS = 256


class ReturnResult(object):
    def __init__(self, returns: tuple[z3.ExprRef], revert_condition: z3.BoolRef):
        self.returns = returns
        self.revert_condition = revert_condition


class ConditionResult(object):
    def __init__(self, _condition: z3.BoolRef):
        self.condition = _condition


class ExecutionController(ABC):
    @abstractmethod
    def before_op(
        self, env: Env, op: Operation, path_conditions: list[z3.BoolRef]
    ) -> None:
        pass

    @abstractmethod
    def after_op(
        self, env: Env, op: Operation, path_conditions: list[z3.BoolRef]
    ) -> None:
        pass

    @abstractmethod
    def before_call(
        self, env: Env, call_op: Call, path_conditions: list[z3.BoolRef]
    ) -> bool:
        """
        :param path_conditions:
        :param env:
        :param call_op:
        :return: Whether to skip the call
        """
        pass


class DefaultController(ExecutionController):
    def before_op(
        self, env: Env, op: Operation, path_conditions: list[z3.BoolRef]
    ) -> None:
        pass

    def after_op(
        self, env: Env, op: Operation, path_conditions: list[z3.BoolRef]
    ) -> None:
        pass

    def before_call(
        self, env: Env, call_op: Call, path_conditions: list[z3.BoolRef]
    ) -> bool:
        return False


class FunctionExecutor(object):
    def __init__(
        self,
        fn: Function,
        env: Env,
        controller: ExecutionController = None,
        path_conditions: list[z3.BoolRef] = None,
        visited: set[Node] = None,
    ):
        self.env = env
        self.function = fn
        self.controller = controller if controller is not None else DefaultController()

        self._visited: set[Node] = visited if visited is not None else set()

        self._path_conditions: List[z3.BoolRef] = (
            path_conditions if path_conditions is not None else []
        )
        self._revert_conditions: List[z3.BoolRef] = []
        self._returns_cases: List[tuple[tuple[z3.ExprRef], z3.BoolRef]] = []

    def execute(self, *args: z3.ExprRef) -> ReturnResult:
        # assignment arguments
        assert len(args) == len(self.function.parameters)
        for i, arg in enumerate(args):
            self.assign(self.function.parameters[i], arg)

        # execute
        if self.function.entry_point is not None:
            self.execute_node(self.function.entry_point)
        else:
            pass
        revert_condition = None

        # prepare return result
        if len(self._revert_conditions) == 1:
            revert_condition = self._revert_conditions[0]
        elif len(self._revert_conditions) > 1:
            revert_condition = z3.Or(*self._revert_conditions)

        return_values: list[z3.ExprRef] = []
        for r in self.function.returns:
            return_values.append(self.access(r))
        for case in self._returns_cases:
            for i, rv in enumerate(case[0]):
                return_values[i] = z3.If(case[1], rv, return_values[i])
        return ReturnResult(tuple(return_values), revert_condition)

    def execute_node(self, node: Node):
        if node in self._visited and node.type not in [
            NodeType.ENDIF,
            NodeType.ENDLOOP,
        ]:
            # execute loop/recursion only once
            return
        self._visited.add(node)

        for i, op in enumerate(node.irs):
            r = self.execute_op(op)
            if isinstance(r, ConditionResult):
                assert len(node.sons) == 2
                assert i == len(node.irs) - 1
                # True branch
                self._path_conditions.append(r.condition)
                self.execute_node(node.sons[0])
                self._path_conditions.pop()
                # False branch
                self._path_conditions.append(z3.Not(r.condition))
                self.execute_node(node.sons[1])
                self._path_conditions.pop()
                break
        else:
            if len(node.sons) > 0:
                assert len(node.sons) == 1
                next_node = node.sons[0]
                self.execute_node(next_node)

        self._visited.remove(node)

    def execute_op(self, op: Operation) -> Optional[ConditionResult]:
        """
        Execute one operation.
        Update environments, and revert conditions
        :param op:
        :return:
        """
        try:
            self.controller.before_op(self.env, op, self._path_conditions)
            if isinstance(op, Assignment):
                return self._assignment_op(op)
            elif isinstance(op, Binary):
                return self._binary_op(op)
            elif isinstance(op, Condition):
                return self._condition_op(op)
            elif isinstance(op, Delete):
                return self._delete_op(op)
            elif isinstance(op, EventCall):
                return self._event_call_op(op)
            elif isinstance(op, HighLevelCall) and not isinstance(op, LibraryCall):
                return self._high_level_call_op(op)
            elif isinstance(op, Index):
                return self._index_op(op)
            elif isinstance(op, InitArray):
                return self._init_array_op(op)
            elif isinstance(op, InternalCall):
                return self._internal_call_op(op)
            elif isinstance(op, InternalDynamicCall):
                return self._internal_dynamic_call_op(op)
            elif isinstance(op, Length):
                return self._length_op(op)
            elif isinstance(op, LibraryCall):
                return self._library_call_op(op)
            elif isinstance(op, LowLevelCall):
                return self._low_level_call_op(op)
            elif isinstance(op, Member):
                return self._member_op(op)
            elif isinstance(op, NewArray):
                return self._new_array_op(op)
            elif isinstance(op, NewElementaryType):
                return self._new_elementary_type_op(op)
            elif isinstance(op, NewContract):
                return self._new_contract_op(op)
            elif isinstance(op, NewStructure):
                return self._new_structure_op(op)
            elif isinstance(op, Nop):
                return self._nop_op(op)
            elif isinstance(op, Phi):
                return self._phi_op(op)
            elif isinstance(op, Return):
                return self._return_op(op)
            elif isinstance(op, Send):
                return self._send_op(op)
            elif isinstance(op, SolidityCall):
                return self._solidity_call_op(op)
            elif isinstance(op, Transfer):
                return self._transfer_op(op)
            elif isinstance(op, TypeConversion):
                return self._type_conversion_op(op)
            elif isinstance(op, Unpack):
                return self._unpack_op(op)
            elif isinstance(op, Unary):
                return self._unary_op(op)
            else:
                raise NotImplementedError(op)
        finally:
            self.controller.after_op(self.env, op, self._path_conditions)

    def access(
        self, var: Variable | SolidityVariable
    ) -> z3.ExprRef | tuple[z3.ExprRef, ...]:
        return self.env.access_var(var)

    def assign(
        self,
        var: Variable | SolidityVariable,
        val: z3.ExprRef | tuple[z3.ExprRef] = None,
    ) -> None:
        if var.type is None:
            # not sure why there are variable with type None, but in case it happens,
            # We do not assign anything to it.
            return
        if val is None:
            # access it will assign an unconstrained symbolic value to it
            self.env.access_var(var)
            return

        cond = None
        if len(self._path_conditions) == 1:
            cond = self._path_conditions[0]
        elif len(self._path_conditions) > 1:
            cond = z3.And(*self._path_conditions[-MAX_PATH_CONDITIONS:])

        if cond is None:
            self.env.assign_var(var, val)
            return

        if (
            isinstance(var, StateVariable)
            or isinstance(var, ReferenceVariable)
            and isinstance(var.points_to_origin, StateVariable)
            # or var in self.function.returns
        ):
            # we need to attach path condition to state variables
            origin = self.access(var)
            val = z3.If(cond, val, origin)
            self.env.assign_var(var, val)
            return
        else:
            # for local variables we don't bother to attach path condition,
            # since we are enumerating all paths.
            self.env.assign_var(var, val)
            return

    def _assignment_op(self, op: Assignment):
        """
        Assignment operation
        :param op:
        :return:
        """
        if op.rvalue.type is None:
            op.rvalue.type = op.lvalue.type
        right_val = self.access(op.rvalue)

        if isinstance(op.lvalue.type, ArrayType) and not isinstance(
            op.rvalue.type, ArrayType
        ):
            # workaround for issue crytic/slither#1748
            key_expr = type_to_expr(op.lvalue.type)
            self.assign(op.lvalue, z3.K(key_expr.sort(), right_val))
            return

        self.assign(op.lvalue, right_val)

    def _binary_op(self, op: Binary):
        arg1_val = self.access(op.variable_left)
        arg2_val = self.access(op.variable_right)

        arg1_val_expr = arg1_val
        arg2_val_expr = arg2_val

        expr = None
        if isinstance(arg1_val_expr, (z3.ArithRef, z3.BitVecRef)) and isinstance(
            arg2_val_expr, (z3.ArithRef, z3.BitVecRef)
        ):
            signed = is_signed_type(op.lvalue.type)
            is_bv = isinstance(arg1_val_expr, z3.BitVecRef) and isinstance(
                arg2_val_expr, z3.BitVecRef
            )
            arg1_bv = arg1_val_expr if is_bv else z3.Int2BV(arg1_val_expr, 256)
            arg2_bv = arg2_val_expr if is_bv else z3.Int2BV(arg2_val_expr, 256)
            # number like operations
            if op.type == BinaryType.POWER:
                expr = arg1_val_expr**arg2_val_expr
            elif op.type == BinaryType.MULTIPLICATION:
                expr = arg1_val_expr * arg2_val_expr
            elif op.type == BinaryType.DIVISION:
                expr = arg1_val_expr / arg2_val_expr
            elif op.type == BinaryType.MODULO:
                try:
                    expr = arg1_val_expr % arg2_val_expr
                except z3.Z3Exception:
                    # sometimes the operand becomes z3.Real number
                    # in these cases, we just use the unconstrained expression
                    expr = self.access(op.lvalue)
            elif op.type == BinaryType.ADDITION:
                expr = arg1_val_expr + arg2_val_expr
            elif op.type == BinaryType.SUBTRACTION:
                expr = arg1_val_expr - arg2_val_expr
            elif op.type == BinaryType.LEFT_SHIFT:
                expr = arg1_bv << arg2_bv
                if not is_bv:
                    expr = z3.BV2Int(expr, signed)
            elif op.type == BinaryType.RIGHT_SHIFT:
                expr = arg1_bv >> arg2_bv
                if not is_bv:
                    expr = z3.BV2Int(expr, signed)
            elif op.type == BinaryType.AND:
                expr = arg1_bv & arg2_bv
                if not is_bv:
                    expr = z3.BV2Int(expr, signed)
            elif op.type == BinaryType.CARET:
                expr = arg1_bv ^ arg2_bv
                if not is_bv:
                    expr = z3.BV2Int(expr, signed)
            elif op.type == BinaryType.OR:
                expr = arg1_bv | arg2_bv
                if not is_bv:
                    expr = z3.BV2Int(expr, signed)
            elif op.type == BinaryType.LESS:
                expr = arg1_val_expr < arg2_val_expr
            elif op.type == BinaryType.GREATER:
                expr = arg1_val_expr > arg2_val_expr
            elif op.type == BinaryType.LESS_EQUAL:
                expr = arg1_val_expr <= arg2_val_expr
            elif op.type == BinaryType.GREATER_EQUAL:
                expr = arg1_val_expr >= arg2_val_expr
        if isinstance(arg1_val_expr, z3.ExprRef) and isinstance(
            arg2_val_expr, z3.ExprRef
        ):
            # the most general operations
            if op.type == BinaryType.EQUAL:
                expr = arg1_val_expr == arg2_val_expr
            elif op.type == BinaryType.NOT_EQUAL:
                expr = arg1_val_expr != arg2_val_expr
        if isinstance(arg1_val_expr, z3.BoolRef) and isinstance(
            arg2_val_expr, z3.BoolRef
        ):
            # boolean operations
            if op.type == BinaryType.ANDAND:
                expr = z3.And(arg1_val_expr, arg2_val_expr)
            elif op.type == BinaryType.OROR:
                expr = z3.Or(arg1_val_expr, arg2_val_expr)
        self.assign(op.lvalue, expr)

    def _condition_op(self, op: Condition) -> ConditionResult:
        cond = self.access(op.value)
        assert isinstance(cond, z3.BoolRef)
        return ConditionResult(cond)

    def _delete_op(self, op: Delete):
        typ = op.variable.type
        zero = type_to_expr(typ, zero=True)
        self.assign(op.variable, zero)

    def _event_call_op(self, op: EventCall):
        return

    def _high_level_call_op(self, op: HighLevelCall):
        if isinstance(op.function, StateVariable):
            # access the public state variable of another contract
            val = self.access(op.function)
            self.assign(op.lvalue, val)
            return

        skip = self.controller.before_call(self.env, op, self._path_conditions)
        if skip:
            return

        callees: list[Function] = (
            op.context[INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY]
            if INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY in op.context
            else []
        )

        returns: list[z3.ExprRef | None] = [
            None for _ in range(len(op.function.returns))
        ]

        if len(callees) > 0:
            for callee in callees:
                if isinstance(callee, FunctionContract):
                    callee_contract = callee.contract
                else:
                    callee_contract = None
                sender = self.env.access_var(SolidityVariable("this"))
                value = (
                    self.access(op.call_value)
                    if op.call_value is not None
                    else type_to_expr(ElementaryType("uint"), zero=True)
                )
                callee_addr = self.env.get_address(callee_contract)
                state = self.env.external_call(
                    callee=callee_addr, msg_sender=sender, msg_value=value
                )
                executor = FunctionExecutor(
                    callee,
                    state,
                    self.controller,
                    self._path_conditions,
                    self._visited,
                )
                args = [self.access(a) for a in op.arguments]
                r = executor.execute(*args)
                if r.revert_condition is not None:
                    self._revert_conditions.append(r.revert_condition)
                for i, ret in enumerate(r.returns):
                    if returns[i] is None:
                        returns[i] = ret
                    else:
                        # unconditionally alternative value (condition is unconstrained value)
                        returns[i] = z3.If(
                            z3.BoolVal(gen_unique_name()), ret, returns[i]
                        )

        else:
            # unimplemented function
            rets = self.env.call_to_abstract_function(op.function, op.arguments)
            if op.lvalue is not None:
                if isinstance(op.lvalue, TupleVariable):
                    self.assign(op.lvalue, rets)
                else:
                    self.assign(op.lvalue, rets[0])

        if op.lvalue is not None:
            if isinstance(op.lvalue, TupleVariable):
                self.assign(op.lvalue, tuple[z3.ExprRef](returns))
            else:
                self.assign(op.lvalue, returns[0])

    def _index_op(self, op: Index):
        self.env.def_ref(op.lvalue, op)

    def _init_array_op(self, op: InitArray):
        elems = [self.access(v) for v in op.init_values]
        val = self.access(op.lvalue)
        assert isinstance(val, z3.ArrayRef)
        for i, elem in enumerate(elems):
            val = z3.Store(val, i, elem)
        self.assign(op.lvalue, val)

    def _internal_call_op(self, op: InternalCall):
        skip = self.controller.before_call(self.env, op, self._path_conditions)
        if skip:
            return

        callee = op.function
        executor = FunctionExecutor(
            callee,
            self.env.internal_call(),
            self.controller,
            self._path_conditions,
            self._visited,
        )
        args = [self.access(a) for a in op.arguments]
        r = executor.execute(*args)
        if r.revert_condition is not None:
            self._revert_conditions.append(r.revert_condition)
        if op.lvalue is not None:
            if isinstance(op.lvalue, TupleVariable):
                self.assign(op.lvalue, r.returns)
            else:
                self.assign(op.lvalue, r.returns[0])

    def _internal_dynamic_call_op(self, op: InternalDynamicCall):
        if INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY not in op.context:
            return

        skip = self.controller.before_call(self.env, op, self._path_conditions)
        if skip:
            return

        callees: list[Function] = op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY]
        if len(callees) == 0:
            return

        returns: list[z3.ExprRef | None] = [
            None for _ in range(len(callees[0].returns))
        ]
        for callee in callees:
            executor = FunctionExecutor(
                callee,
                self.env.internal_call(),
                self.controller,
                self._path_conditions,
                self._visited,
            )
            args = [self.access(a) for a in op.arguments]
            r = executor.execute(*args)
            if r.revert_condition is not None:
                self._revert_conditions.append(r.revert_condition)
            for i, ret in enumerate(r.returns):
                if returns[i] is None:
                    returns[i] = ret
                else:
                    # unconditionally alternative value (condition is unconstrained value)
                    returns[i] = z3.If(z3.BoolVal(gen_unique_name()), ret, returns[i])

        if op.lvalue is not None:
            if isinstance(op.lvalue, TupleVariable):
                self.assign(op.lvalue, tuple[z3.ExprRef](returns))
            else:
                self.assign(op.lvalue, returns[0])

    def _length_op(self, op: Length):
        self.env.def_ref(op.lvalue, op)

    def _library_call_op(self, op: LibraryCall):
        skip = self.controller.before_call(self.env, op, self._path_conditions)
        if skip:
            return

        if (
            op.function.name in ["add", "tryAdd"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) >= 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2, (z3.ArithRef, z3.BitVecRef))
            self.assign(op.lvalue, arg1 + arg2)
            return
        elif (
            op.function.name in ["sub", "trySub"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) >= 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2, (z3.ArithRef, z3.BitVecRef))
            self.assign(op.lvalue, arg1 - arg2)
        elif (
            op.function.name in ["mul", "tryMul"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) >= 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2, (z3.ArithRef, z3.BitVecRef))
            self.assign(op.lvalue, arg1 * arg2)
        elif (
            op.function.name in ["div", "sdiv", "tryDiv"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) >= 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2, (z3.ArithRef, z3.BitVecRef))
            self.assign(op.lvalue, arg1 / arg2)
        elif (
            op.function.name in ["mod", "smod", "tryMod"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) >= 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, z3.ArithRef)
            assert isinstance(arg2, z3.ArithRef)
            self.assign(op.lvalue, arg1 % arg2)
        elif (
            op.function.name == "exp"
            and len(op.function.parameters) == 2
            and len(op.function.returns) == 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            assert isinstance(arg1, z3.ArithRef)
            assert isinstance(arg2, z3.ArithRef)
            self.assign(op.lvalue, arg1**arg2)
        elif (
            op.function.name == "addmod"
            and len(op.function.parameters) == 3
            and len(op.function.returns) == 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            arg3 = self.access(op.arguments[2])
            assert isinstance(arg1, z3.ArithRef)
            assert isinstance(arg2, z3.ArithRef)
            assert isinstance(arg3, z3.ArithRef)
            self.assign(op.lvalue, (arg1 + arg2) % arg3)
        elif (
            op.function.name == "mulmod"
            and len(op.function.parameters) == 3
            and len(op.function.returns) == 1
        ):
            arg1 = self.access(op.arguments[0])
            arg2 = self.access(op.arguments[1])
            arg3 = self.access(op.arguments[2])
            assert isinstance(arg1, z3.ArithRef)
            assert isinstance(arg2, z3.ArithRef)
            assert isinstance(arg3, z3.ArithRef)
            self.assign(op.lvalue, (arg1 * arg2) % arg3)
        elif (
            op.function.name == "sqrt"
            and len(op.function.parameters) == 1
            and len(op.function.returns) == 1
        ):
            arg = self.access(op.arguments[0])
            assert isinstance(arg, z3.ArithRef)
            self.assign(op.lvalue, z3.ToInt(z3.Sqrt(z3.ToReal(arg))))
        else:
            # For simplicity, we treat library call as internal call.
            # However, call to dynamic library is mishandled here.
            callee = op.function
            executor = FunctionExecutor(
                callee,
                self.env.internal_call(),
                self.controller,
                self._path_conditions,
                self._visited,
            )
            args = [self.access(a) for a in op.arguments]
            r = executor.execute(*args)
            if r.revert_condition is not None:
                self._revert_conditions.append(r.revert_condition)
            if op.lvalue is not None:
                if isinstance(op.lvalue, TupleVariable):
                    self.assign(op.lvalue, r.returns)
                else:
                    self.assign(op.lvalue, r.returns[0])

    def _low_level_call_op(self, op: LowLevelCall):
        skip = self.controller.before_call(self.env, op, self._path_conditions)
        if skip:
            return
        # TODO
        return

    def _member_op(self, op: Member):
        self.env.def_ref(op.lvalue, op)

    def _new_array_op(self, op: NewArray):
        # FIXME: workaround for issue crytic/slither#1776
        typ = op.array_type
        for _ in range(op.depth):
            typ = ArrayType(typ, None)
        op.lvalue.type = typ

    def _new_elementary_type_op(self, op: NewElementaryType):
        val = self.access(op.lvalue)
        self.assign(op.lvalue, val)

    def _new_contract_op(self, op: NewContract):
        c = op.contract_created
        addr = self.env.get_address(c)
        self.assign(op.lvalue, addr)

    def _new_structure_op(self, op: NewStructure):
        sort = self.access(op.lvalue).sort()
        assert isinstance(sort, z3.DatatypeSortRef)
        constructor = sort.constructor(0)
        val = constructor(*[self.access(arg) for arg in op.arguments])
        self.assign(op.lvalue, val)

    def _nop_op(self, op: Nop):
        return

    def _phi_op(self, op: Phi):
        # Phi will not occur in non-ssa operations
        return

    def _return_op(self, op: Return):
        assert len(op.values) == len(self.function.returns)
        returns: list[z3.ExprRef] = []
        for i, v in enumerate(op.values):
            val = self.access(v)
            assert isinstance(val, z3.ExprRef)
            self.assign(self.function.returns[i], val)
            returns.append(val)
        cond: z3.BoolRef | None = None
        if len(self._path_conditions) == 1:
            cond = self._path_conditions[0]
        elif len(self._path_conditions) > 1:
            cond = z3.And(*self._path_conditions)
        if cond is not None:
            self._returns_cases.append((tuple(returns), cond))

    def _send_op(self, op: Send):
        if op.lvalue is not None:
            self.assign(op.lvalue)

    def _solidity_call_op(self, op: SolidityCall):
        fn = op.function
        returns = None
        assert fn.name in SOLIDITY_FUNCTIONS
        if fn.name == "gasleft()":
            returns = self.access(op.lvalue.type)
        elif fn.name in [
            "assert(bool)",
            "require(bool)",
            "require(bool,string)",
            "revert()",
            "revert(string)",
            "revert ",
        ]:
            if len(op.arguments) > 0:
                arg0_val = self.access(op.arguments[0])
                assert isinstance(arg0_val, z3.BoolRef)
                conds = self._path_conditions + [arg0_val]
                cond = z3.And(*conds)
            else:
                cond = z3.And(*self._path_conditions)
            self._revert_conditions.append(cond)
        elif fn.name in [
            "addmod(uint256,uint256,uint256)",
            "mulmod(uint256,uint256,uint256)",
        ]:
            arg1_expr = self.access(op.arguments[0])
            arg2_expr = self.access(op.arguments[1])
            arg3_expr = self.access(op.arguments[2])
            assert isinstance(arg1_expr, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2_expr, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg3_expr, (z3.ArithRef, z3.BitVecRef))
            if fn.name.startswith("addmod"):
                expr = arg1_expr + arg2_expr % arg3_expr
            elif fn.name.startswith("mulmod"):
                expr = arg1_expr * arg2_expr % arg3_expr
            else:
                raise NotImplementedError()
            returns = expr

        elif fn.name in [
            "keccak256()",
            "keccak256(bytes32)",
            "keccak256(bytes)",
            "sha256()",
            "sha256(bytes)",
            "sha256(bytes32)",
            "sha3()",
            "ripemd160()",
            "ripemd160(bytes)",
            "ecrecover(bytes32,uint8,bytes32,bytes32)",
        ]:
            returns = self.access(op.lvalue)
        elif fn.name in [
            "selfdestruct(address)",
            "suicide(address)",
            "log0(bytes32)",
            "log1(bytes32,bytes32)",
            "log2(bytes32,bytes32)",
            "log3(bytes32,bytes32)",
        ]:
            returns = None
        elif fn.name == "blockhash":
            returns = self.access(op.lvalue)
        elif fn.name == "this.balance()":
            assert isinstance(self.function, FunctionContract)
            returns = self.env.get_balance(self.function.contract)
        elif fn.name in [
            "abi.encode()",
            "abi.encodePacked()",
            "abi.encodeWithSelector()",
            "abi.encodeWithSignature()",
        ]:
            returns = self.access(op.lvalue)
        elif fn.name in [
            "bytes.concat()",
            "string.concat()",
        ]:
            returns = self.access(op.lvalue)
        elif fn.name in [
            "abi.decode()",
        ]:
            # returns = self.access(op.lvalue)
            # FIXME: lvalue type is None
            pass
        elif fn.name in [
            "type(address)",
            "type()",
        ]:
            self.env.def_ref(op.lvalue, op)
        elif fn.name == "balance(address)":
            if isinstance(op.arguments[0], UserDefinedType):
                returns = self.env.get_balance(op.arguments[0].type.type)
            else:
                addr = self.access(op.arguments[0])
                returns = self.env.get_balance(addr)
        elif fn.name == "code(address)":
            if isinstance(op.arguments[0], UserDefinedType):
                returns = self.env.get_code(op.arguments[0].type.type)
            else:
                addr = self.access(op.arguments[0])
                returns = self.env.get_code(addr)
        elif fn.name == "codehash(address)":
            if isinstance(op.arguments[0], UserDefinedType):
                returns = self.env.get_codehash(op.arguments[0].type.type)
            else:
                addr = self.access(op.arguments[0])
                returns = self.env.get_codehash(addr)
        else:
            print("Not implemented SolidityFunction:", fn.name)
            # raise NotImplementedError(fn.name)

        self.assign(op.lvalue, returns)

    def _transfer_op(self, op: Transfer):
        return

    def _type_conversion_op(self, op: TypeConversion):
        assert not isinstance(op.lvalue, ReferenceVariable)
        arg_val = self.access(op.variable)
        result_val = self.access(op.lvalue)
        from_sort = arg_val.sort()
        to_sort = result_val.sort()
        if isinstance(from_sort, z3.BitVecSortRef) and isinstance(
            to_sort, z3.BitVecSortRef
        ):
            if from_sort.size() > to_sort.size():
                expr = z3.Extract(to_sort.size() - 1, 0, arg_val)
            elif from_sort.size() < to_sort.size():
                signed = is_signed_type(op.variable.type)
                if signed:
                    expr = z3.SignExt(to_sort.size() - from_sort.size(), arg_val)
                else:
                    expr = z3.ZeroExt(to_sort.size() - from_sort.size(), arg_val)
            else:
                expr = arg_val
            self.assign(op.lvalue, expr)
        elif isinstance(from_sort, z3.ArithSortRef) and isinstance(
            to_sort, z3.BitVecSortRef
        ):
            expr = z3.Int2BV(arg_val, to_sort.size())
            self.assign(op.lvalue, expr)
        elif isinstance(from_sort, z3.BitVecSortRef) and isinstance(
            to_sort, z3.ArithRef
        ):
            expr = z3.BV2Int(arg_val)
            self.assign(op.lvalue, expr)
        else:
            # dynamic types, e.g., string, bytes
            self.assign(op.lvalue, arg_val)

    def _unary_op(self, op: Unary):
        arg_val = self.access(op.rvalue)
        assert isinstance(arg_val, (z3.BoolRef, z3.ArithRef, z3.BitVecRef))
        if op.type == UnaryOperationType.BANG:
            val = z3.Not(arg_val)
        elif op.type == UnaryOperationType.TILD:
            val = ~arg_val
        elif op.type == UnaryOperationType.DELETE:
            # over-approximation, do not model delete
            return
        else:
            raise ValueError()
        self.assign(op.lvalue, val)

    def _unpack_op(self, op: Unpack):
        tuple_val = self.access(op.tuple)
        assert isinstance(tuple_val, (list, tuple))
        assert op.index < len(tuple_val)
        self.assign(op.lvalue, tuple_val[op.index])
