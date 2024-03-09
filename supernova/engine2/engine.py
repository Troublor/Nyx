from abc import abstractmethod, ABC

import z3
from slither.core.declarations import Function, FunctionContract, Modifier
from slither.core.expressions import UnaryOperationType
from slither.core.solidity_types import ArrayType, UserDefinedType, ElementaryType
from slither.core.variables.state_variable import StateVariable
from slither.core.variables.variable import Variable
from slither.slithir.operations import (
    Operation,
    Condition,
    Assignment,
    Binary,
    Delete,
    EventCall,
    HighLevelCall,
    LibraryCall,
    Index,
    InitArray,
    InternalCall,
    InternalDynamicCall,
    Length,
    LowLevelCall,
    Member,
    NewArray,
    NewElementaryType,
    NewContract,
    NewStructure,
    Nop,
    Phi,
    Return,
    Send,
    SolidityCall,
    Transfer,
    TypeConversion,
    Unpack,
    Unary,
    BinaryType,
    Call,
)
from slither.slithir.operations.codesize import CodeSize
from slither.slithir.variables import TupleVariable
from web3 import Web3

from engine2.controller import EngineController
from engine2.env import Env
from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.transfer import ResolvedTransfer
from engine2.value import (
    structure_accessor,
    sort_conversion,
    is_signed_type,
    unique_name,
    zero_value,
    type_to_sort,
    sort_value,
)
from engine2.variable import TupleVar, AbsVar, TypeRefVar, Var
from hfg.inter_contract import INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY
from hfg.intra_contract import INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY, TRANSFER_KEY
from lib.assets import is_token_function_call


class SymEngine(ABC):
    def __init__(
        self,
        fn: Function,
        state: State,
        msg_call: MsgCall = None,
        env: Env = None,
        path_conditions: list[z3.BoolRef] = None,
        controller: EngineController = None,
    ):
        self.function = fn
        self.controller = controller if controller else EngineController()
        self.state = state
        self.call = msg_call if msg_call else MsgCall()
        self.env = env if env else Env(self.state, self.call)
        self.raw_path_conditions = (
            path_conditions if path_conditions is not None else list()
        )
        self.raw_revert_conditions: list[z3.BoolRef] = list()
        self.last_application_revert_cond: z3.BoolRef | None = None
        self.raw_constraints: list[z3.BoolRef] = list()
        self.free_values: list[z3.ExprRef] = list()

        """ optimization & approximation """
        self.concretization_values: list[z3.ExprRef] = list()

    @property
    def path_condition(self) -> z3.BoolRef | None:
        limit = self.controller.path_condition_limit
        if limit is None:
            pcs = self.raw_path_conditions
        elif limit <= 0:
            pcs = []
        else:
            pcs = self.raw_path_conditions[-limit:]
        if len(pcs) == 0:
            return None
        elif len(pcs) == 1:
            return pcs[0]
        else:
            return z3.And(*pcs)

    def execute_operation(self, op: Operation):
        self.controller.before_op(op, self)
        try:
            if isinstance(op, Assignment):
                return self._assignment_op(op)
            elif isinstance(op, Binary):
                return self._binary_op(op)
            elif isinstance(op, CodeSize):
                return self._codesize_op(op)
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
            self.controller.after_op(op, self)

    """ operations """

    def _assignment_op(self, op: Assignment):
        if op.rvalue.type is None:
            # workaround for issue crytic/slither#1793
            return
        if op.lvalue.type is None:
            # special case when assigning function selector to a temp var
            op.lvalue.type = op.rvalue.type
        lvar = self.env.use(op.lvalue, op)
        rvar = self.env.use(op.rvalue)
        if isinstance(op.lvalue.type, ArrayType) and not isinstance(
            op.rvalue.type, ArrayType
        ):
            # workaround for issue crytic/slither#1748
            self._do_init_array(lvar, [rvar.val])
        else:
            lvar.assign(rvar.val, self.path_condition)

    def _binary_op(self, op: Binary):
        if op.lvalue.type is None:
            # workaround for issue crytic/slither#1793
            return
        lvar = self.env.use(op.lvalue)
        rvar1 = self.env.use(op.variable_left)
        rvar2 = self.env.use(op.variable_right)
        signed = rvar1.signed or rvar2.signed
        val = self._do_binary(op.type, rvar1.val, rvar2.val, signed)
        lvar.assign(val, self.path_condition)

    def _codesize_op(self, op: CodeSize):
        self.env.use(op.lvalue)

    def _condition_op(self, op: Condition):
        # branching handled in build()
        pass

    def _delete_op(self, op: Delete):
        var = self.env.use(op.variable)
        self._do_delete(var)

    def _event_call_op(self, op: EventCall):
        self._do_collect_transfers(op)

    def _high_level_call_op(self, op: HighLevelCall):
        if isinstance(op.function, StateVariable):
            # access the public variable of another contract
            lvar = self.env.use(op.lvalue)
            rvar = self.env.use(op.function)
            lvar.assign(rvar.val, self.path_condition)
        else:
            self._do_update_balance(op)
            self._do_collect_transfers(op)
            called = self._do_multi_call(op)
            if not called:
                self._do_simulate_call(op)

    def _index_op(self, op: Index):
        self.env.use(op.lvalue, op)

    def _init_array_op(self, op: InitArray):
        lvar = self.env.use(op.lvalue)
        rvars = [self.env.use(v) for v in op.init_values]
        lvar_type = lvar.type
        if len(rvars) == 1 and (
            rvars[0].type == lvar_type
            or isinstance(lvar_type, ArrayType)
            and rvars[0].type == lvar_type.type
        ):
            # workaround for issue crytic/slither#1829
            lvar.assign(rvars[0].val, self.path_condition)
            return
        self._do_init_array(lvar, [r.val for r in rvars])

    def _internal_call_op(self, op: InternalCall):
        self._do_collect_transfers(op)
        self._do_multi_call(op)

    def _internal_dynamic_call_op(self, op: InternalDynamicCall):
        self._do_collect_transfers(op)
        self._do_multi_call(op)

    def _length_op(self, op: Length):
        self.env.use(op.lvalue, op)

    def _library_call_op(self, op: LibraryCall):
        if self._math_library_modeling(op):
            return
        if self._signature_library_modeling(op):
            return
        self._do_collect_transfers(op)
        self._do_multi_call(op)

    def _low_level_call_op(self, op: LowLevelCall):
        self._do_update_balance(op)
        self._do_collect_transfers(op)
        # self.controller.logger.warn(
        #     "Low-level call not handled yet",
        #     op=str(op),
        #     node=str(op.node),
        #     fn=str(self.function),
        #     line=",".join(map(str, op.node.source_mapping.lines)),
        #     file=op.node.source_mapping.filename.absolute,
        # )
        lvar = self.env.use(op.lvalue)
        if isinstance(lvar, TupleVar):
            for val in lvar.val:
                self.free_values.append(val)
        elif isinstance(lvar.val, z3.ExprRef):
            self.free_values.append(lvar.val)

    def _member_op(self, op: Member):
        self.env.use(op.lvalue, op)

    def _new_array_op(self, op: NewArray):
        typ = op.array_type
        for _ in range(op.depth):
            typ = ArrayType(typ, None)
        op.lvalue.type = typ
        self.env.use(op.lvalue)

    def _new_elementary_type_op(self, op: NewElementaryType):
        self.env.use(op.lvalue)

    def _new_contract_op(self, op: NewContract):
        self.env.use(op.lvalue)
        self._do_update_balance(op)
        self._do_collect_transfers(op)

    def _new_structure_op(self, op: NewStructure):
        lvar = self.env.use(op.lvalue)
        args = [self.env.use(v) for v in op.arguments]
        sort = lvar.val.sort()
        assert isinstance(sort, z3.DatatypeSortRef)
        structure = op.structure
        vals = [a.val for a in args]
        for i, decl in enumerate(structure.elems_ordered):
            accessor = structure_accessor(structure, decl.name)
            val = accessor(lvar.val)
            vals[i] = sort_conversion(val.sort(), vals[i], is_signed_type(decl.type))
        constructor = sort.constructor(0)
        val = constructor(*vals)
        lvar.assign(val, self.path_condition)

    def _nop_op(self, op: Nop):
        pass

    def _phi_op(self, op: Phi):
        pass

    def _return_op(self, op: Return):
        if len(op.node.function.returns) == 0:
            # it seems when a function has no return values, return statement is still allowed,
            # and the return variable type is None.
            return
        # assert len(op.values) == len(self.function.returns), op.node.source_mapping
        i = 0
        j = 0
        while i < len(op.values) and j < len(self.function.returns):
            return_values = [self.env.use(rvariable).val for rvariable in op.values]
            if len(return_values) == 1 and isinstance(return_values[0], (tuple, list)):
                # returning tuple variable
                return_values0 = return_values[0]
                assert isinstance(return_values0, (tuple, list))
                return_values = list(return_values0)
            lvariable = self.function.returns[j]
            lvar = self.env.use(lvariable)
            lvar_type = lvariable.type
            val = return_values[i]
            if (
                isinstance(lvar_type, ArrayType)
                and lvar_type.is_fixed_array
                and not isinstance(op.values[i].type, ArrayType)
            ):
                # workaround for issue crytic/slither#1827
                # we merge elements for the fixed array return value
                length = lvar_type.length_value.value
                if isinstance(length, str):
                    length = int(length)
                assert isinstance(length, int)
                val = lvar.val
                assert isinstance(val, z3.ArrayRef)
                for k in range(length):
                    rvar_val = return_values[i + k]
                    val = z3.Store(val, k, rvar_val)
                i += length - 1

            path_condition = self.path_condition
            if isinstance(lvar, Var):
                if not z3.eq(lvar.val, lvar.symbol) and path_condition is None:
                    # the return variable is already assigned
                    path_condition = z3.Bool(unique_name("path_condition"))
            lvar.assign(val, path_condition)
            i += 1
            j += 1

    def _send_op(self, op: Send):
        self._do_update_balance(op)
        self._do_collect_transfers(op)

    def _solidity_call_op(self, op: SolidityCall):
        fn = op.function
        if fn.name == "gasleft()":
            sort = type_to_sort("uint")
            val = z3.Const(unique_name("gasleft"), sort)
            lvar = self.env.use(op.lvalue)
            lvar.assign(val, self.path_condition)
        elif fn.name in [
            "assert(bool)",
            "require(bool)",
            "require(bool,string)",
        ]:
            cond = self.env.use(op.arguments[0])
            cond_val = cond.val
            assert isinstance(cond_val, z3.BoolRef)
            r_cond = z3.Not(cond_val)
            p_cond = self.path_condition
            if p_cond is not None:
                r_cond = z3.If(p_cond, r_cond, z3.BoolVal(False))
            self.raw_revert_conditions.append(r_cond)
            # we don't need to add revert conditions into path conditions
            # since revert conditions will be reflected in the profits directly
        elif fn.name in [
            "revert()",
            "revert(string)",
            "revert ",
        ]:
            cond = self.path_condition
            if cond is None:
                cond = z3.BoolVal(True)
            self.raw_revert_conditions.append(cond)
        elif fn.name in [
            "addmod(uint256,uint256,uint256)",
            "mulmod(uint256,uint256,uint256)",
        ]:
            arg1 = self.env.use(op.arguments[0])
            arg2 = self.env.use(op.arguments[1])
            arg3 = self.env.use(op.arguments[2])
            arg1_expr = arg1.val
            arg2_expr = arg2.val
            arg3_expr = arg3.val
            assert isinstance(arg1_expr, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg2_expr, (z3.ArithRef, z3.BitVecRef))
            assert isinstance(arg3_expr, (z3.ArithRef, z3.BitVecRef))
            if fn.name.startswith("addmod"):
                val = arg1_expr + arg2_expr % arg3_expr
            elif fn.name.startswith("mulmod"):
                val = arg1_expr * arg2_expr % arg3_expr
            else:
                raise NotImplementedError()
            lvar = self.env.use(op.lvalue)
            lvar.assign(val, self.path_condition)
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
        ]:
            lvar = self.env.use(op.lvalue)
            # arg = self.env.use(op.arguments[0]).val
            # val = crypto_hash(op, arg)
            # lvar.assign(val, self.path_condition)
        elif fn.name in [
            "ecrecover(bytes32,uint8,bytes32,bytes32)",
        ]:
            lvar = self.env.use(op.lvalue)
            # args = tuple(self.env.use(arg).val for arg in op.arguments)
            # val = ecrecover(args)
            # lvar.assign(val, self.path_condition)
        elif fn.name in [
            "selfdestruct(address)",
            "suicide(address)",
            "log0(bytes32)",
            "log1(bytes32,bytes32)",
            "log2(bytes32,bytes32)",
            "log3(bytes32,bytes32)",
        ]:
            pass
        elif fn.name == "blockhash":
            self.env.use(op.lvalue)
        elif fn.name == "this.balance()":
            assert isinstance(self.function, FunctionContract)
            c = self.state.load_contract(self.function.contract)
            val = self.state.balance_of(c.val)
            lvar = self.env.use(op.lvalue)
            lvar.assign(val, self.path_condition)
        elif fn.name in [
            "abi.encode()",
            "abi.encodePacked()",
            "abi.encodeWithSelector()",
            "abi.encodeWithSignature()",
            "abi.encodeWithCall()",
        ]:
            lvar = self.env.use(op.lvalue)
            # args = tuple(self.env.use(arg).val for arg in op.arguments)
            # val = abi_encode(fn.name, args)
            # lvar.assign(val, self.path_condition)
        elif fn.name in [
            "bytes.concat()",
            "string.concat()",
        ]:
            self.env.use(op.lvalue)
        elif fn.name in [
            "abi.decode()",
        ]:
            # workaround for issue Crytic/slither#566
            if isinstance(op.lvalue, (TupleVariable)):
                assert isinstance(op.lvalue.type, list)
                for i, typ in enumerate(op.lvalue.type):
                    if isinstance(typ, Variable):
                        # user-defined type reference.
                        # dereference it to get the actual type
                        typ_var = self.env.use(typ)
                        assert isinstance(typ_var, TypeRefVar)
                        op.lvalue.type[i] = typ_var.val
            else:
                if op.lvalue.type is None:
                    typ_var = self.env.use(op.arguments[1])
                    assert isinstance(typ_var, TypeRefVar)
                    op.lvalue.type = typ_var.val
                elif isinstance(op.lvalue.type, Variable):
                    # user-defined type reference.
                    # dereference it to get the actual type
                    typ_var = self.env.use(op.lvalue.type)
                    assert isinstance(typ_var, TypeRefVar)
                    op.lvalue.type = typ_var.val
            assert op.lvalue.type is not None
            self.env.use(op.lvalue)
        elif fn.name in [
            "type(address)",
            "type()",
        ]:
            self.env.use(op.lvalue)
        elif fn.name == "balance(address)":
            lvar = self.env.use(op.lvalue)
            if isinstance(op.arguments[0], UserDefinedType):
                c_var = self.state.load_contract(op.arguments[0].type.type)
                lvar.assign(c_var.balance, self.path_condition)
            else:
                addr = self.env.use(op.arguments[0])
                bal = self.state.balance_of(addr.val)
                lvar.assign(bal, self.path_condition)
        elif fn.name == "code(address)":
            lvar = self.env.use(op.lvalue)
            if isinstance(op.arguments[0], UserDefinedType):
                c_var = self.state.load_contract(op.arguments[0].type.type)
                lvar.assign(c_var.code, self.path_condition)
            else:
                addr = self.env.use(op.arguments[0])
                code = self.state.code_of(addr.val)
                lvar.assign(code, self.path_condition)
        elif fn.name == "codehash(address)":
            lvar = self.env.use(op.lvalue)
            if isinstance(op.arguments[0], UserDefinedType):
                c_var = self.state.load_contract(op.arguments[0].type.type)
                lvar.assign(c_var.codehash, self.path_condition)
            else:
                addr = self.env.use(op.arguments[0])
                codehash = self.state.codehash_of(addr.val)
                lvar.assign(codehash, self.path_condition)
        else:
            # self.controller.logger.warn(
            #     "Not modeled SolidityFunction",
            #     op=str(op),
            #     node=str(op.node),
            #     fn=str(self.function),
            #     line=",".join(map(str, op.node.source_mapping.lines)),
            #     file=op.node.source_mapping.filename.absolute,
            # )
            pass

    def _transfer_op(self, op: Transfer):
        self._do_update_balance(op)
        self._do_collect_transfers(op)

    def _type_conversion_op(self, op: TypeConversion):
        arg = self.env.use(op.variable)
        result = self.env.use(op.lvalue)
        arg_val = arg.val
        result_val = result.val
        to_sort = result_val.sort()
        val = sort_conversion(to_sort, arg_val, result.signed)
        result.assign(val, self.path_condition)

    def _unary_op(self, op: Unary):
        arg = self.env.use(op.rvalue)
        result = self.env.use(op.lvalue)
        self._do_unary(result, op.type, arg.val)

    def _unpack_op(self, op: Unpack):
        tuple_var = self.env.use(op.tuple)
        assert isinstance(tuple_var, TupleVar)
        assert op.index < len(tuple_var.val)
        lvar = self.env.use(op.lvalue)
        lvar.assign(tuple_var.val[op.index], self.path_condition)

    """ common actions """

    def _do_assemble_new_val(
        self, origin_val: z3.ExprRef, val: z3.ExprRef, cond: z3.BoolRef = None
    ):
        if cond is None:
            return val
        else:
            return z3.If(cond, val, origin_val)

    def _do_binary(
        self,
        op_type: BinaryType,
        arg1: z3.ExprRef,
        arg2: z3.ExprRef,
        signed: bool,
    ) -> z3.ExprRef:
        # implicit type conversion
        # if isinstance(arg1, z3.ArithRef) and isinstance(arg2, z3.BitVecRef):
        #     # comparing int and address
        #     arg2 = z3.BV2Int(arg2)
        # elif isinstance(arg1, z3.ArithRef) and isinstance(arg2, z3.RatNumRef):
        #     # comparing int and real number
        #     arg2 = z3.ToInt(arg2)

        arg1, arg2 = self._do_regularize_binary_operands(op_type, arg1, arg2, signed)
        val = None

        # assert not isinstance(arg1, z3.ArithRef)
        # assert not isinstance(arg2, z3.ArithRef)
        # arg2 = sort_conversion(arg1.sort(), arg2, signed)

        if isinstance(arg1, (z3.BitVecRef, z3.ArithRef)) and isinstance(
            arg2, (z3.ArithRef, z3.BitVecRef)
        ):
            # arithmetic operation
            if op_type == BinaryType.POWER:
                if (
                    self.controller.concretize_non_linear_expression
                    and not z3.is_bv_value(arg2)
                    and not z3.is_int_value(arg2)
                    and not z3.is_rational_value(arg2)
                ):
                    arg2 = sort_value(1, arg2.sort())
                if z3.is_int_value(arg2) or z3.is_rational_value(arg2):
                    val = arg1**arg2
                else:
                    val = z3.Const(unique_name(), arg1.sort())
            elif op_type == BinaryType.MULTIPLICATION:
                if (
                    self.controller.concretize_non_linear_expression
                    and not z3.is_bv_value(arg2)
                    and not z3.is_int_value(arg2)
                    and not z3.is_rational_value(arg2)
                ):
                    arg2 = sort_value(1, arg2.sort())
                val = arg1 * arg2
                if isinstance(arg1, z3.BitVecRef):
                    self.raw_constraints.append(z3.BVMulNoOverflow(arg1, arg2, signed))
            elif op_type == BinaryType.DIVISION:
                if (
                    self.controller.concretize_non_linear_expression
                    and not z3.is_int_value(arg2)
                    and not z3.is_rational_value(arg2)
                    and not z3.is_bv_value(arg2)
                ):
                    arg2 = sort_value(1, arg2.sort())
                if isinstance(arg1, z3.BitVecRef):
                    if not z3.is_bv_value(arg2):
                        arg2 = sort_value(1, arg1.sort())
                    if signed:
                        val = arg1 / arg2
                        self.raw_constraints.append(z3.BVSDivNoOverflow(arg1, arg2))
                    else:
                        val = z3.UDiv(arg1, arg2)
                else:
                    val = arg1 / arg2
            elif op_type == BinaryType.MODULO:
                if (
                    self.controller.concretize_non_linear_expression
                    and not z3.is_int_value(arg2)
                    and not z3.is_rational_value(arg2)
                    and not z3.is_bv_value(arg2)
                ):
                    arg2 = sort_value(1, arg2.sort())
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        val = z3.SRem(arg1, arg2)
                    else:
                        val = z3.URem(arg1, arg2)
                elif arg1.sort().is_int() and arg1.sort().is_int():
                    val = arg1 % arg2
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    val = z3.ToReal(z3.ToInt(arg1) % z3.ToInt(arg2))
                else:
                    raise ValueError(
                        "Unsupported modulo operation", arg1.sort(), arg2.sort()
                    )
            elif op_type == BinaryType.ADDITION:
                val = arg1 + arg2
                if isinstance(arg1, z3.BitVecRef):
                    self.raw_constraints.append(z3.BVAddNoOverflow(arg1, arg2, signed))
                    if signed:
                        self.raw_constraints.append(z3.BVAddNoUnderflow(arg1, arg2))
            elif op_type == BinaryType.SUBTRACTION:
                val = arg1 - arg2
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        self.raw_constraints.append(z3.BVSubNoOverflow(arg1, arg2))
                #     self.raw_constraints.append(z3.BVSubNoUnderflow(arg1, arg2, signed))
            elif op_type == BinaryType.LESS:
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        val = arg1 < arg2
                    else:
                        val = z3.ULT(arg1, arg2)
                else:
                    val = arg1 < arg2
            elif op_type == BinaryType.GREATER:
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        val = arg1 > arg2
                    else:
                        val = z3.UGT(arg1, arg2)
                else:
                    val = arg1 > arg2
            elif op_type == BinaryType.LESS_EQUAL:
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        val = arg1 <= arg2
                    else:
                        val = z3.ULE(arg1, arg2)
                else:
                    val = arg1 <= arg2
            elif op_type == BinaryType.GREATER_EQUAL:
                if isinstance(arg1, z3.BitVecRef):
                    if signed:
                        val = arg1 >= arg2
                    else:
                        val = z3.UGE(arg1, arg2)
                else:
                    val = arg1 >= arg2

        if isinstance(arg1, (z3.ArithRef, z3.BitVecRef)) and isinstance(
            arg2, (z3.ArithRef, z3.BitVecRef)
        ):
            # bitwise operation
            if op_type == BinaryType.LEFT_SHIFT:
                if isinstance(arg1, z3.BitVecRef):
                    if z3.is_bv_value(arg2):
                        typ = ElementaryType("uint")
                        sort = type_to_sort("uint")
                        assert isinstance(sort, z3.BitVecSortRef)
                        scale = typ.size // sort.size()
                        val = arg1 << (arg2 / scale)
                    else:
                        val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_int() and arg2.sort().is_int():
                    # val = arg1 << arg2
                    val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    # val = z3.ToReal(z3.ToInt(arg1) << z3.ToInt(arg2))
                    val = z3.Const(unique_name(), arg1.sort())
                else:
                    raise ValueError(
                        "Unsupported left shift operation", arg1.sort(), arg2.sort()
                    )
            elif op_type == BinaryType.RIGHT_SHIFT:
                if isinstance(arg1, z3.BitVecRef):
                    if z3.is_bv_value(arg2):
                        typ = ElementaryType("uint")
                        sort = type_to_sort("uint")
                        assert isinstance(sort, z3.BitVecSortRef)
                        scale = typ.size // sort.size()
                        val = arg1 >> (arg2 / scale)
                    else:
                        val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_int() and arg2.sort().is_int():
                    # val = arg1 >> arg2
                    val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    # val = z3.ToReal(z3.ToInt(arg1) >> z3.ToInt(arg2))
                    val = z3.Const(unique_name(), arg1.sort())
                else:
                    raise ValueError(
                        "Unsupported right shift operation", arg1.sort(), arg2.sort()
                    )
            elif op_type == BinaryType.AND:
                if isinstance(arg1, z3.BitVecRef) and isinstance(arg2, z3.BitVecRef):
                    val = arg1 & arg2
                elif arg1.sort().is_int() and arg2.sort().is_int():
                    # val = arg1 & arg2
                    val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    # val = z3.ToReal(z3.ToInt(arg1) & z3.ToInt(arg2))
                    val = z3.Const(unique_name(), arg1.sort())
                else:
                    raise ValueError(
                        "Unsupported bitwise and operation", arg1.sort(), arg2.sort()
                    )
            elif op_type == BinaryType.CARET:
                if isinstance(arg1, z3.BitVecRef) and isinstance(arg2, z3.BitVecRef):
                    val = arg1 ^ arg2
                elif arg1.sort().is_int() and arg2.sort().is_int():
                    # val = arg1 ^ arg2
                    val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    # val = z3.ToReal(z3.ToInt(arg1) ^ z3.ToInt(arg2))
                    val = z3.Const(unique_name(), arg1.sort())
                else:
                    raise ValueError(
                        "Unsupported bitwise xor operation", arg1.sort(), arg2.sort()
                    )
            elif op_type == BinaryType.OR:
                if isinstance(arg1, z3.BitVecRef) and isinstance(arg2, z3.BitVecRef):
                    val = arg1 | arg2
                elif arg1.sort().is_int() and arg2.sort().is_int():
                    # val = arg1 | arg2
                    val = z3.Const(unique_name(), arg1.sort())
                elif arg1.sort().is_real() and arg2.sort().is_real():
                    # val = z3.ToReal(z3.ToInt(arg1) | z3.ToInt(arg2))
                    val = z3.Const(unique_name(), arg1.sort())
                else:
                    raise ValueError(
                        "Unsupported bitwise xor operation", arg1.sort(), arg2.sort()
                    )

        if isinstance(arg1, z3.BoolRef) and isinstance(arg2, z3.BoolRef):
            # boolean operation
            if op_type == BinaryType.ANDAND:
                val = z3.And(arg1, arg2)
            elif op_type == BinaryType.OROR:
                val = z3.Or(arg1, arg2)

        if isinstance(arg1, z3.ExprRef) and isinstance(arg2, z3.ExprRef):
            # equality operation
            if op_type == BinaryType.EQUAL:
                val = arg1 == arg2
            elif op_type == BinaryType.NOT_EQUAL:
                val = arg1 != arg2

        assert val is not None, (op_type, arg1.sort(), arg2.sort())
        return val

    @abstractmethod
    def _do_call(
        self,
        result: AbsVar | None,
        fn: Function,
        state: State,
        msg_call: MsgCall,
        args: tuple[z3.ExprRef, ...],
    ):
        pass

    def _do_collect_transfers(self, op: Operation):
        asset_transfers = op.context.get(TRANSFER_KEY, [])
        for asset_transfer in asset_transfers:
            _transfer = ResolvedTransfer(
                self.env,
                asset_transfer,
                self.path_condition,
            )
            self.controller.on_transfer(_transfer, self)
            # token contract modeling
            if isinstance(op, HighLevelCall):
                self.env.simulate_token_transfer(op, _transfer)

    def _do_delete(self, var: AbsVar):
        zero = zero_value(var.val.sort())
        var.assign(zero, self.path_condition)

    def _do_init_array(self, arr: AbsVar, values: list[z3.ExprRef]):
        assert isinstance(arr.val.sort(), z3.ArraySortRef)
        for i, v in enumerate(values):
            arr.assign(z3.Store(arr.val, i, v), self.path_condition)

    def _do_multi_call(
        self,
        op: HighLevelCall | LibraryCall | InternalCall | InternalDynamicCall,
    ) -> bool:  # return True if a call is performed
        call_edge_key = (
            INTRA_PROCEDURAL_EXTERNAL_CALL_EDGE_KEY
            if self._is_external_call(op)
            else INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY
        )
        callees: list[Function] = [
            callee
            for callee in op.context.get(call_edge_key, [])
            if not isinstance(callee, Modifier)
        ]

        # execute the modifiers
        modifiers: list[Modifier] = [
            callee
            for callee in op.context.get(call_edge_key, [])
            if isinstance(callee, Modifier) and callee.name != "nonReentrant"
        ]
        for _modifier in modifiers:
            self._do_register_modifier(_modifier)

        if len(callees) == 0 or is_token_function_call(op):
            # don't step into unimplemented functions and token contract functions
            # assume the unknown external call always success
            self.last_application_revert_cond = z3.BoolVal(False)
            if op.lvalue is not None:
                lvar = self.env.use(op.lvalue)
                lvar.free()
                # save the free variables for substitute in apply function
                if isinstance(lvar, TupleVar):
                    self.free_values.extend(lvar.val)
                else:
                    self.free_values.append(lvar.val)
            return False

        lvar = self.env.use(op.lvalue) if op.lvalue else None
        zero = zero_value(type_to_sort("uint"))
        if self._is_external_call(op):
            value = self.env.use(op.call_value).val if op.call_value else zero
        else:
            value = zero

        sender = (
            self.call.this.val if self._is_external_call(op) else self.call.sender.val
        )
        callee_addrs = []
        for callee in callees:
            if isinstance(callee, FunctionContract):
                c_var = self.state.load_contract(callee.contract)
                callee_addrs.append(c_var.val)
            else:
                addr_val = z3.Const(unique_name("addr"), type_to_sort("address"))
                callee_addrs.append(addr_val)
        msg_calls = [
            self.call.external_call(sender, value, callee_addr)
            for callee_addr in callee_addrs
        ]

        args = tuple(self.env.use(arg).val for arg in op.arguments)

        if len(callees) == 1:
            self._do_call(lvar, callees[0], self.state, msg_calls[0], args)
        else:
            for i, callee in enumerate(callees):
                self.raw_path_conditions.append(z3.Bool(unique_name("multicall")))
                self._do_call(lvar, callee, self.state, msg_calls[i], args)
                self.raw_path_conditions.pop()
        return True

    @abstractmethod
    def _do_register_modifier(self, modifier: Modifier):
        pass

    def _do_regularize_binary_operands(
        self,
        typ: BinaryType,
        arg1: z3.ExprRef,
        arg2: z3.ExprRef,
        signed: bool,
    ) -> tuple[z3.ExprRef, z3.ExprRef]:
        if typ in [
            BinaryType.POWER,
            BinaryType.MULTIPLICATION,
            BinaryType.DIVISION,
            BinaryType.MODULO,
            BinaryType.ADDITION,
            BinaryType.SUBTRACTION,
            BinaryType.LESS,
            BinaryType.GREATER,
            BinaryType.LESS_EQUAL,
            BinaryType.GREATER_EQUAL,
        ]:
            if isinstance(arg1, z3.BitVecRef) or isinstance(arg2, z3.BitVecRef):
                # convert to bitvector
                size = 0
                if isinstance(arg1.sort(), z3.BitVecSortRef):
                    size = arg1.sort().size() if arg1.sort().size() > size else size
                if isinstance(arg2.sort(), z3.BitVecSortRef):
                    size = arg2.sort().size() if arg2.sort().size() > size else size
                if size == 0:
                    uint_sort = type_to_sort(ElementaryType("uint"))
                    assert isinstance(uint_sort, z3.BitVecSortRef)
                    size = uint_sort.size()
                arg1 = sort_conversion(z3.BitVecSort(size), arg1, signed)
                arg2 = sort_conversion(z3.BitVecSort(size), arg2, signed)
            elif isinstance(arg1, z3.ArithRef) or isinstance(arg2, z3.ArithRef):
                # arith
                to_real = (isinstance(arg1, z3.ArithRef) and arg1.sort().is_real()) or (
                    isinstance(arg2, z3.ArithRef) and arg2.sort().is_real()
                )
                if to_real:
                    arg1 = sort_conversion(z3.RealSort(), arg1, signed)
                    arg2 = sort_conversion(z3.RealSort(), arg2, signed)
                else:
                    arg1 = sort_conversion(z3.IntSort(), arg1, signed)
                    arg2 = sort_conversion(z3.IntSort(), arg2, signed)
            else:
                raise ValueError(
                    "unsupported binary operation", arg1.sort(), arg2.sort()
                )
        elif typ in [
            BinaryType.LEFT_SHIFT,
            BinaryType.RIGHT_SHIFT,
            BinaryType.AND,
            BinaryType.CARET,
            BinaryType.OR,
        ]:
            if isinstance(arg1, z3.BitVecRef) or isinstance(arg2, z3.BitVecRef):
                # convert to bitvector
                size = 0
                if isinstance(arg1.sort(), z3.BitVecSortRef):
                    size = arg1.sort().size() if arg1.sort().size() > size else size
                if isinstance(arg2.sort(), z3.BitVecSortRef):
                    size = arg2.sort().size() if arg2.sort().size() > size else size
                if size == 0:
                    uint_sort = type_to_sort(ElementaryType("uint"))
                    assert isinstance(uint_sort, z3.BitVecSortRef)
                    size = uint_sort.size()
                arg1 = sort_conversion(z3.BitVecSort(size), arg1, signed)
                arg2 = sort_conversion(z3.BitVecSort(size), arg2, signed)
            elif isinstance(arg1, z3.ArithRef) or isinstance(arg2, z3.ArithRef):
                # arith
                to_real = (isinstance(arg1, z3.ArithRef) and arg1.sort().is_real()) or (
                    isinstance(arg2, z3.ArithRef) and arg2.sort().is_real()
                )
                if to_real:
                    arg1 = sort_conversion(z3.RealSort(), arg1, signed)
                    arg2 = sort_conversion(z3.RealSort(), arg2, signed)
                else:
                    arg1 = sort_conversion(z3.IntSort(), arg1, signed)
                    arg2 = sort_conversion(z3.IntSort(), arg2, signed)
            else:
                raise ValueError(
                    "unsupported binary operation", arg1.sort(), arg2.sort()
                )
        elif typ in [
            BinaryType.ANDAND,
            BinaryType.OROR,
        ]:
            # convert to boolean
            arg1 = sort_conversion(z3.BoolSort(), arg1, signed)
            arg2 = sort_conversion(z3.BoolSort(), arg2, signed)
        elif typ in [
            BinaryType.EQUAL,
            BinaryType.NOT_EQUAL,
        ]:
            if isinstance(arg1, z3.BitVecRef) or isinstance(arg2, z3.BitVecRef):
                size = 0
                if isinstance(arg1.sort(), z3.BitVecSortRef):
                    size = arg1.sort().size() if arg1.sort().size() > size else size
                if isinstance(arg2.sort(), z3.BitVecSortRef):
                    size = arg2.sort().size() if arg2.sort().size() > size else size
                if size > 0:
                    arg1 = sort_conversion(z3.BitVecSort(size), arg1, signed)
                    arg2 = sort_conversion(z3.BitVecSort(size), arg2, signed)

        return arg1, arg2

    def _do_simulate_call(self, call: HighLevelCall):
        if call.function.solidity_signature == "balanceOf(address)":
            arg0_var = self.env.use(call.arguments[0])
            ret = self.env.simulate_token_balance_of(call, arg0_var.val)
        elif call.function.solidity_signature == "ownerOf(uint256)":
            arg0_var = self.env.use(call.arguments[0])
            ret = self.env.simulate_token_owner_of(call, arg0_var.val)
        elif call.function.solidity_signature == "balanceOf(address,uint256)":
            arg0_var = self.env.use(call.arguments[0])
            arg1_var = self.env.use(call.arguments[1])
            ret = self.env.simulate_token_balance_of(call, arg0_var.val, arg1_var.val)
        elif call.function.solidity_signature == "owner()":
            ret = self.env.simulate_owner(call)
        elif (
            call.function.solidity_signature
            == "onERC721Received(address,address,uint256,bytes)"
        ):
            sig_hash = Web3.keccak(text=call.function.solidity_signature)[:4]
            ret = sort_value(
                int.from_bytes(sig_hash, byteorder="big"), type_to_sort("bytes4")
            )
        else:
            return
        lval = self.env.use(call.lvalue)
        assert not isinstance(lval, TupleVar)
        lval.assign(ret, self.path_condition)

    def _do_update_balance(self, op: Call):
        value = None
        receiver = None
        if hasattr(op, "call_value"):
            call_value = getattr(op, "call_value")
            if call_value is not None:
                rvar = self.env.use(call_value)
                value = rvar.val
        if hasattr(op, "destination"):
            destination = getattr(op, "destination")
            if destination is not None:
                rvar = self.env.use(destination)
                receiver = rvar.val

        if value is None or receiver is None:
            return
        assert isinstance(value, (z3.ArithRef, z3.BitVecRef))
        self.state.add_balance(receiver, value)
        zero = zero_value(type_to_sort("uint"))
        self.state.add_balance(self.call.this.val, zero - value)

    def _do_unary(self, result: AbsVar, op_type: UnaryOperationType, arg: z3.ExprRef):
        assert isinstance(arg, (z3.BoolRef, z3.ArithRef, z3.BitVecRef))
        if op_type == UnaryOperationType.BANG:
            if not isinstance(arg, z3.BoolRef):
                arg = sort_conversion(z3.BoolSort(), arg, False)
            val = z3.Not(arg)
            result.assign(val, self.path_condition)
        elif op_type == UnaryOperationType.TILD:
            if isinstance(arg, z3.BitVecRef):
                val = ~arg
            else:
                val = z3.Const(unique_name("tilde"), arg.sort())
            result.assign(val, self.path_condition)
        elif op_type == UnaryOperationType.DELETE:
            self._do_delete(result)
        else:
            raise NotImplementedError(f"unary operation {op_type} not implemented")

    def _is_external_call(self, op: Call) -> bool:
        return isinstance(op, HighLevelCall) and not isinstance(op, LibraryCall)

    def _math_library_modeling(
        self,
        op: LibraryCall,
    ) -> bool:
        env = self.env
        var1 = env.use(op.arguments[0]) if len(op.arguments) >= 1 else None
        var2 = env.use(op.arguments[1]) if len(op.arguments) >= 2 else None
        var3 = env.use(op.arguments[2]) if len(op.arguments) >= 3 else None
        arg1 = var1.val if var1 is not None else None
        arg2 = var2.val if var2 is not None else None
        arg3 = var3.val if var3 is not None else None
        signed = False
        signed = signed or (var1 is not None and var1.signed)
        signed = signed or (var2 is not None and var2.signed)
        signed = signed or (var3 is not None and var3.signed)
        if op.lvalue is None:
            return False
        lvar = env.use(op.lvalue)
        if isinstance(lvar, TupleVar):
            return False
        if (
            op.function.name in ["add", "tryAdd", "addDelta"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.ADDITION, arg1, arg2, signed)
        elif (
            op.function.name in ["sub", "trySub"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.SUBTRACTION, arg1, arg2, signed)
        elif (
            op.function.name in ["mul", "tryMul"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.MULTIPLICATION, arg1, arg2, signed)
        elif (
            op.function.name in ["div", "sdiv", "tryDiv", "divRoundingUp"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.DIVISION, arg1, arg2, signed)
        elif (
            op.function.name in ["mod", "smod", "tryMod"]
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.MODULO, arg1, arg2, signed)
        elif (
            op.function.name == "exp"
            and len(op.function.parameters) >= 2
            and len(op.function.returns) == 1
        ):
            val = self._do_binary(BinaryType.POWER, arg1, arg2, signed)
        elif (
            op.function.name == "addmod"
            and len(op.function.parameters) >= 3
            and len(op.function.returns) == 1
        ):
            tmp = self._do_binary(BinaryType.ADDITION, arg1, arg2, signed)
            val = self._do_binary(BinaryType.MODULO, tmp, arg3, signed)
        elif (
            op.function.name == "mulmod"
            and len(op.function.parameters) >= 3
            and len(op.function.returns) == 1
        ):
            tmp = self._do_binary(BinaryType.MULTIPLICATION, arg1, arg2, signed)
            val = self._do_binary(BinaryType.MODULO, tmp, arg3, signed)
        elif (
            op.function.name == "sqrt"
            or op.function.name.startswith("getSqrt")
            and len(op.function.parameters) >= 1
            and len(op.function.returns) == 1
        ):
            if isinstance(arg1, z3.ArithRef) and arg1.sort().is_real():
                val = z3.Sqrt(arg1)
            else:
                val = z3.Const(unique_name("sqrt"), lvar.val.sort())
        elif (
            op.function.name in ["mulDiv", "mulDivRoundingUp"]
            and len(op.function.parameters) >= 3
            and len(op.function.returns) == 1
        ):
            tmp = self._do_binary(BinaryType.MULTIPLICATION, arg1, arg2, signed)
            val = self._do_binary(BinaryType.DIVISION, tmp, arg3, signed)
        else:
            return False

        lvar.assign(val, self.path_condition)
        return True

    def _signature_library_modeling(self, op: LibraryCall) -> bool:
        env = self.env
        if op.lvalue is None:
            return False
        lvar = env.use(op.lvalue)
        if isinstance(lvar, TupleVar):
            return False
        if (
            op.function.name == "isValidSigfature"
            and len(op.function.parameters) == 2
            and len(op.function.returns) == 1
        ):
            val = z3.BoolVal(True)
            lvar.assign(val, self.path_condition)
            return True
        return False
