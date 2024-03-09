import copy
from enum import Enum
from typing import TypedDict, Set, Dict, Tuple, Optional, Union, List

from slither.analyses.data_dependency.data_dependency import (
    KEY_SSA,
)
from slither.core.cfg.node import Node
from slither.core.declarations import Function
from slither.core.solidity_types import ArrayType
from slither.core.variables.variable import Variable
from slither.slithir.operations import (
    Operation,
    Condition,
    HighLevelCall,
    Assignment,
    Unpack,
    OperationWithLValue,
    InternalCall,
    InternalDynamicCall,
    LibraryCall,
    LowLevelCall,
    SolidityCall,
    EventCall,
    Transfer,
    Send,
    Return,
    Phi,
)
from slither.slithir.variables import (
    StateIRVariable,
    ReferenceVariableSSA,
    TupleVariableSSA,
    LocalIRVariable,
)
from slither.slithir.variables.variable import SlithIRVariable

from lib.assets import resolve_asset_transfer_op

# In the context of a function, this is used to store the sources of each taint sink variable.
# Taint source could be:
# 1. function parameters
# 2. state variable
# 3. external call return values
# Taint sink could be:
# 1. state variable assignment
# 2. return value assignment
# 3. path condition
# 4. external/internal call arguments
# 5. profit making locations

"""
NOTE: We use SSA all the time.
"""


def merge_sources(
    dest: "IntraProceduralDataFlowSource", src: "IntraProceduralDataFlowSource"
):
    dest["parameters"] |= src["parameters"]
    dest["states"] |= src["states"]
    dest["call_returns"] |= src["call_returns"]


class IntraProceduralDataFlowSource(TypedDict):
    # set of parameter indices (starting from 1, 0 is reserved for function selector (maybe useful in the future)
    parameters: Set[int]
    # set of state variable read operations. field-insensitive
    states: Set[StateIRVariable]
    # set of (call operation, return index) tuples (starting from 1, 0 is reserved for call success)
    call_returns: Set[Tuple[Operation, int]]


class SinkKind(Enum):
    STATE = "state"
    RETURN = "return"
    CONDITION = "condition"
    CALL_ARG = "call"
    PROFIT = "profit"


class IntraProceduralDataFlowSinkSummary(object):
    """
    To be attached to the context of an operation
    """

    def __init__(self, op: Operation, kind: SinkKind):
        self.op = op
        self.kind = kind
        self.sources: IntraProceduralDataFlowSource = {
            "parameters": set(),
            "states": set(),
            "call_returns": set(),
        }

    @property
    def node(self):
        return self.op.node

    @property
    def function(self):
        return self.node.function

    def _resolve_sources(self, sink_var: Union[SlithIRVariable, ReferenceVariableSSA]):
        SSA_VAR_DEF_MAP_KEY = "ssa_var_def_map"
        if SSA_VAR_DEF_MAP_KEY not in self.function.context:
            self.function.context[SSA_VAR_DEF_MAP_KEY] = {
                op.lvalue: op
                for op in self.function.slithir_ssa_operations
                if isinstance(op, OperationWithLValue)
            }

        # if sink var is itself a source
        self.__resolve_sources(self.function.context[SSA_VAR_DEF_MAP_KEY], sink_var)

        if sink_var in self.function.context[KEY_SSA]:
            for dep in self.function.context[KEY_SSA][sink_var]:
                self.__resolve_sources(self.function.context[SSA_VAR_DEF_MAP_KEY], dep)

    def __resolve_sources(
        self,
        ssa_var_def_map: Dict[Variable, OperationWithLValue],
        dep: Variable,
    ):
        fn = self.function
        # source is function parameter
        if isinstance(dep, LocalIRVariable):
            try:
                if dep.index == 0:
                    param_idx = fn.parameters_ssa.index(dep) + 1
                    self.sources["parameters"].add(param_idx)
                    return
                elif dep.index == 1:
                    # FIXME: this is a workaround for bug: https://github.com/crytic/slither/issues/1683
                    # We check if this LocalIRVariable's index is 1,
                    # and if it is, we check if it is a function parameter.
                    param_idx = fn.parameters.index(dep.non_ssa_version) + 1
                    self.sources["parameters"].add(param_idx)
                    return
                else:
                    pass
            except ValueError:
                pass

        # source is state variable read
        # Do not dereference here, since we want to have some field sensitive analysis later.
        if isinstance(dep, StateIRVariable):
            self.sources["states"].add(dep)  # TODO
            return
        elif isinstance(dep, ReferenceVariableSSA):
            dep = dep.points_to_origin
            if isinstance(dep, StateIRVariable):
                self.sources["states"].add(dep)
                return
            return

        def is_call(op: Operation) -> bool:
            # TODO: handle low level external call, assembly external call
            return isinstance(
                op, (HighLevelCall, InternalCall, InternalDynamicCall, LibraryCall)
            )

        # source is external call return value
        if dep in ssa_var_def_map:
            def_op = ssa_var_def_map[dep]
            if not isinstance(dep, TupleVariableSSA) and is_call(def_op):
                self.sources["call_returns"].add((def_op, 1))
                return
            if isinstance(def_op, Unpack):
                tuple_def_op = ssa_var_def_map[def_op.tuple]
                if is_call(tuple_def_op):
                    self.sources["call_returns"].add((tuple_def_op, def_op.index + 1))
                    # TODO: handle nested unpack tuples and structs.
                    return
        return


class StateSinkSummary(IntraProceduralDataFlowSinkSummary):
    def __init__(
        self,
        store: Operation,
        state: StateIRVariable,
        ref: Optional[ReferenceVariableSSA] = None,
    ):
        super().__init__(store, SinkKind.STATE)
        self.store = store
        self.state = state
        self.ref = ref
        self._resolve_sources(state)
        if ref:
            self._resolve_sources(ref)

        # remove redundant self data flow
        self.sources["states"].discard(self.state)

    def __eq__(self, other):
        return self.store == other.store and self.state == other.state

    def __hash__(self):
        return hash(("StateSinkSummary", self.store, self.state))


class ReturnSinkSummary(IntraProceduralDataFlowSinkSummary):
    def __init__(self, op: Operation, var: SlithIRVariable, idx: int):
        super().__init__(op, SinkKind.RETURN)
        self.var = var
        self.idx = idx
        self._resolve_sources(var)

    def __eq__(self, other):
        return self.op == other.op and self.var == other.var and self.idx == other.idx

    def __hash__(self):
        return hash(("ReturnSinkSummary", self.op, self.var, self.idx))


class ConditionSinkSummary(IntraProceduralDataFlowSinkSummary):
    def __init__(self, op: Operation, var: SlithIRVariable):
        super().__init__(op, SinkKind.CONDITION)
        self.var = var
        self._resolve_sources(var)

    def __eq__(self, other):
        return self.op == other.op and self.var == other.var

    def __hash__(self):
        return hash(("ConditionSinkSummary", self.op, self.var))


class CallArgSinkSummary(IntraProceduralDataFlowSinkSummary):
    def __init__(self, call: Operation, arg: SlithIRVariable, idx: int):
        super().__init__(call, SinkKind.CALL_ARG)
        self.call = call
        self.arg = arg
        self.idx = idx
        self._resolve_sources(arg)

    def __eq__(self, other):
        return (
            self.call == other.call and self.arg == other.arg and self.idx == other.idx
        )

    def __hash__(self):
        return hash(("CallArgSinkSummary", self.call, self.arg, self.idx))


class ProfitSinkSummary(IntraProceduralDataFlowSinkSummary):
    def __init__(self, op: Operation, var: SlithIRVariable):
        super().__init__(op, SinkKind.PROFIT)
        self.var = var
        self._resolve_sources(var)

    def __eq__(self, other):
        return self.op == other.op and self.var == other.var

    def __hash__(self):
        hash(("ProfitSinkSummary", self.op, self.var))


# operation level key
DATA_FLOW_SINK_KEY = "data_flow_sink"


def summarize_intra_procedural_data_flow(fn: Function):
    """
    NOTE: this function assumes that the function has already been summarized for asset transfers
            using `summarize_intra_procedural_profits`.
    Summarize the intra_procedural data flow:
    - Source:
        - Function parameters
        - State variable
        - External call return values
    - Sink:
        - State variable
        - Function return values
        - Path conditions
        - External/internal call arguments
        - Profit locations
    :param fn:
    :return:
    """
    patch_named_return_variables(fn)

    for op in fn.slithir_ssa_operations:
        op.context[DATA_FLOW_SINK_KEY] = []

    def summarize_state_sink(_op: Operation):
        if isinstance(_op, OperationWithLValue) and not isinstance(_op, Phi):
            var = None
            ref = None
            if isinstance(_op.lvalue, StateIRVariable):
                var = _op.lvalue
            elif isinstance(_op.lvalue, ReferenceVariableSSA):
                ref = _op.lvalue
                var = _op.lvalue.points_to_origin
                if not isinstance(var, StateIRVariable):
                    var = None
            if var is not None:
                _op.context[DATA_FLOW_SINK_KEY].append(StateSinkSummary(_op, var, ref))

    def summarize_return_sink(_op: Operation):
        if len(_op.node.function.returns) == 0:
            # it seems at solc <= 0.6, return statement is allowed in a function without return values
            return
        if len(fn.returns_ssa) == 0:
            # No named return variable
            if isinstance(_op, Return):
                i = 0
                j = 0
                while i < len(_op.values) and j < len(fn.returns):
                    ret = _op.values[i]
                    return_var = fn.returns[j]
                    return_var_type = return_var.type
                    sink_summary = ReturnSinkSummary(_op, ret, i + 1)
                    if (
                        isinstance(return_var_type, ArrayType)
                        and return_var_type.is_fixed_array
                        and not isinstance(ret.type, ArrayType)
                    ):
                        # workaround for issue crytic/slither#1827
                        # we merge elements for the fixed array return value
                        length = return_var_type.length_value.value
                        if isinstance(length, str):
                            length = int(length)
                        assert isinstance(length, int)
                        for _ in range(length - 1):
                            i += 1
                            ret = _op.values[i]
                            s = ReturnSinkSummary(_op, ret, sink_summary.idx)
                            merge_sources(sink_summary.sources, s.sources)

                    _op.context[DATA_FLOW_SINK_KEY].append(sink_summary)
                    i += 1
                    j += 1
        else:
            # Has named return variable
            if NAMED_RETURN_LAST_ASSIGN_KEY in _op.context:
                # FIXME: workaround for issue crytic/slither#1827
                for i, ret in _op.context[NAMED_RETURN_LAST_ASSIGN_KEY]:
                    _op.context[DATA_FLOW_SINK_KEY].append(
                        ReturnSinkSummary(_op, ret, i + 1)
                    )

    def summarize_condition_sink(_op: Operation):
        if isinstance(_op, Condition):
            _op.context[DATA_FLOW_SINK_KEY].append(ConditionSinkSummary(_op, _op.value))
        elif isinstance(_op, SolidityCall) and (
            "require" in _op.function.name or "assert" in _op.function.name
        ):
            _op.context[DATA_FLOW_SINK_KEY].append(
                ConditionSinkSummary(_op, _op.arguments[0])
            )

    def summarize_call_arg_sink(_op: Operation):
        if isinstance(
            _op,
            (
                HighLevelCall,
                InternalCall,
                LibraryCall,
                InternalDynamicCall,
            ),
        ):
            for i, arg in enumerate(_op.arguments):
                _op.context[DATA_FLOW_SINK_KEY].append(
                    CallArgSinkSummary(_op, arg, i + 1)
                )
        elif isinstance(
            _op,
            (
                LowLevelCall,
                SolidityCall,
            ),
        ):
            for use in _op.read:
                _op.context[DATA_FLOW_SINK_KEY].append(CallArgSinkSummary(_op, use, -1))

    def summarize_profit_sink(_op: Operation):
        if isinstance(
            _op,
            (
                EventCall,
                Transfer,
                Send,
                HighLevelCall,
                LowLevelCall,
                SolidityCall,
            ),
        ):
            for use in _op.read:
                _op.context[DATA_FLOW_SINK_KEY].append(ProfitSinkSummary(_op, use))

    for op in fn.slithir_ssa_operations:
        summarize_state_sink(op)
        summarize_return_sink(op)
        summarize_condition_sink(op)
        summarize_call_arg_sink(op)
        summarize_profit_sink(op)

    # function-level return sink summary


# operation level key
NAMED_RETURN_LAST_ASSIGN_KEY = "named_return_last_assign"


def patch_named_return_variables(fn: Function):
    """
    Analyze the data dependency of the name return variable of a function.
    :param fn:
    :return:
    """
    if len(fn.returns_ssa) == 0:
        # No named return variable
        return

    last_assigns: Dict[int, List[Tuple[Operation, LocalIRVariable]]] = {
        i: [] for i in range(len(fn.returns))
    }
    ref_assigns: Dict[int, List[Tuple[Operation, ReferenceVariableSSA]]] = {
        i: [] for i in range(len(fn.returns))
    }

    def mark_last_assign():
        for i, assigns in last_assigns.items():
            if len(assigns) > 0:
                last_assign = assigns[-1]
                if NAMED_RETURN_LAST_ASSIGN_KEY not in last_assign[0].context:
                    last_assign[0].context[NAMED_RETURN_LAST_ASSIGN_KEY] = set()
                last_assign[0].context[NAMED_RETURN_LAST_ASSIGN_KEY] |= {
                    (
                        i,
                        last_assign[1],
                    )
                }
        for i, assigns in ref_assigns.items():
            for assign in assigns:
                if NAMED_RETURN_LAST_ASSIGN_KEY not in assign[0].context:
                    assign[0].context[NAMED_RETURN_LAST_ASSIGN_KEY] = set()
                assign[0].context[NAMED_RETURN_LAST_ASSIGN_KEY] |= {
                    (
                        i,
                        assign[1],
                    )
                }

    visited: Set[Node] = set()

    def dfs(node: Node):
        if node in visited:
            return

        nonlocal last_assigns
        last_assigns_cp = copy.copy(last_assigns)

        for op in node.irs_ssa:
            if isinstance(op, Assignment):
                if isinstance(op.lvalue, LocalIRVariable):
                    for i in last_assigns:
                        if op.lvalue.non_ssa_version == fn.returns[i]:
                            last_assigns[i].append((op, op.rvalue))
                elif isinstance(op.lvalue, ReferenceVariableSSA) and isinstance(
                    op.lvalue.points_to_origin, LocalIRVariable
                ):
                    for i in ref_assigns:
                        if op.lvalue.points_to_origin.non_ssa_version == fn.returns[i]:
                            ref_assigns[i].append((op, op.rvalue))

            elif isinstance(op, Return):
                # FIXME: workaround for issue crytic/slither#1827
                # return literal fixed array for named return variable

                for i, ret in enumerate(op.values):
                    last_assigns[i].append((op, ret))

        if node.will_return:
            mark_last_assign()
            return

        visited.add(node)
        for son in node.sons:
            dfs(son)

        last_assigns = last_assigns_cp
        # we don't consider override of assignments to references (over-approximate data flow)

    dfs(fn.entry_point)


# In the context of an operation, this is used to store the set of functions that are called by this operation.
INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY = "intra_procedural_internal_call_edge"

# In the context of a function, this is used to store the set of operations that call this function.
INTRA_PROCEDURAL_INTERNAL_CALLER_KEY = "intra_procedural_internal_caller"


def summarize_intra_procedural_internal_call_edges(fn: Function):
    """
    Summarize the intra_contract (inter-procedural) call edges:
    :param fn:
    :return:
    """

    for op in fn.slithir_ssa_operations + fn.slithir_operations:
        if isinstance(op, (InternalCall, LibraryCall)):
            op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY] = (
                {op.function} if op.function.is_implemented else set()
            )
        elif isinstance(op, InternalDynamicCall):
            data_dep = op.node.function.context[KEY_SSA]
            if op.function in data_dep:
                op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY] = {
                    callee
                    for callee in data_dep[op.function]
                    if isinstance(callee, Function) and callee.is_implemented
                }
            else:
                op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY] = set()

        # set INTRA_CONTRACT_CALLER_KEY for each callee function
        if INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY not in op.context:
            continue
        for callee in op.context[INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY]:
            if INTRA_PROCEDURAL_INTERNAL_CALLER_KEY not in callee.context:
                callee.context[INTRA_PROCEDURAL_INTERNAL_CALLER_KEY] = set()
            callee.context[INTRA_PROCEDURAL_INTERNAL_CALLER_KEY].add(op)


# In the context of an operation, this is used to store the set of asset transfers that are performed by this operation.
TRANSFER_KEY = "transfer"


def summarize_intra_procedural_profits(fn: Function):
    """
    Summarize the intra_contract (inter-procedural) profit locations:
    :param fn:
    :return:
    """
    for op in fn.slithir_ssa_operations + fn.slithir_operations:
        transfers = resolve_asset_transfer_op(op)
        op.context[TRANSFER_KEY] = transfers
