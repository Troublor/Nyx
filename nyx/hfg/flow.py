from __future__ import annotations

from enum import Enum
from typing import Union

from slither.core.declarations import Function
from slither.core.variables.state_variable import StateVariable
from slither.slithir.operations import (
    Operation,
    InternalCall,
    InternalDynamicCall,
    LibraryCall,
    SolidityCall,
    LowLevelCall,
    HighLevelCall,
)
from slither.slithir.variables.variable import SlithIRVariable


class FlowType(Enum):
    # control flow
    IntraProceduralControl = 0
    InterProceduralCall = 1
    InterProceduralReturn = 2

    # data flow
    IntraTransactionData = 7
    InterTransactionData = 8


InternalCallableOperation = Union[
    InternalCall,
    InternalDynamicCall,
    LibraryCall,
]

ExternalCallableOperation = Union[
    HighLevelCall,
    LowLevelCall,
    SolidityCall,
]


class Flow(object):
    def __init__(self, flow_type: FlowType):
        self.type = flow_type


class IntraProceduralControlFlow(Flow):
    def __init__(self):
        super().__init__(FlowType.IntraProceduralControl)

    def __eq__(self, other):
        return isinstance(other, IntraProceduralControlFlow)

    def __hash__(self):
        return hash(("IntraProceduralControlFlow", self.type))

    def __str__(self):
        return "IntraProceduralControlFlow"


class InterProceduralCallFlow(Flow):
    def __init__(self, call_site: Operation, callee: Function):
        super().__init__(FlowType.InterProceduralCall)
        self.call_site = call_site
        self.callee = callee

    def __eq__(self, other):
        return (
            isinstance(other, InterProceduralCallFlow)
            and self.call_site == other.call_site
            and self.callee == other.callee
        )

    def __hash__(self):
        return hash(("InterProceduralCallFlow", self.type, self.call_site, self.callee))

    def __str__(self):
        return f"InterProceduralCallFlow({self.call_site}, {self.callee})"


class InterProceduralReturnFlow(Flow):
    def __init__(self, call_site: Operation, callee: Function):
        super().__init__(FlowType.InterProceduralReturn)
        self.call_site = call_site
        self.callee = callee

    def __eq__(self, other):
        return (
            isinstance(other, InterProceduralReturnFlow)
            and self.call_site == other.call_site
            and self.callee == other.callee
        )

    def __hash__(self):
        return hash(
            ("InterProceduralReturnFlow", self.type, self.call_site, self.callee)
        )

    def __str__(self):
        return f"InterProceduralReturnFlow({self.call_site}, {self.callee})"


class IntraTransactionDataFlow(Flow):
    def __init__(
        self,
        source: PseudoVariable,
        sink: PseudoVariable,
    ):
        super().__init__(FlowType.IntraTransactionData)
        self.source = source
        self.sink = sink

    def __eq__(self, other):
        return (
            isinstance(other, IntraTransactionDataFlow)
            and self.source == other.source
            and self.sink == other.sink
        )

    def __hash__(self):
        return hash(("IntraTransactionDataFlow", self.type, self.source, self.sink))

    def __str__(self):
        return f"IntraTransactionDataFlow({self.source}, {self.sink})"


class InterTransactionDataFlow(Flow):
    def __init__(
        self,
        source: Union[StateVariable, PseudoVariable],
        sink: Union[StateVariable, PseudoVariable],
    ):
        super().__init__(FlowType.InterTransactionData)
        self.source = source
        self.sink = sink

    def __eq__(self, other):
        return (
            isinstance(other, InterTransactionDataFlow)
            and self.source == other.source
            and self.sink == other.sink
        )

    def __hash__(self):
        return hash(("InterTransactionDataFlow", self.type, self.source, self.sink))

    def __str__(self):
        return f"InterTransactionDataFlow({self.source}, {self.sink})"


class PseudoVariable(object):
    """
    Pseudo variable that is only used in the HFG.
    """

    pass


class FunctionParamVariable(PseudoVariable):
    def __init__(self, function: Function, index: int):
        """
        :param function:
        :param index: start from 1
        """
        super().__init__()
        self.function = function
        self.index = index

    def __str__(self):
        return f"{self.function}.params[{self.index}]"

    def __eq__(self, other):
        return (
            isinstance(other, FunctionParamVariable)
            and self.function == other.function
            and self.index == other.index
        )

    def __hash__(self):
        return hash((self.function, self.index))


class FunctionReturnVariable(PseudoVariable):
    def __init__(self, function: Function, index: int):
        """
        :param function:
        :param index: start from 1
        """
        super().__init__()
        self.function = function
        self.index = index

    def __str__(self):
        return f"{self.function}.returns[{self.index}]"

    def __eq__(self, other):
        return (
            isinstance(other, FunctionReturnVariable)
            and self.function == other.function
            and self.index == other.index
        )

    def __hash__(self):
        return hash((self.function, self.index))


class CallArgVariable(PseudoVariable):
    def __init__(self, call: Operation, index: int):
        """
        :param function:
        :param index: start from 1
        """
        super().__init__()
        self.call = call
        self.index = index

    def __str__(self):
        return f"{self.call}.args[{self.index}]"

    def __eq__(self, other):
        return (
            isinstance(other, CallArgVariable)
            and self.call == other.call
            and self.index == other.index
        )

    def __hash__(self):
        return hash((self.call, self.index))


class CallReturnVariable(PseudoVariable):
    def __init__(self, call: Operation, index: int):
        """
        :param function:
        :param index: start from 1
        """
        super().__init__()
        self.call = call
        self.index = index

    def __str__(self):
        return f"{self.call}.returns[{self.index}]"

    def __eq__(self, other):
        return (
            isinstance(other, CallReturnVariable)
            and self.call == other.call
            and self.index == other.index
        )

    def __hash__(self):
        return hash((self.call, self.index))


class WrappedSlithIRVariable(PseudoVariable):
    def __init__(self, slithir_variable: SlithIRVariable):
        super().__init__()
        self.slithir_variable = slithir_variable

    def __str__(self):
        return f"{self.slithir_variable}"

    def __eq__(self, other):
        return (
            isinstance(other, WrappedSlithIRVariable)
            and self.slithir_variable == other.slithir_variable
        )

    def __hash__(self):
        return hash(self.slithir_variable)
