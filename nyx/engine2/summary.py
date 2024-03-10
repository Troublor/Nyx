from functools import cached_property
from typing import TYPE_CHECKING

import z3
from slither.core.declarations import Function, Contract, Modifier

from engine2.controller import UnknownCallHandleStrategy
from engine2.env import Env
from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.value import (
    type_to_sort,
    unique_name,
    sort_conversion,
    is_signed_type,
)

if TYPE_CHECKING:
    from engine2.summary_builder import FunctionSummaryBuilder


class StorageChange(dict[tuple[Contract, str], z3.ExprRef]):
    def substitute(
        self, strategy: list[tuple[z3.ExprRef, z3.ExprRef]]
    ) -> "StorageChange":
        change = StorageChange()
        for k, v in self.items():
            change[k] = z3.substitute(v, *strategy)
        return change

    def merge(
        self,
        other: dict[tuple[Contract, str], z3.ExprRef],
        path_condition: z3.BoolRef = None,
    ):
        if path_condition is None:
            for k, v in other.items():
                self[k] = v
        else:
            for k, v in other.items():
                if k in self:
                    v = self._do_assemble_new_val(self[k], v, path_condition)
                    self[k] = v
                else:
                    self[k] = v

    def _do_assemble_new_val(
        self, origin_val: z3.ExprRef, val: z3.ExprRef, cond: z3.BoolRef = None
    ):
        if cond is None:
            return val
        else:
            return z3.If(cond, val, origin_val)


class SummaryApplication:
    def __init__(
        self,
        summary: "FunctionSummary",
        state: State,
        msg_call: MsgCall,
        args: tuple[z3.ExprRef, ...],
    ):
        self.summary = summary

        """ input """
        self.state = state
        self.msg_call = msg_call
        self.args = args

        self.substitute_strategy: list[tuple[z3.ExprRef, z3.ExprRef]] = []

        """ output """
        self.free_values: list[z3.ExprRef] = list()

        # contract => state variable name => state variable written
        self.storage_written: StorageChange = StorageChange()

        self.returns: tuple[z3.ExprRef, ...] = tuple()

        # revert conditions
        self.revert_condition: z3.BoolRef | None = None

        # constraints
        self.constraints: list[z3.BoolRef] = list()


class FunctionSummary:
    """
    A summary of an internal/external function.
    It summarizes the symbolic function that given:
    1. state,
    2. arguments,
    so that
    1. what value will be returned
    2. how state will be updated
    3. what revert condition will be added
    4. what constraints will be added
    5. what free values will be added
    """

    def __init__(self, fn: Function, builder: "FunctionSummaryBuilder" = None):
        self.function = fn
        self._builder = builder
        self._controller = builder.controller

        """ input """

        self.param_sorts = tuple(type_to_sort(p.type) for p in fn.parameters)
        self.parameters = tuple(
            z3.Const(f"{fn.canonical_name}_param{i}", s)
            for i, s in enumerate(self.param_sorts)
        )

        """ output """

        self.return_sorts = tuple(type_to_sort(r.type) for r in fn.returns)
        self.returns = tuple(
            z3.Const(f"{fn.canonical_name}_return{i}", s)
            for i, s in enumerate(self.return_sorts)
        )

        # unknown call return values
        # when a function call is made to an unknown function,
        # the symbolic execution assign a fresh variable to the return value
        # These fresh variable need to be replaces with different fresh variables
        # in each summary application (i.e., call to apply function).
        self.free_values: list[z3.ExprRef] = list()

        # contract => state variable name => state variable written
        self.storage_written: StorageChange = StorageChange()

        # revert conditions
        self.raw_revert_conditions: list[z3.BoolRef] = list()

        # constraints
        self.raw_constraints: list[z3.BoolRef] = list()

    @property
    def _env(self) -> Env:
        return self._builder.env

    @property
    def _call(self) -> MsgCall:
        return self._builder.call

    @property
    def _state(self) -> State:
        return self._builder.state

    @cached_property
    def is_modifier(self) -> bool:
        return isinstance(self.function, Modifier)

    @property
    def revert_condition(self) -> z3.BoolRef | None:
        if len(self.raw_revert_conditions) == 0:
            return None
        elif len(self.raw_revert_conditions) == 1:
            return self.raw_revert_conditions[0]
        else:
            return z3.Or(*self.raw_revert_conditions)

    @property
    def id(self) -> str:
        return self.function.canonical_name

    @property
    def constraints(self) -> list[z3.BoolRef]:
        return self._env.constraints
        # return []

    def apply(
        self,
        state: State,
        msg_call: MsgCall,
        args: tuple[z3.ExprRef, ...],
    ) -> SummaryApplication:
        """
        Apply the function to the given arguments.
        """
        assert len(args) == len(self.parameters)
        application = SummaryApplication(self, state, msg_call, args)

        # implicit convert type for parameters
        args = [z3.simplify(a) for a in args]
        for i, p in enumerate(self.parameters):
            args[i] = sort_conversion(
                p.sort(), args[i], is_signed_type(self.function.parameters[i].type)
            )

        # new set of free values
        free_values = [
            z3.Const(unique_name("free_" + str(s)), s.sort()) for s in self.free_values
        ]

        strategy = (
            self._state.substitute_strategy(state)
            + self._call.substitute_strategy(msg_call)
            + list(zip(self.parameters, args))
        )
        if self._controller.unknown_call_strategy == UnknownCallHandleStrategy.DYNAMIC:
            strategy += list(zip(self.free_values, free_values))
        application.substitute_strategy = strategy

        # substitute storage writes
        application.storage_written = self.storage_written.substitute(strategy)

        # substitute returns
        application.returns = tuple(z3.substitute(r, *strategy) for r in self.returns)

        # substitute revert condition
        if self.revert_condition is not None:
            application.revert_condition = z3.substitute(
                self.revert_condition, *strategy
            )
        else:
            application.revert_condition = None

        # substitute constraints
        application.constraints = [
            z3.substitute(c, *strategy) for c in self.constraints
        ]

        # free values
        application.free_values = free_values

        # callbacks
        self._controller.on_application(application)

        return application
