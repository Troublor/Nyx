from abc import ABC
from enum import Enum
from typing import TYPE_CHECKING

import structlog
import z3
from slither.core.declarations import Modifier, Function
from slither.slithir.operations import Operation
from structlog.stdlib import BoundLogger

from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.transfer import ResolvedTransfer
from engine2.variable import AbsVar

if TYPE_CHECKING:
    from engine2.summary import SummaryApplication
    from engine2.engine import SymEngine
    from engine2.summary_builder import FunctionSummaryBuilder


class UnknownCallHandleStrategy(Enum):
    # When the function summary is applied,
    # statically use the same single free variable for each return value at each call site.
    STATIC = "static"

    # When the function summary is applied,
    # dynamically generate a new free variable for each return value of each call site.
    # That is to say, different application will use different free variables.
    DYNAMIC = "dynamic"


class EngineController(ABC):
    """
    The controller of the summary builder.
    """

    @property
    def logger(self) -> BoundLogger:
        return structlog.get_logger()

    """Configurations"""

    @property
    def path_condition_limit(self) -> int | None:
        """
        The maximum number of most recent path conditions to be used.
        if None, all path conditions are used.
        """
        return None

    @property
    def unknown_call_strategy(self) -> UnknownCallHandleStrategy:
        """
        How to deal with the return value of unknown calls.
        :return:
        """
        return UnknownCallHandleStrategy.DYNAMIC

    @property
    def concretize_non_linear_expression(self) -> bool:
        """
        Whether to concretize non-linear computation.
        """
        return False

    """ Callbacks """

    def before_op(self, op: Operation, builder: "SymEngine"):
        pass

    def after_op(self, op: Operation, builder: "SymEngine"):
        pass

    def on_transfer(self, transfer: ResolvedTransfer, builder: "SymEngine"):
        pass


class SummaryController(EngineController):
    """
    The controller of the summary builder.
    """

    @property
    def logger(self) -> BoundLogger:
        return structlog.get_logger()

    """Configurations"""

    @property
    def path_condition_limit(self) -> int | None:
        """
        The maximum number of most recent path conditions to be used.
        if None, all path conditions are used.
        """
        return None

    @property
    def unknown_call_strategy(self) -> UnknownCallHandleStrategy:
        """
        How to deal with the return value of unknown calls.
        :return:
        """
        return UnknownCallHandleStrategy.DYNAMIC

    @property
    def reuse_function_summary(self) -> bool:
        """
        Whether to use function summary.
        """
        return True

    """ Callbacks """

    def before_op(self, op: Operation, builder: "FunctionSummaryBuilder"):
        pass

    def after_op(self, op: Operation, builder: "FunctionSummaryBuilder"):
        pass

    def before_summarize(self, builder: "FunctionSummaryBuilder"):
        pass

    def after_summarize(self, builder: "FunctionSummaryBuilder"):
        pass

    def on_application(
        self,
        application: "SummaryApplication",
    ):
        pass
