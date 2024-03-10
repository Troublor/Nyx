import time
from collections import defaultdict

import structlog
import z3
from structlog.stdlib import BoundLogger

from engine2.controller import SummaryController, UnknownCallHandleStrategy
from engine2.engine import SymEngine
from engine2.summary import SummaryApplication
from engine2.summary_builder import FunctionSummaryBuilder
from engine2.transfer import ResolvedTransfer


class TimeoutException(TimeoutError):
    pass


class Controller(SummaryController):
    def __init__(
        self,
        logger: BoundLogger = None,
        function_timeout: float = float("inf"),
        concretize_non_linear_expression: bool = False,
        reuse_function_summary: bool = False,
        path_condition_limit: int | None = None,
        unknown_call_strategy: UnknownCallHandleStrategy = UnknownCallHandleStrategy.DYNAMIC,
    ):
        self._logger = logger or structlog.get_logger()

        # configurations
        assert function_timeout > 0
        self.function_timeout = function_timeout  # in seconds
        self._concretize_non_linear_expression = concretize_non_linear_expression
        self._reuse_function_summary = reuse_function_summary
        self._path_condition_limit = path_condition_limit
        self._unknown_call_strategy = unknown_call_strategy

        self._start_time = time.time()

        # function summary id => list of transfers
        self.transfers: dict[str, list[ResolvedTransfer]] = defaultdict(list)
        self.current_transfers: list[ResolvedTransfer] = list()

        # call stack
        self._call_stack: list[str] = list()

    def reset_timer(self):
        self._start_time = time.time()

    @property
    def logger(self) -> BoundLogger:
        return self._logger

    @property
    def unknown_call_strategy(self) -> UnknownCallHandleStrategy:
        return self._unknown_call_strategy

    @property
    def path_condition_limit(self) -> int | None:
        return self._path_condition_limit

    @property
    def reuse_function_summary(self) -> bool:
        return self._reuse_function_summary

    @property
    def concretize_non_linear_expression(self) -> bool:
        return self._concretize_non_linear_expression

    def on_transfer(self, transfer: ResolvedTransfer, builder: "SymEngine"):
        self.transfers[builder.function.canonical_name].append(transfer)
        self.current_transfers.append(transfer)

    def before_summarize(self, builder: FunctionSummaryBuilder):
        if self.function_timeout != float("inf"):
            if time.time() - self._start_time > self.function_timeout:
                raise TimeoutError()
        self._call_stack.append(builder.summary.id)

    def after_summarize(self, builder: FunctionSummaryBuilder):
        self._call_stack.pop()

    def apply_transfers(
        self, summary_id: str, substitute_strategy: list[tuple[z3.ExprRef, z3.ExprRef]]
    ) -> list[ResolvedTransfer]:
        transfers = [
            t.substitute(substitute_strategy) for t in self.transfers[summary_id]
        ]
        return transfers

    def on_application(
        self,
        application: "SummaryApplication",
    ):
        if len(self._call_stack) == 0:
            return

        summary_id = self._call_stack[-1]
        transfers = self.apply_transfers(
            application.summary.id, application.substitute_strategy
        )
        self.transfers[summary_id].extend(transfers)
        self.current_transfers.extend(transfers)
