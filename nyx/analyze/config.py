from enum import Enum
from typing import Callable

import structlog
from slither.core.declarations import FunctionContract
from structlog.stdlib import BoundLogger

from engine2.controller import UnknownCallHandleStrategy
from lib.signal import interrupted


class Config:
    def __init__(self):
        self.logger: BoundLogger = structlog.get_logger()
        self.disable_pruning: bool = False
        self.disable_validation: bool = False
        self.concretize_non_linear_expression: bool = False
        self.reuse_function_summary: bool = False
        self.path_condition_limit: int | None = None
        self.unknown_call_strategy: UnknownCallHandleStrategy = (
            UnknownCallHandleStrategy.DYNAMIC
        )

        self.solver_timeout: float = 300  # in seconds
        self.function_timeout: float = float("inf")  # in seconds
        self.pair_execution_timeout: float = float("inf")  # in seconds

        self.cleanup_tasks: list[Callable] = []

    def cleanup(self):
        for task in self.cleanup_tasks:
            task()


class FunctionPairResult(Enum):
    VULNERABLE = "vulnerable"
    SAFE = "safe"
    FUNCTION_TIMEOUT = "function_timeout"
    SOLVER_TIMEOUT = "solver_timeout"
    PAIR_EXECUTION_TIMEOUT = "pair_execution_timeout"
    INTERRUPTED = "interrupted"


class Output:
    def __init__(self):
        self.functions: set[FunctionContract] = set()
        self.phase0_pairs_count: int = 0
        self.phase1_pairs: set[tuple[FunctionContract, FunctionContract]] = set()
        self.phase2_pairs: set[
            tuple[FunctionContract, FunctionContract, FunctionPairResult]
        ] = set()

    @property
    def pairs(self) -> set[tuple[FunctionContract, FunctionContract]]:
        return {
            (fn1, fn2)
            for fn1, fn2, r in self.phase2_pairs
            if r == FunctionPairResult.VULNERABLE
        }

    def _stringify_fn(self, fn: FunctionContract) -> str:
        return fn.canonical_name

    def to_dict(self) -> dict:
        return {
            "functions": [self._stringify_fn(fn) for fn in self.functions],
            "phase0": self.phase0_pairs_count,
            "phase1": [
                (self._stringify_fn(fn1), self._stringify_fn(fn2))
                for fn1, fn2 in self.phase1_pairs
            ],
            "phase2": [
                (self._stringify_fn(fn1), self._stringify_fn(fn2), r.value)
                for fn1, fn2, r in self.phase2_pairs
            ],
            "result": [
                (self._stringify_fn(fn1), self._stringify_fn(fn2))
                for fn1, fn2, r in self.phase2_pairs
                if r == FunctionPairResult.VULNERABLE
            ],
            "interrupted": interrupted(),
        }
