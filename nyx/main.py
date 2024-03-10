import argparse
import json
import logging.config
import resource
import time
from pathlib import Path

import structlog

from analyze import analyze_single
from analyze.config import Config
from analyze.group import AnalyzeGroup
from analyze.observe import Observer
from engine2.controller import UnknownCallHandleStrategy
from galaxy.ContractRepo import ContractRepoRaw, CryticCompileRepo
from lib.log import *
from lib.signal import register_interrupt_handler

observer = Observer()
config = Config()


def config_logger(_args) -> structlog.BoundLogger:
    # console processors
    console_formatter = structlog.stdlib.ProcessorFormatter(
        processors=[
            structlog.processors.TimeStamper(fmt="iso", utc=False),
            structlog.processors.add_log_level,
            structlog.stdlib.ProcessorFormatter.remove_processors_meta,
            structlog.dev.ConsoleRenderer(),
        ],
    )
    console_handler = logging.StreamHandler()
    console_handler.setFormatter(console_formatter)
    std_logger = logging.getLogger()
    std_logger.handlers.clear()  # remove default handler
    std_logger.addHandler(console_handler)
    std_logger.setLevel(_args.log_level)

    structlog.configure(
        processors=[
            # Prepare event dict for `ProcessorFormatter`.
            structlog.stdlib.ProcessorFormatter.wrap_for_formatter,
        ],
        logger_factory=structlog.stdlib.LoggerFactory(),
    )

    # file processors
    if _args.log_file:
        file_formatter = structlog.stdlib.ProcessorFormatter(
            processors=[
                structlog.processors.TimeStamper(fmt="iso", utc=False),
                structlog.processors.add_log_level,
                structlog.stdlib.ProcessorFormatter.remove_processors_meta,
                structlog.processors.JSONRenderer(),
            ],
        )
        file_handler = logging.FileHandler(_args.log_file)
        file_handler.setFormatter(file_formatter)
        std_logger = logging.getLogger()
        std_logger.addHandler(file_handler)
        std_logger.setLevel(_args.log_level)

    return structlog.get_logger()


def analyze_one(_args):
    repos = []
    for repo in _args.contract_repos:
        repos.append(ContractRepoRaw(Path(repo)))
        # repos.append(CryticCompileRepo(Path(repo)))

    group = AnalyzeGroup(
        _args.name,
        *repos,
    )
    group.focus(*_args.focus)
    group.result_file = _args.output
    group.profiling_file = _args.profiling_file

    t0 = time.time()
    config.logger.info(f"Analysis started", group=group.name)

    output = analyze_single(group, observer, config)

    config.logger.info(
        f"Analysis finished",
        group=group.name,
        pairs=len(output.pairs),
        time=time.time() - t0,
    )
    observer.total_time += time.time() - t0


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=str, default="result.json")
    parser.add_argument(
        "--log-level",
        type=str,
        choices=["INFO", "DEBUG", TRACE_LEVEL_TEXT],
        default="INFO",
    )
    parser.add_argument("--log-file", type=str, default=None)
    parser.add_argument("--profiling-file", type=str, default=None)
    parser.add_argument("--name", type=str, default="Contracts")
    parser.add_argument("--focus", action="append", default=[])
    parser.add_argument(
        "--memory-limit",
        type=int,
        default=-1,
        help="memory limit in MB, negative or zero means no limit",
    )
    parser.add_argument(
        "--solver-timeout",
        type=float,
        default=60,
        help="timeout of SMT solving in seconds",
    )
    parser.add_argument(
        "--function-timeout",
        type=float,
        default=float("inf"),
        help="timeout of execution of a public function in seconds (0 means no timeout)",
    )
    parser.add_argument(
        "--pair-execution-timeout",
        type=float,
        default=float("inf"),
        help="timeout of executing a function pair in two scenarios in seconds (0 means no timeout)",
    )
    parser.add_argument(
        "--path-condition-limit",
        type=int,
        default=-1,
        help="limit of path conditions. Negative means no limit. (default: no limit)",
    )
    parser.add_argument(
        "--concretize-non-linear-expression",
        action="store_true",
        help="concretize non-linear expressions",
    )
    parser.add_argument(
        "--reuse-function-summary",
        action="store_true",
        help="reuse function summary if possible",
    )
    parser.add_argument(
        "--unknown-call-strategy",
        type=str,
        choices=[
            UnknownCallHandleStrategy.STATIC.value,
            UnknownCallHandleStrategy.DYNAMIC.value,
        ],
        default=UnknownCallHandleStrategy.DYNAMIC.value,
        help="strategy when encountering unknown function calls",
    )
    parser.add_argument(
        "--disable-pruning",
        action="store_true",
        help="disable static pruning",
    )
    parser.add_argument(
        "--disable-validation",
        action="store_true",
        help="disable symbolic validation",
    )
    parser.add_argument("contract_repos", nargs="+")
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()

    # memory limit
    if args.memory_limit > 0:
        _, hard = resource.getrlimit(resource.RLIMIT_AS)
        resource.setrlimit(resource.RLIMIT_AS, (args.memory_limit * 1024 * 1024, hard))

    # configure
    config.logger = config_logger(args)
    config.solver_timeout = args.solver_timeout
    config.function_timeout = (
        args.function_timeout if args.function_timeout > 0 else float("inf")
    )
    config.pair_execution_timeout = (
        args.pair_execution_timeout if args.pair_execution_timeout > 0 else float("inf")
    )
    config.concretize_non_linear_expression = args.concretize_non_linear_expression
    config.reuse_function_summary = args.reuse_function_summary
    config.unknown_call_strategy = UnknownCallHandleStrategy(args.unknown_call_strategy)
    config.path_condition_limit = (
        args.path_condition_limit if args.path_condition_limit >= 0 else None
    )
    config.disable_pruning = args.disable_pruning
    config.disable_validation = args.disable_validation

    config.logger.info(
        "Command-line arguments",
        output=args.output,
        log_file=args.log_file,
        name=args.name,
        focus=args.focus,
        repos=args.contract_repos,
    )
    config.logger.info(
        "Analysis configuration",
        solver_timeout=f"{config.solver_timeout:.2f}s",
        function_timeout=f"{config.function_timeout:.2f}s",
        pair_timeout=f"{config.pair_execution_timeout:.2f}s",
    )

    register_interrupt_handler()
    analyze_one(args)

    config.cleanup()
    config.logger.info("Profiling result", result=json.dumps(observer.to_dict()))
