import time

import z3
from slither.core.declarations import FunctionContract, Contract, Structure
from slither.core.solidity_types import ElementaryType, UserDefinedType, ArrayType
from structlog.stdlib import BoundLogger

from analyze.config import Config, FunctionPairResult
from analyze.controller import Controller
from analyze.observe import Observer
from analyze.profit import ProfitCollection
from engine2.transfer import ResolvedTransfer
from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.summary import FunctionSummary
from engine2.summary_builder import FunctionSummaryBuilder
from engine2.value import (
    type_to_sort,
    unique_name,
    structure_accessors,
    collision_free_constraints,
)
from lib.signal import interrupt, interrupted


def update_datatype(
    structure: Structure, val: z3.DatatypeRef, key: str, field: z3.ExprRef
) -> z3.DatatypeRef:
    fields = []
    accessors = structure_accessors(structure)
    for k, accessor in accessors.items():
        if k == key:
            fields.append(field)
        else:
            fields.append(accessor(val))
    return val.sort().constructor(0)(*fields)


class Validator:
    def __init__(
        self,
        contracts: set[Contract],
        observer: Observer = None,
        config: Config = None,
        logger: BoundLogger = None,
    ):
        self.contracts = contracts
        self.summaries: dict[
            str, FunctionSummary | None
        ] = dict()  # None means failed to summarize
        self.observer: Observer = observer if observer else Observer()
        self.config: Config = config if config else Config()
        self.logger = logger if logger else self.config.logger
        self.controller = Controller(
            self.logger,
            function_timeout=self.config.function_timeout,
            concretize_non_linear_expression=self.config.concretize_non_linear_expression,
            reuse_function_summary=self.config.reuse_function_summary,
            path_condition_limit=self.config.path_condition_limit,
            unknown_call_strategy=self.config.unknown_call_strategy,
        )
        # cache
        self.init_state: State = State(self.contracts)
        self.fn_exe_cache: dict[
            FunctionContract,
            tuple[
                State,
                MsgCall,
                list[z3.ExprRef],
                list[ResolvedTransfer],
                FunctionSummary,
            ],
        ] = dict()

    def _summary_of(
        self, fn: FunctionContract
    ) -> FunctionSummary | None:  # None means failed to summarize
        t0 = time.time()

        if fn.canonical_name not in self.summaries:
            builder = FunctionSummaryBuilder(
                fn, self.contracts, self.summaries, self.controller
            )
            self.controller.reset_timer()
            try:
                summary = builder.build()
                self.summaries[summary.id] = summary
            except TimeoutError:
                self.logger.warn(
                    "Function summarization timed out", fn=fn.canonical_name
                )
                self.summaries[builder.summary.id] = None

        self.observer.summarization_time += time.time() - t0

        return self.summaries[fn.canonical_name]

    def execute_function_from_fresh(self, fn: FunctionContract) -> None:
        if fn in self.fn_exe_cache:
            return

        t0 = time.time()
        sender = z3.Const(unique_name("sender"), type_to_sort("address"))
        profit_addresses = [sender]
        value = z3.Const(unique_name("value"), type_to_sort("uint256"))
        callee = self.init_state.load_contract(fn.contract).val
        assert isinstance(callee, z3.BitVecRef)
        call = MsgCall(sender, value, callee)
        state = self.init_state.copy()
        args = []
        for p in fn.parameters:
            sort = type_to_sort(p.type)
            arg = z3.Const(unique_name(p.name), sort)

            p_type = p.type
            if isinstance(p_type, ElementaryType) and p_type.type == "address":
                profit_addresses.append(arg)
            elif isinstance(p_type, UserDefinedType):
                p_type_type = p_type.type
                if isinstance(p_type_type, Structure):
                    for field in p_type_type.elems_ordered:
                        field_type = field.type
                        if (
                            isinstance(field_type, ElementaryType)
                            and field_type.type == "address"
                        ):
                            sender_ = z3.Const(
                                unique_name("sender'"), type_to_sort("address")
                            )
                            arg = update_datatype(p_type_type, arg, field.name, sender_)
                            profit_addresses.append(sender_)
            elif isinstance(p_type, ArrayType) and not p_type.is_dynamic:
                p_type_type = p_type.type
                if (
                    isinstance(p_type_type, ElementaryType)
                    and p_type_type.type == "address"
                ):
                    length = int(p_type.length_value.value)
                    for i in range(length):
                        sender_ = z3.Const(
                            unique_name("sender'"), type_to_sort("address")
                        )
                        arg = z3.Update(arg, i, sender_)
                        profit_addresses.append(sender_)
            args.append(arg)
        args = tuple(args)
        builder = FunctionSummaryBuilder(
            fn,
            self.contracts,
            self.summaries,
            self.controller,
            state=state,
            msg_call=call,
        )
        self.controller.reset_timer()
        try:
            self.controller.current_transfers = []
            summary = builder.build(args=args)
            transfers = self.controller.current_transfers
            self.controller.current_transfers = []
            self.fn_exe_cache[fn] = (state, call, profit_addresses, transfers, summary)
        finally:
            self.observer.summarization_time += time.time() - t0

    def validate2(
        self, fn_pair: tuple[FunctionContract, FunctionContract]
    ) -> FunctionPairResult:
        logger = self.logger.bind(
            fn1=fn_pair[0].canonical_name,
            fn2=fn_pair[1].canonical_name,
        )

        fn1, fn2 = fn_pair
        try:
            self.execute_function_from_fresh(fn1)
        except TimeoutError:
            self.logger.warn("Function summarization timed out", fn=fn1.canonical_name)
        if interrupted():
            return FunctionPairResult.INTERRUPTED
        try:
            self.execute_function_from_fresh(fn2)
        except TimeoutError:
            self.logger.warn("Function summarization timed out", fn=fn2.canonical_name)
        if interrupted():
            return FunctionPairResult.INTERRUPTED

        # load the cache of executing fn1
        state_a, call1, profit_addresses1, transfers1_a, summary1 = self.fn_exe_cache[
            fn1
        ]
        # load the cache of executing fn2
        if fn2 != fn1:
            (
                state_af,
                call2,
                profit_addresses2,
                transfers2_af,
                summary2,
            ) = self.fn_exe_cache[fn2]
        else:
            sender = z3.Const(unique_name("sender"), type_to_sort("address"))
            profit_addresses2 = [sender]
            value = z3.Const(unique_name("value"), type_to_sort("uint256"))
            callee = self.init_state.load_contract(fn2.contract).val
            assert isinstance(callee, z3.BitVecRef)
            call2 = MsgCall(sender, value, callee)
            state_af = self.init_state.copy()
            args = []
            for p in fn2.parameters:
                sort = type_to_sort(p.type)
                arg = z3.Const(unique_name(p.name), sort)

                p_type = p.type
                if isinstance(p_type, ElementaryType) and p_type.type == "address":
                    profit_addresses2.append(arg)
                elif isinstance(p_type, UserDefinedType):
                    p_type_type = p_type.type
                    if isinstance(p_type_type, Structure):
                        for field in p_type_type.elems_ordered:
                            field_type = field.type
                            if (
                                isinstance(field_type, ElementaryType)
                                and field_type.type == "address"
                            ):
                                sender_ = z3.Const(
                                    unique_name("sender'"), type_to_sort("address")
                                )
                                arg = update_datatype(
                                    p_type_type, arg, field.name, sender_
                                )
                                profit_addresses2.append(sender_)
                elif isinstance(p_type, ArrayType) and not p_type.is_dynamic:
                    p_type_type = p_type.type
                    if (
                        isinstance(p_type_type, ElementaryType)
                        and p_type_type.type == "address"
                    ):
                        length = int(p_type.length_value.value)
                        for i in range(length):
                            sender_ = z3.Const(
                                unique_name("sender'"), type_to_sort("address")
                            )
                            arg = z3.Update(arg, i, sender_)
                            profit_addresses2.append(sender_)
                args.append(arg)
            args = tuple(args)
            builder = FunctionSummaryBuilder(
                fn2,
                self.contracts,
                self.summaries,
                self.controller,
                state=state_af,
                msg_call=call2,
            )
            self.controller.reset_timer()
            self.controller.current_transfers = []
            summary2 = builder.build(args=args)
            transfers2_af = self.controller.current_transfers
            self.controller.current_transfers = []

        if interrupted():
            return FunctionPairResult.INTERRUPTED

        solver = z3.Solver()
        solver.set("timeout", int(self.config.solver_timeout * 1000))

        solver.add(call1.sender.val != call2.sender.val)

        # attack scenario fn1 -> fn2
        t2 = time.time()
        logger.debug("Simulating execution scenario fn1->fn2...")
        # execute fn1
        # ... already did in execute_function_from_fresh
        state_a = state_a.copy()
        # collect profits
        ps1_a = ProfitCollection(profit_addresses1, summary1.revert_condition)
        ps1_a.add_transfer(*transfers1_a)
        # add constraints
        solver.add(*summary1.constraints)
        logger.debug(
            "Function fn1 applied",
            fn=fn1.canonical_name,
            time=f"{time.time() - t2:.2f}s",
        )
        if interrupted():
            return FunctionPairResult.INTERRUPTED

        # execute fn2
        t3 = time.time()
        if self.controller.reuse_function_summary:
            application = summary2.apply(state_a, call2, summary2.parameters)
            # collect profits
            ps2_a = ProfitCollection(profit_addresses2, application.revert_condition)
            transfers2_a = [
                t.substitute(application.substitute_strategy) for t in transfers2_af
            ]
            ps2_a.add_transfer(*transfers2_a)
            # add constraints
            solver.add(*application.constraints)
        else:
            builder = FunctionSummaryBuilder(
                fn2,
                self.contracts,
                self.summaries,
                self.controller,
                state=state_a,
                msg_call=call2,
            )
            self.controller.current_transfers = []
            application = builder.build(args=summary2.parameters)
            # collect profits
            ps2_a = ProfitCollection(profit_addresses2, application.revert_condition)
            transfers2_a = self.controller.current_transfers
            self.controller.current_transfers = []
            ps2_a.add_transfer(*transfers2_a)
            # add constraints
            solver.add(*application.constraints)
        if interrupted():
            return FunctionPairResult.INTERRUPTED
        logger.debug(
            "Function fn2 applied",
            fn=fn2.canonical_name,
            time=f"{time.time() - t3:.2f}s",
        )

        # attack-free scenario fn2 -> fn1
        t4 = time.time()
        logger.debug("Simulating execution scenario fn2->fn1...")
        # execute fn2
        # ... already did in execute_function_from_fresh
        state_af = state_af.copy()
        # collect profits
        ps2_af = ProfitCollection(profit_addresses2, summary2.revert_condition)
        ps2_af.add_transfer(*transfers2_af)
        # add constraints
        solver.add(*summary2.constraints)
        logger.debug(
            "Function fn2 applied",
            fn=fn2.canonical_name,
            time=f"{time.time() - t4:.2f}s",
        )
        if interrupted():
            return FunctionPairResult.INTERRUPTED

        # execute fn1
        t5 = time.time()
        if self.controller.reuse_function_summary:
            application = summary1.apply(state_af, call1, summary1.parameters)
            # collect profits
            ps1_af = ProfitCollection(profit_addresses1, application.revert_condition)
            transfers1_af = [
                t.substitute(application.substitute_strategy) for t in transfers1_a
            ]
            ps1_af.add_transfer(*transfers1_af)
            # add constraints
            solver.add(*application.constraints)
        else:
            builder = FunctionSummaryBuilder(
                fn1,
                self.contracts,
                self.summaries,
                self.controller,
                state=state_af,
                msg_call=call1,
            )
            self.controller.current_transfers = []
            application = builder.build(args=summary1.parameters)
            # collect profits
            ps1_af = ProfitCollection(profit_addresses1, application.revert_condition)
            transfers1_af = self.controller.current_transfers
            self.controller.current_transfers = []
            ps1_af.add_transfer(*transfers1_af)
            # add constraints
            solver.add(*application.constraints)
        if interrupted():
            return FunctionPairResult.INTERRUPTED
        logger.debug(
            "Function fn1 applied",
            fn=fn1.canonical_name,
            time=f"{time.time() - t5:.2f}s",
        )

        self.observer.application_time += time.time() - t2

        # attack property
        solver.add(ps1_a > ps1_af)
        solver.add(ps2_af > ps2_a)

        solver.add(*collision_free_constraints)

        t6 = time.time()
        logger.debug("Checking vulnerability property...")
        res = solver.check()
        check_time = time.time() - t6
        self.observer.solving_time += check_time
        if res == z3.unknown and check_time < self.config.solver_timeout:
            # interrupt instead of timeout
            interrupt()
            return FunctionPairResult.INTERRUPTED
        logger.debug(
            "Vulnerability property checked",
            result=res,
            time=f"{check_time:.2f}s",
        )

        logger.unbind("fn1", "fn2")

        if res == z3.sat:
            return FunctionPairResult.VULNERABLE
        elif res == z3.unsat:
            return FunctionPairResult.SAFE
        else:
            return FunctionPairResult.SOLVER_TIMEOUT

    def validate(
        self, fn_pair: tuple[FunctionContract, FunctionContract]
    ) -> FunctionPairResult:
        logger = self.logger.bind(
            fn1=fn_pair[0].canonical_name,
            fn2=fn_pair[1].canonical_name,
        )

        fn1, fn2 = fn_pair
        solver = z3.Solver()
        solver.set("timeout", int(self.config.solver_timeout * 1000))

        t0 = time.time()
        summary1 = self._summary_of(fn1)
        if summary1 is None:
            logger.warn(
                "Pair validation aborts due to function summarization timeout",
                fn=fn1.canonical_name,
            )
            return FunctionPairResult.FUNCTION_TIMEOUT
        logger.debug(
            "Function summarized",
            fn=fn1.canonical_name,
            time=f"{time.time() - t0:.2f}s",
        )

        t1 = time.time()
        summary2 = self._summary_of(fn2)
        logger.debug(
            "Function summarized",
            fn=fn2.canonical_name,
            time=f"{time.time() - t1:.2f}s",
        )
        if summary2 is None:
            logger.warn(
                "Pair validation aborts due to function summarization timeout",
                fn=fn2.canonical_name,
            )
            return FunctionPairResult.FUNCTION_TIMEOUT

        t_exe = time.time()

        def is_timeout() -> bool:
            timeout = time.time() - t_exe > self.config.pair_execution_timeout
            if timeout:
                logger.warn(
                    "Pair execution timed out",
                    fn1=fn1.canonical_name,
                    fn2=fn2.canonical_name,
                )
            return timeout

        state = State(self.contracts)
        account1 = z3.Const("account1", type_to_sort("address"))
        account1_addrs = [account1]
        account2 = z3.Const("account2", type_to_sort("address"))
        account2_addrs = [account2]
        solver.add(account1 != account2)
        solver.add(account1 != 0)
        solver.add(account2 != 0)
        value1 = z3.Const("value1", type_to_sort("uint256"))
        value2 = z3.Const("value2", type_to_sort("uint256"))
        callee1 = state.load_contract(fn1.contract).val
        callee2 = state.load_contract(fn2.contract).val
        assert isinstance(callee1, z3.BitVecRef)
        assert isinstance(callee2, z3.BitVecRef)
        call1 = MsgCall(account1, value1, callee1)
        call2 = MsgCall(account2, value2, callee2)
        args1 = []
        args2 = []
        for p in fn1.parameters:
            sort = type_to_sort(p.type)
            arg = z3.Const(unique_name(p.name), sort)
            args1.append(arg)

            p_type = p.type
            if isinstance(p_type, ElementaryType) and p_type.type == "address":
                account1_addrs.append(arg)
        args1 = tuple(args1)

        for p in fn2.parameters:
            sort = type_to_sort(p.type)
            arg = z3.Const(unique_name(p.name), sort)
            args2.append(arg)

            p_type = p.type
            if isinstance(p_type, ElementaryType) and p_type.type == "address":
                account2_addrs.append(arg)
        args2 = tuple(args2)

        t2 = time.time()

        if is_timeout():
            return FunctionPairResult.PAIR_EXECUTION_TIMEOUT

        # attack scenario fn1 -> fn2
        logger.debug("Simulating execution scenario...", scenario="fn1->fn2")
        state_a = state.copy()
        # execute fn1
        application = summary1.apply(
            state_a,
            call1,
            args1,
        )
        # update state
        state_a.apply_storage_writes(application.storage_written)
        # collect profits
        ps1_a = ProfitCollection(account1_addrs, application.revert_condition)
        transfers = self.controller.apply_transfers(
            application.summary.id, application.substitute_strategy
        )
        ps1_a.add_transfer(*transfers)
        # add constraints
        solver.add(*application.constraints)
        logger.debug(
            "Function applied", fn=fn1.canonical_name, time=f"{time.time() - t2:.2f}s"
        )
        t3 = time.time()

        if is_timeout():
            return FunctionPairResult.PAIR_EXECUTION_TIMEOUT

        # execute fn2
        application = summary2.apply(
            state_a,
            call2,
            args2,
        )
        # collect profits
        ps2_a = ProfitCollection(account2_addrs, application.revert_condition)
        transfers = self.controller.apply_transfers(
            application.summary.id, application.substitute_strategy
        )
        ps2_a.add_transfer(*transfers)
        # add constraints
        solver.add(*application.constraints)
        logger.debug(
            "Function applied", fn=fn2.canonical_name, time=f"{time.time() - t3:.2f}s"
        )

        if is_timeout():
            return FunctionPairResult.PAIR_EXECUTION_TIMEOUT

        # attack scenario fn2 -> fn1
        logger.debug("Simulating execution scenario...", scenario="fn2->fn1")
        t4 = time.time()
        state_af = state.copy()
        # execute fn2
        application = summary2.apply(
            state_af,
            call2,
            args2,
        )
        # update state
        state_af.apply_storage_writes(application.storage_written)
        # collect profits
        ps2_af = ProfitCollection(account2_addrs, application.revert_condition)
        transfers = self.controller.apply_transfers(
            application.summary.id, application.substitute_strategy
        )
        ps2_af.add_transfer(*transfers)
        # add constraints
        solver.add(*application.constraints)
        logger.debug(
            "Function applied", fn=fn2.canonical_name, time=f"{time.time() - t4:.2f}s"
        )
        t5 = time.time()

        if is_timeout():
            return FunctionPairResult.PAIR_EXECUTION_TIMEOUT

        # execute fn1
        application = summary1.apply(
            state_af,
            call1,
            args1,
        )
        # collect profits
        ps1_af = ProfitCollection(account1_addrs, application.revert_condition)
        transfers = self.controller.apply_transfers(
            application.summary.id, application.substitute_strategy
        )
        ps1_af.add_transfer(*transfers)
        # add constraints
        solver.add(*application.constraints)
        logger.debug(
            "Function applied", fn=fn1.canonical_name, time=f"{time.time() - t5:.2f}s"
        )

        if is_timeout():
            return FunctionPairResult.PAIR_EXECUTION_TIMEOUT

        self.observer.application_time += time.time() - t2

        # attack property
        solver.add(ps1_a > ps1_af)
        solver.add(ps2_af > ps2_a)

        t6 = time.time()
        logger.debug("Checking vulnerability property...")
        res = solver.check()
        self.observer.solving_time += time.time() - t6
        logger.debug(
            "Vulnerability property checked",
            result=res,
            time=f"{time.time() - t6:.2f}s",
        )

        logger.unbind("fn1", "fn2")

        if res == z3.sat:
            return FunctionPairResult.VULNERABLE
        elif res == z3.unsat:
            return FunctionPairResult.SAFE
        else:
            return FunctionPairResult.SOLVER_TIMEOUT
