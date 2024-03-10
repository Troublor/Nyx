import logging
import sys
import traceback

import z3
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations import Function, Contract, FunctionContract, Modifier
from slither.core.solidity_types import ElementaryType
from slither.slithir.operations import (
    Condition,
)
from slither.slithir.variables import TemporaryVariable
from structlog.processors import KeyValueRenderer

from engine2.controller import SummaryController
from engine2.engine import SymEngine
from engine2.msg_call import MsgCall
from engine2.state import State
from engine2.summary import FunctionSummary, StorageChange
from engine2.value import (
    unique_name,
    sort_conversion,
    is_signed_type,
)
from engine2.variable import Var, TupleVar, AbsVar
from lib.log import TRACE_LEVEL
from lib.signal import interrupted
from lib.slither_util import SlithIRDisorder


class FunctionSummaryBuilder(SymEngine):
    def __init__(
        self,
        fn: Function,
        contracts: set[Contract],
        summaries: dict[str, FunctionSummary],
        controller: SummaryController = None,
        state: State | None = None,
        msg_call: MsgCall | None = None,
    ):
        controller = controller if controller is not None else SummaryController()
        state = state if state is not None else State(contracts)
        call = msg_call if msg_call is not None else MsgCall()
        super().__init__(fn, state, msg_call=call, controller=controller)
        self.contracts = contracts
        self.contract = fn.contract if isinstance(fn, FunctionContract) else None

        """ temporary data used to construct the summary """
        self.visited_fns: set[str] = set()
        self.storage_change: StorageChange = StorageChange()
        self.summaries: dict[str, FunctionSummary] = summaries

        # a stack of current executed node of modifiers
        self.modifier_stack: list[
            tuple[Node, set[Node], list[Node], list[bool]]
        ] = list()

        """ Essential data for summary """
        self.summary: FunctionSummary | None = None

    def build(
        self,
        visited_fns: set[str] = None,
        args: tuple[z3.ExprRef, ...] = None,
    ) -> FunctionSummary:
        assert self.summary is None
        self.summary = FunctionSummary(self.function, self)

        # callback
        self.controller.before_summarize(self)

        # generate parameter symbolic values
        if args is not None:
            assert len(args) == len(self.summary.parameters)
            self.summary.parameters = args
        for i, p in enumerate(self.function.parameters):
            pvar = self.env.use(p)
            pvar.val = self.summary.parameters[i]

        self.visited_fns = visited_fns if visited_fns is not None else set()
        self.visited_fns.add(self.summary.id)
        self.summaries[self.summary.id] = self.summary

        # Execute modifiers pre function body part
        # this is done in the execution of function body
        # see self._do_multi_call()

        # Execute function body
        node = self.function.entry_point
        visited = set()
        branching_node_stack: list[Node] = list()
        branch_stack: list[bool] = list()
        self.execute_from(node, visited, branching_node_stack, branch_stack)

        # Execute modifiers post function body part
        while len(self.modifier_stack) > 0:
            (
                node,
                visited,
                branching_node_stack,
                branch_stack,
            ) = self.modifier_stack.pop()
            self.execute_from(node, visited, branching_node_stack, branch_stack)

        # finish execution
        self.visited_fns.remove(self.summary.id)

        # collect return
        self.summary.returns = tuple(
            self.env.use(r).simplified_val
            if self.controller.reuse_function_summary
            else self.env.use(r).val
            for r in self.function.returns
        )

        # collect storage writes
        for contract in self.contracts:
            for state in contract.state_variables:
                svar = self.env.use(state)
                assert isinstance(svar, Var)
                if svar.val is not svar.symbol:
                    # the default value of storage variable is its symbol
                    self.summary.storage_written[(contract, state.name)] = (
                        svar.simplified_val
                        if self.controller.reuse_function_summary
                        else svar.val
                    )

        # collect conditions and constraints
        self.summary.raw_revert_conditions = self.raw_revert_conditions.copy()
        self.summary.raw_constraints = self.raw_constraints.copy()
        self.summary.free_values = self.free_values.copy()

        # callback
        self.controller.after_summarize(self)

        return self.summary

    def execute_from(
        self,
        node: Node,
        visited: set[Node],
        branching_node_stack: list[Node],
        branch_stack: list[bool | int],
    ) -> Node | None:
        """
        Execute from the given node (included).
        :param branching_node_stack:
        :param branch_stack:
        :param visited:
        :param node:
        :return: the next node to execute when the execution suspends (in case of modifier placeholder)
        """

        def trace_log(msg: str, _node: Node | None = None, **contexts):
            payload = msg
            if _node is not None:
                contexts["lines"] = ",".join(
                    str(line) for line in _node.source_mapping.lines
                )
            kv_str = KeyValueRenderer(repr_native_str=False)(
                self.controller.logger, msg, contexts
            )
            if len(kv_str) > 0:
                payload += f" | {kv_str}"
            logging.log(TRACE_LEVEL, payload)

        def step_into_if(_node: Node) -> Node:
            assert _node.type in [NodeType.IF]
            assert len(_node.sons) == 2
            # branching nodes, either IF or IFLOOP
            branching_node_stack.append(_node)
            # get the path condition (true branch)
            last_op = _node.irs[-1]
            assert isinstance(last_op, Condition)
            cond_var = self.env.use(last_op.value)
            cond = cond_var.val
            if not isinstance(cond, z3.BoolRef):
                signed = is_signed_type(cond_var.type)
                cond = sort_conversion(z3.BoolSort(), cond, signed)
            assert isinstance(cond, z3.BoolRef)
            # add the path condition
            self.raw_path_conditions.append(cond)
            # set next node to be the true branch node
            _next_node = _node.sons[0]
            # mark that currently we are in the true branch
            branch_stack.append(True)
            trace_log(f"Step into to true branch of IF node: {_node}", _node)
            return _next_node

        def step_into_loop(_node: Node) -> Node:
            assert _node.type == NodeType.IFLOOP
            assert len(_node.sons) == 2
            # branching node, LOOP
            branching_node_stack.append(_node)
            # set next node to be the loop body node
            _next_node = _node.sons[0]
            # mark that currently we are in the loop body
            branch_stack.append(True)
            trace_log(f"Step into to loop body of LOOP node: {_node}", _node)
            return _next_node

        def step_into_try(_node: Node) -> Node:
            assert _node.type == NodeType.TRY
            assert len(_node.sons) >= 2
            # branching node, TRY
            branching_node_stack.append(_node)
            # set next node to be the try branch node
            _next_node = _node.sons[0]
            # get the revert condition of last external call application
            cond = self.last_application_revert_cond
            assert cond is not None
            # add the path condition (external call does not revert)
            self.raw_path_conditions.append(z3.Not(cond))
            # set next node to be the try branch node
            _next_node = _node.sons[0]
            # mark that currently we are in the try branch
            branch_stack.append(0)
            trace_log(f"Step into to try branch of TRY node: {_node}", _node)
            return _next_node

        def if_backtrace(_next_node: Node | None) -> Node:
            # backtrace if statement
            branch = branch_stack[-1]
            assert isinstance(branch, bool)
            if branch is True:
                # if currently we are in the true branch
                # then switch to the false branch
                branch_stack[-1] = False
                # get the if branching node
                branching_node = branching_node_stack[-1]
                # save if end node
                if _next_node is not None and _next_node.type == NodeType.ENDIF:
                    branching_node.context["end"] = _next_node
                # get the false branch node
                _next_node = branching_node.sons[1]
                # remove the path condition of true branch
                _cond = self.raw_path_conditions.pop()
                # add the path condition of false branch
                self.raw_path_conditions.append(z3.Not(_cond))
                trace_log(
                    f"Backtrace to false branch of IF node: {branching_node}",
                    branching_node,
                )
            else:
                # if currently we are in the false branch
                # then we are done with the branching node
                self.raw_path_conditions.pop()
                branching_node = branching_node_stack.pop()
                branch_stack.pop()
                if _next_node is None or len(_next_node.sons) == 0:
                    # end of function
                    _next_node = None
                else:
                    # workaround for issue Crytic/slither#1797
                    # don't assert number of sons
                    # assert len(_next_node.sons) == 1, _next_node.source_mapping
                    if len(_next_node.sons) == 1:
                        if _next_node.type == NodeType.ENDIF:
                            _next_node = _next_node.sons[0]
                        else:
                            _next_node = branching_node.context.get("end", _next_node)
                            if _next_node.type in [NodeType.BREAK, NodeType.CONTINUE]:
                                _next_node = loop_backtrace(_next_node)
                            else:
                                _next_node = _next_node.sons[0]
                    else:
                        # workaround for issue Crytic/slither#1797
                        # generate a dummy branching node
                        # noinspection PyProtectedMember
                        dummy_node = Node(
                            NodeType.IF,
                            self.function._counter_nodes,
                            _next_node.scope,
                            _next_node.file_scope,
                        )
                        # noinspection PyProtectedMember
                        self.function._counter_nodes += 1
                        dummy_node.set_function(self.function)
                        dummy_node.source_mapping = _next_node.source_mapping
                        cond_variable = TemporaryVariable(dummy_node)
                        cond_variable.type = ElementaryType("bool")
                        cond_op = Condition(cond_variable)
                        dummy_node.irs.append(cond_op)
                        dummy_node.add_father(_next_node)
                        dummy_node.set_sons(_next_node.sons)
                        return dummy_node
                trace_log(
                    f"Backtrace to end of IF node: {branching_node}", branching_node
                )
            return _next_node

        def try_backtrace(_next_node: Node | None) -> Node:
            branch = branch_stack[-1]
            assert isinstance(branch, int)
            assert branching_node_stack[-1].type == NodeType.TRY
            branching_node = branching_node_stack[-1]
            total_branches = len(branching_node.sons)
            if branching_node.sons[-1].type != NodeType.CATCH:
                # this is the node after the try-catch block
                branching_node.context["end"] = branching_node.sons[-1]
                total_branches -= 1
            # noinspection PyUnreachableCode
            # if branch < total_branches - 1:
            if False:  # ignore catch branches
                # there are still other catch branches
                # switch to the next catch branch
                if branch == 0:
                    # the previous branch was the try branch
                    # get the path condition of the try branch (external call does not revert)
                    _cond = self.raw_path_conditions.pop()
                    # add the path condition of the catch branch (external call reverts)
                    self.raw_path_conditions.append(z3.Not(_cond))
                else:
                    # the previous branch was a catch branch
                    # the path condition of the catch branch is already added
                    pass
                branch_stack[-1] = branch + 1
                _next_node = branching_node.sons[branch + 1]
                trace_log(
                    f"Backtrace to {branch + 1}th catch branch of TRY node: {branching_node}",
                    branching_node,
                )
            else:
                # we are done with the try-catch branching node
                self.raw_path_conditions.pop()
                branching_node = branching_node_stack.pop()
                branch_stack.pop()
                if _next_node is None or len(_next_node.sons) == 0:
                    # end of function
                    _next_node = None
                else:
                    # workaround for issue Crytic/slither#1797
                    # don't assert number of sons
                    # assert len(_next_node.sons) == 1, _next_node.source_mapping
                    _next_node = branching_node.context.get("end", _next_node)
                    if _next_node in [NodeType.BREAK, NodeType.CONTINUE]:
                        _next_node = loop_backtrace(_next_node)
                    else:
                        _next_node = _next_node.sons[0]
                trace_log(
                    f"Backtrace to end of TRY node: {branching_node}", branching_node
                )
            return _next_node

        def loop_backtrace(_next_node: Node | None) -> Node:
            # backtrace loop
            branch = branch_stack[-1]
            assert isinstance(branch, bool)
            assert branch is True
            # currently we are in side the loop
            # then opt out of the loop
            branch_stack.pop()
            branching_node = branching_node_stack.pop()
            _next_node = branching_node.sons[1]
            # remove the path condition of the loop
            # _cond = self.raw_path_conditions.pop()
            trace_log(
                f"Backtrace to false branch of IF node: {branching_node}",
                branching_node,
            )
            return _next_node

        def backtrace(_next_node: Node | None) -> Node:
            # node is a merging node
            branch = branch_stack[-1]
            branching_node = branching_node_stack[-1]
            if isinstance(branch, bool):
                if branching_node.type == NodeType.IF:
                    return if_backtrace(_next_node)
                elif branching_node.type == NodeType.IFLOOP:
                    return loop_backtrace(_next_node)
                else:
                    raise NotImplementedError(
                        f"Unsupported branching node type: {branching_node.type}"
                    )
            elif isinstance(branch, int):
                return try_backtrace(_next_node)
            else:
                raise ValueError(f"Unexpected branch type: {type(branch)}")

        def should_backtrace(_next_node: Node | None) -> bool:
            if _next_node is None and len(branching_node_stack) > 0:
                # node will exit the current function and there are still unvisited branches
                return True
            elif _next_node is not None and _next_node.type == NodeType.ENDIF:
                # merge node of IF statement
                assert len(branching_node_stack) > 0
                return True
            elif _next_node is not None and _next_node.type in [
                NodeType.BREAK,
                NodeType.CONTINUE,
            ]:
                # end of loop
                return True
            elif (
                _next_node is not None
                and _next_node.type != NodeType.ENDIF
                and _next_node in visited
            ):
                # merge node of loops
                assert len(branching_node_stack) > 0
                return True
            else:
                return False

        def execute_node(_node: Node):
            if _node in visited:
                # don't re-visit same nodes
                return
            visited.add(_node)

            if _node.type == NodeType.TRY:
                # facilitate assertions
                self.last_application_revert_cond = None

            if _node.type == NodeType.THROW:
                # add revert condition
                cond = self.path_condition
                if cond is None:
                    cond = z3.BoolVal(True)
                self.raw_revert_conditions.append(cond)

            trace_log(f"Executing node: {_node}", _node)
            for op in _node.irs:
                if interrupted():
                    return
                try:
                    trace_log(f"Executing op: {op}", _node)
                    self.execute_operation(op)
                except TimeoutError as e:
                    raise e
                except SlithIRDisorder as e:
                    self.controller.logger.warn(
                        "Disorder in SlithIR",
                        op=str(op),
                        node=str(_node),
                        fn=str(self.function),
                        line=",".join(map(str, _node.source_mapping.lines)),
                        file=_node.source_mapping.filename.absolute,
                        msg=e.msg,
                    )
                except Exception as e:
                    self.controller.logger.error(
                        "Error while executing operation",
                        op=str(op),
                        node=str(_node),
                        fn=str(self.function),
                        line=",".join(map(str, _node.source_mapping.lines)),
                        file=_node.source_mapping.filename.absolute,
                        err=e,
                    )
                    sys.stderr.write(traceback.format_exc())

        def should_suspend(_node: Node) -> bool:
            # suspend execution in modifier
            return _node.type == NodeType.PLACEHOLDER

        def suspend(_node: Node) -> Node | None:
            assert isinstance(_node.function, Modifier)
            trace_log(f"Suspend execution at node: {_node}", _node)
            # suspend execution and push the next node to modifier stack
            if len(_node.sons) > 0:
                assert len(_node.sons) == 1
                _next_node = _node.sons[0]
                return _next_node
            else:
                return None

        if node.type == NodeType.ENTRYPOINT:
            trace_log(
                f"Start execution: {self.function.canonical_name}",
                line=node.source_mapping.start,
                file=self.function.source_mapping.filename.absolute,
            )
        else:
            trace_log(
                f"Resume execution: {self.function.canonical_name}",
                line=node.source_mapping.start,
                file=self.function.source_mapping.filename.absolute,
            )

        while node:
            if should_suspend(node):
                return suspend(node)

            if interrupted():
                return None

            execute_node(node)

            if len(node.sons) == 0:
                # no more nodes to execute
                next_node = None
            elif len(node.sons) == 1:
                # only one node to execute
                # no branching
                next_node = node.sons[0]
            else:
                if node.type in [NodeType.IF]:
                    next_node = step_into_if(node)
                elif node.type in [NodeType.IFLOOP]:
                    next_node = step_into_loop(node)
                elif node.type == NodeType.TRY:
                    next_node = step_into_try(node)
                else:
                    raise Exception(f"Invalid node: {node}")

            while should_backtrace(next_node):
                next_node = backtrace(next_node)
            node = next_node

        trace_log(
            f"Finish execution: {self.function.canonical_name}",
            line=self.function.source_mapping.start,
            file=self.function.source_mapping.filename.absolute,
        )
        return None

    """ common actions """

    def _do_call(
        self,
        result: AbsVar | None,
        fn: Function,
        state: State,
        msg_call: MsgCall,
        args: tuple[z3.ExprRef, ...],
    ):
        if (
            fn.canonical_name in self.visited_fns  # recursion
            or not fn.is_implemented  # not implemented function
        ):
            self.last_application_revert_cond = z3.BoolVal(False)
            return

        summary = self._do_summarize_fn(fn, state, msg_call, args)
        if self.controller.reuse_function_summary:
            application = summary.apply(
                state,
                msg_call,
                args,
            )
            (
                storage_written,
                returns,
                revert_cond,
                constraints,
                free_values,
            ) = (
                application.storage_written,
                application.returns,
                application.revert_condition,
                application.constraints,
                application.free_values,
            )
            self.last_application_revert_cond = application.revert_condition
        else:
            (
                storage_written,
                returns,
                revert_cond,
                constraints,
                free_values,
            ) = (
                summary.storage_written,
                summary.returns,
                summary.revert_condition,
                summary.constraints,
                summary.free_values,
            )
            self.last_application_revert_cond = summary.revert_condition

        # storage merge
        self.storage_change.merge(storage_written, self.path_condition)
        self.state.apply_storage_writes(storage_written, self.path_condition)

        # assign return values
        if result is not None:
            if len(returns) == 1:
                result.assign(returns[0], self.path_condition)
            else:
                assert isinstance(result, TupleVar)
                result.assign(returns, self.path_condition)

        # add revert condition
        if revert_cond is not None:
            p_cond = self.path_condition
            if p_cond is None:
                self.raw_revert_conditions.append(revert_cond)
            else:
                r_cond = z3.If(p_cond, revert_cond, z3.BoolVal(False))
                self.raw_revert_conditions.append(r_cond)

        # extend constraints
        self.raw_constraints.extend(constraints)

        # extend free values
        self.free_values.extend(free_values)

    def _do_register_modifier(self, modifier: Modifier):
        visited = set()
        branching_node_stack: list[Node] = list()
        branch_stack: list[bool] = list()
        node = modifier.entry_point
        next_node = self.execute_from(node, visited, branching_node_stack, branch_stack)
        if next_node is not None:
            self.modifier_stack.append(
                (next_node, visited, branching_node_stack, branch_stack)
            )

    def _do_summarize_fn(
        self,
        fn: Function,
        state: State = None,
        msg_call: MsgCall = None,
        args: tuple[z3.ExprRef, ...] = None,
    ) -> "FunctionSummary":
        # In reuse_function_summary mode, we will generate a function summary using fresh state,
        # and then apply the summary to the current state
        # If not in reuse_function_summary mode, we will generate a function summary using the current state,
        # and the summary should only be reused later.
        if self.controller.reuse_function_summary:
            if fn.canonical_name in self.summaries:
                return self.summaries[fn.canonical_name]

        builder = FunctionSummaryBuilder(
            fn,
            contracts=self.state.all_contracts,
            summaries=self.summaries,
            controller=self.controller,
            state=None if self.controller.reuse_function_summary else state,
            msg_call=None if self.controller.reuse_function_summary else msg_call,
        )
        summary = builder.build(
            self.visited_fns,
            args=None if self.controller.reuse_function_summary else args,
        )
        return summary
