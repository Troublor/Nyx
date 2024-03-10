import unittest

from slither.core.variables.state_variable import StateVariable

from hfg.intra_contract import *
from lib.test_util import TestSourceCode


class IntraContractTest(unittest.TestCase):
    def assertDataFlowFromState(
        self,
        op: Operation,
        state: StateVariable,
        sink_type=IntraProceduralDataFlowSinkSummary,
    ):
        self.assertTrue(DATA_FLOW_SINK_KEY in op.context)
        summaries = filter(
            lambda x: isinstance(x, sink_type),
            op.context[DATA_FLOW_SINK_KEY],
        )
        self.assertTrue(
            any(
                [
                    summary
                    for summary in summaries
                    if any(
                        [
                            x
                            for x in summary.sources["states"]
                            if x.non_ssa_version == state
                        ]
                    )
                ]
            ),
        )

    def assertNotDataFlowFromState(
        self,
        op: Operation,
        state: StateVariable,
        sink_type=IntraProceduralDataFlowSinkSummary,
    ):
        try:
            self.assertDataFlowFromState(op, state, sink_type)
            self.assertFalse(True)
        except Exception as e:
            self.assertIsInstance(e, AssertionError)

    def assertDataFlowFromParameter(
        self,
        op: Operation,
        idx: int,
        sink_type=IntraProceduralDataFlowSinkSummary,
    ):
        self.assertTrue(DATA_FLOW_SINK_KEY in op.context)
        summaries = [
            x for x in op.context[DATA_FLOW_SINK_KEY] if isinstance(x, sink_type)
        ]
        self.assertTrue(
            any(
                [
                    summary
                    for summary in summaries
                    if idx in summary.sources["parameters"]
                ]
            ),
        )

    def assertDataFlowFromCallReturns(
        self,
        op: Operation,
        call: Operation,
        idx: int,
        sink_type=IntraProceduralDataFlowSinkSummary,
    ):
        self.assertTrue(DATA_FLOW_SINK_KEY in op.context)
        summaries = [
            x for x in op.context[DATA_FLOW_SINK_KEY] if isinstance(x, sink_type)
        ]
        self.assertTrue(
            any(
                [
                    summary
                    for summary in summaries
                    if (call, idx) in summary.sources["call_returns"]
                ]
            ),
        )

    def test_data_to_return(self):
        code = """
        interface I {
            function foo(uint x) external returns (uint);
        }
        contract A {
            I i;
            uint a = 1;
            struct S {
                uint[10][10][] arr;
            }
            S s;
            function foo(uint x, S memory ss) public returns (uint) {
                x = x + a + i.foo(x) + s.arr[0][0][0] + ss.arr[0][0][0];
                x *= block.timestamp;
                if (x > 0) {
                    return x;
                } else {
                    return ss.arr[0][0][0];
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256,(uint256[][][]))")
            summarize_intra_procedural_data_flow(foo)
            op = next(
                _op for _op in foo.slithir_ssa_operations if isinstance(_op, Return)
            )
            # flow from state
            state_a = a.get_state_variable_from_name("a")
            state_s = a.get_state_variable_from_name("s")
            self.assertDataFlowFromState(op, state_a, ReturnSinkSummary)
            self.assertDataFlowFromState(op, state_s, ReturnSinkSummary)
            # flow from parameters
            self.assertDataFlowFromParameter(op, 1, ReturnSinkSummary)
            self.assertDataFlowFromParameter(op, 2, ReturnSinkSummary)
            # flow from external call returns
            call_op = next(
                _op
                for _op in foo.slithir_ssa_operations
                if isinstance(_op, HighLevelCall)
            )
            self.assertDataFlowFromCallReturns(op, call_op, 1, ReturnSinkSummary)

    def test_data_to_return_variable(self):
        code = """
        contract A {
            uint a = 1;
            uint b = 1;
            function foo(uint x) public returns (uint y) {
                if (x > 0) {
                    y = x;
                } else {
                    y = x + a;
                    return b + 1;
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            summarize_intra_procedural_data_flow(foo)
            op0 = foo.slithir_ssa_operations[4]
            op1 = next(
                _op for _op in foo.slithir_ssa_operations if isinstance(_op, Return)
            )
            # flow from state
            state_a = a.get_state_variable_from_name("a")
            self.assertNotDataFlowFromState(op1, state_a, ReturnSinkSummary)
            state_b = a.get_state_variable_from_name("b")
            self.assertDataFlowFromState(op1, state_b, ReturnSinkSummary)
            # flow from parameters
            self.assertDataFlowFromParameter(op0, 1, ReturnSinkSummary)

    def test_data_to_state(self):
        code = """
        interface I {
            function foo(uint x) external returns (uint,uint);
        }
        contract A {
            uint a;
            uint x;
            struct S {
                uint[10][10][] arr;
            }
            S s;
            function foo(uint y, S memory ss) public {
                (uint m, uint n) = I(msg.sender).foo(y);
                x = y + 1 + a + m * n;
                s.arr[0][0][0] = x;
                ss.arr[0][0][0] = x;
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256,(uint256[][][]))")
            summarize_intra_procedural_data_flow(foo)
            ops = [
                _op for _op in foo.slithir_ssa_operations if isinstance(_op, Assignment)
            ]
            op0 = ops[0]
            op1 = ops[1]
            # flow from state
            state_a = a.get_state_variable_from_name("a")
            state_x = a.get_state_variable_from_name("x")
            state_s = a.get_state_variable_from_name("s")
            self.assertDataFlowFromState(op0, state_a)
            self.assertDataFlowFromState(op1, state_a)
            self.assertDataFlowFromState(op1, state_x)
            # flow from parameters
            self.assertDataFlowFromParameter(op0, 1)
            self.assertDataFlowFromParameter(op1, 1)
            # flow from external call returns
            call_op = next(
                _op
                for _op in foo.slithir_ssa_operations
                if isinstance(_op, HighLevelCall)
            )
            self.assertDataFlowFromCallReturns(op0, call_op, 1)
            self.assertDataFlowFromCallReturns(op0, call_op, 2)
            self.assertDataFlowFromCallReturns(op1, call_op, 1)
            self.assertDataFlowFromCallReturns(op1, call_op, 2)

    def test_data_from_param_to_condition(self):
        code = """
        contract A {
            function foo(uint x) public {
                uint y = x + block.timestamp;
                require(x >= 100000);
                if (y >= 0) {
                    payable(msg.sender).transfer(y);
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            summarize_intra_procedural_data_flow(foo)
            op_if = next(
                _op for _op in foo.slithir_ssa_operations if isinstance(_op, Condition)
            )
            op_require = next(
                _op
                for _op in foo.slithir_ssa_operations
                if isinstance(_op, SolidityCall) and "require" in _op.function.name
            )
            # flow from parameters
            self.assertDataFlowFromParameter(op_if, 1, ConditionSinkSummary)
            self.assertDataFlowFromParameter(op_require, 1, ConditionSinkSummary)

    def test_data_from_state_to_transfer(self):
        code = """
        interface IERC20 {
            function transfer(address to, uint value) external returns (bool);
        }
        contract A {
            IERC20 token;
            function foo(uint x) public {
                x = block.timestamp + x;
                payable(msg.sender).transfer(x);
                if (x >= 100000) {
                    token.transfer(msg.sender, x);
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            summarize_intra_procedural_data_flow(foo)
            op_transfer = next(
                _op for _op in foo.slithir_ssa_operations if isinstance(_op, Transfer)
            )
            op_token_transfer = next(
                _op
                for _op in foo.slithir_ssa_operations
                if isinstance(_op, HighLevelCall)
            )
            # flow from state
            self.assertDataFlowFromParameter(op_transfer, 1, ProfitSinkSummary)
            self.assertDataFlowFromParameter(op_token_transfer, 1, ProfitSinkSummary)

    def test_data_from_parameter_to_call(self):
        code = """
        interface I {
            function baz(uint x) external returns (uint);
        }
        contract A {
            I i;
            function foo(uint x) public {
                x = block.timestamp + x;
                bar(x);
            }
            function bar(uint x) internal {
                address(i).call{value: x}(abi.encodeWithSignature("baz(uint256)", x));
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo(uint256)")
            bar = a.get_function_from_signature("bar(uint256)")
            summarize_intra_procedural_data_flow(foo)
            summarize_intra_procedural_data_flow(bar)
            op_internal_call = next(
                _op
                for _op in foo.slithir_ssa_operations
                if isinstance(_op, InternalCall)
            )
            op_low_level_call = next(
                _op
                for _op in bar.slithir_ssa_operations
                if isinstance(_op, LowLevelCall)
            )
            # flow from parameters
            self.assertDataFlowFromParameter(op_internal_call, 1, CallArgSinkSummary)
            self.assertDataFlowFromParameter(op_low_level_call, 1, CallArgSinkSummary)

    def test_call_edge(self):
        code = """
        contract A {
            function cal(uint x) public returns (uint) {
                return x + 1;
            }
            function foo() public {
                bar(cal);
            }
            function bar(function(uint) returns (uint) fn) internal {
                uint x = fn(1);
                payable(msg.sender).transfer(x);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo()")
            bar = a.get_function_from_signature(
                "bar(function(uint256) returns(uint256))"
            )
            cal = a.get_function_from_signature("cal(uint256)")
            summarize_intra_procedural_internal_call_edges(foo)
            summarize_intra_procedural_internal_call_edges(bar)
            foo_summary = foo.slithir_ssa_operations[0].context[
                INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY
            ]
            bar_summary = bar.slithir_ssa_operations[1].context[
                INTRA_PROCEDURAL_INTERNAL_CALL_EDGE_KEY
            ]
            self.assertEqual({bar}, foo_summary)
            self.assertEqual({cal}, bar_summary)

    def test_profits(self):
        code = """
        interface ERC20 {
            function transfer(address to, uint value) external returns (bool);
        }
        contract A {
            ERC20 token;
            function foo() public {
                uint x = block.timestamp;
                payable(msg.sender).transfer(x);
                payable(msg.sender).send(x);
                token.transfer(msg.sender, x);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo()")
            summarize_intra_procedural_profits(foo)
            ops = [
                op
                for op in foo.slithir_ssa_operations
                if TRANSFER_KEY in op.context and len(op.context[TRANSFER_KEY]) > 0
            ]
            self.assertEqual(3, len(ops))


if __name__ == "__main__":
    unittest.main()
