import unittest

import z3
from slither.core.declarations import FunctionContract
from slither.core.solidity_types import ElementaryType

from engine.env import Env
from engine.executor import FunctionExecutor
from engine.sym_value import type_to_expr
from lib.test_util import TestSourceCode


class FunctionExecutorTest(unittest.TestCase):
    def test_simple_arith_op(self):
        code = """
        contract A {
            uint c = 1;
            function f(uint a) public returns (uint r) {
                uint b = 2;
                uint d = a + b + c;
                return d;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            fn = slither.contracts[0].functions[0]
            state = Env.from_slither(slither, fn)
            exe = FunctionExecutor(fn, state)
            a = type_to_expr(ElementaryType("uint256"), identifier="a")
            r = exe.execute(a)
            self.assertIsInstance(r.returns[0], z3.ExprRef)
            print(r.returns)
            z3.solve(r.returns[0] == 10)

    def test_struct(self):
        code = """
        contract A {
            struct S {
                uint a;
                uint[] b;
            }
            S s;
            mapping(uint => uint) map;
            function f(uint a) public returns (uint, uint) {
                s.a = a;
                uint[] memory b_arr;
                b_arr[0] = 2;
                S memory ss = S(a, b_arr);
                return (s.a + ss.b[0] + map[1], ss.b[0]);
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            fn = slither.contracts[0].functions[0]
            state = Env.from_slither(slither, fn)
            exe = FunctionExecutor(fn, state)
            a = type_to_expr(ElementaryType("uint256"), identifier="a")
            r = exe.execute(a)
            self.assertIsInstance(r.returns[0], z3.ExprRef)
            self.assertIsInstance(r.returns[1], z3.ExprRef)
            print(r.returns)
            z3.solve(r.returns[0] == 10)
            z3.solve(r.returns[1] == 9)

    def test_internal_call(self):
        code = """
        contract A {
            uint c = 1;
            function f(uint a) public returns (uint r) {
                uint b = 2;
                uint d = a + b + c;
                return d;
            }
            function g(uint a) public returns (uint r) {
                uint b = 2;
                uint d = a + f(b);
                h(d);
                return d;
            }
            function h(uint a) public returns (uint r) {
                payable(address(msg.sender)).transfer(address(this).balance);
                bool b = payable(msg.sender).send(100);
                return a;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            f = c.get_function_from_signature("f(uint256)")
            g = c.get_function_from_signature("g(uint256)")
            h = c.get_function_from_signature("h(uint256)")
            assert isinstance(g, FunctionContract)
            state = Env.from_slither(slither, g)
            exe = FunctionExecutor(g, state)
            a = type_to_expr(ElementaryType("uint256"), identifier="a")
            r = exe.execute(a)
            self.assertIsInstance(r.returns[0], z3.ExprRef)
            print(r.returns)
            z3.solve(r.returns[0] == 10)

    def test_if_statement(self):
        code = """
        contract A {
            function foo(uint a) public returns (bool) {
                if (a > 100) {
                    return true;
                } else if (a > 0) {
                    return false;
                } else {
                    revert();
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo(uint256)")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            a = type_to_expr(ElementaryType("uint256"), identifier="a")
            r = exe.execute(a)
            self.assertIsInstance(r.returns[0], z3.BoolRef)
            print(r.returns)
            z3.solve(r.returns[0] == True)
            z3.solve(r.returns[0] == False)
            z3.solve(r.revert_condition)

    def test_multi_transaction(self):
        code = """
        contract A {
            uint x;
            function foo(uint a) public returns (bool) {
                if (a > 100) {
                    x -= a / 2;
                    return true;
                } else if (!(a < 0)) {
                    x -= a;
                    return false;
                } else {
                    revert();
                }
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo(uint256)")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            a = type_to_expr(ElementaryType("uint256"), identifier="a")
            b = type_to_expr(ElementaryType("uint256"), identifier="b")
            exe.execute(a)
            exe.execute(b)
            x = state.access_var(c.state_variables[0])
            print(x)
            z3.solve(x == 20)

    def test_external_call(self):
        code = """
        contract A {
            uint x;
            function foo(uint a) public returns (uint) {
                return a + x / 2;
            }

            function setX(uint _x) public {
                x = _x;
            }
        }
        contract B {
            A contractA;
            function bar(int b) public returns (int) {
                contractA.setX(uint(b));
                uint r = contractA.foo(100);
                return int(r);
            }
        }
        """
        with TestSourceCode(code) as slither:
            contractA = slither.get_contract_from_name("A")[0]
            contractB = slither.get_contract_from_name("B")[0]
            bar = contractB.get_function_from_signature("bar(int256)")
            arg = type_to_expr(ElementaryType("int256"), identifier="arg")
            state = Env.from_slither(slither, bar)
            exe = FunctionExecutor(bar, state)
            r = exe.execute(arg)
            print(r)
            z3.solve(r.returns[0] == 101)

    def test_array_init(self):
        code = """
        contract A {
            int[] arr;
            function foo(uint i) public returns (int) {
                arr = [int(1),2,3,4];
                arr.push(5);
                arr.pop();
                delete arr[3];
                int[3] memory fa = [int(1), 2, 3];
                require(i < arr.length);
                return arr[i];
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo(uint256)")
            arg = type_to_expr(ElementaryType("int256"), identifier="arg")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute(arg)
            print(r.returns)
            z3.solve(r.returns[0] == 5)

    def test_low_level_call(self):
        code = """
        contract A {
            address addr;
            function foo(bytes memory data) public returns (bool, bytes memory) {
                (bool r, bytes memory ret) = addr.call{value: 1}(data);
                return (r, ret);
            }
        }
        """

        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo(bytes)")
            arg = type_to_expr(ElementaryType("bytes"), identifier="data")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute(arg)
            print(r.returns)
            z3.solve(r.returns[0] == True)

    def test_new_array(self):
        code = """
        contract A {
            function foo() public returns (uint) {
                uint[] memory arr = new uint[](2);
                return 0;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo()")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute()
            print(r.returns)
            z3.solve(r.returns[0] == True)

    def test_new_contract(self):
        code = """
        contract A {
            function foo(uint y) public returns (uint) {
                B b = new B();
                b.setX(y);
                return b.x();
            }
        }
        contract B {
            uint public x;
            function setX(uint _x) public {
                x = _x;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo(uint256)")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            arg = type_to_expr(ElementaryType("uint"), identifier="arg")
            r = exe.execute(arg)
            print(r.returns)
            z3.solve(r.returns[0] == 100)

    def test_new_elementary(self):
        code = """
        contract A {
            function foo() public returns (uint) {
                uint x = new x();
                return x;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo()")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute()
            print(r.returns)
            z3.solve(r.returns[0] == True)

    def test_unary(self):
        code = """
        contract A {
            function foo() public returns (uint,uint) {
                uint x = 0;
                uint y = --x;
                y = ++x;
                x = y--;
                x = y++;
                return (x, y);
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo()")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute()
            print(r.returns)
            z3.solve(r.returns[0] == True)

    def test_new_array(self):
        code = """
        contract A {
            function foo() public returns (uint) {
                uint[] memory arr = new uint[](2);
                return 0;
            }
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.contracts[0]
            foo = c.get_function_from_signature("foo()")
            state = Env.from_slither(slither, foo)
            exe = FunctionExecutor(foo, state)
            r = exe.execute()
            print(r.returns)
            z3.solve(r.returns[0] == True)


if __name__ == "__main__":
    unittest.main()
