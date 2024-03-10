import unittest

from slither.analyses.data_dependency.data_dependency import is_dependent, KEY_SSA

from lib.test_util import TestSourceCode


class SlitherPlayground(unittest.TestCase):
    def test_public_functions_in_super_contract_is_included_in_child(self):
        code = """
        contract A {
            function foo() public {}
        }
        contract B is A {
            function bar() public {}
        }
        """
        with TestSourceCode(code) as slither:
            b = slither.get_contract_from_name("B")[0]
            self.assertEqual(len(b.functions), 2)

    def test_inheritance_property_contains_all_ancestors_including_interfaces(self):
        code = """
        interface L {
            function baz() external;
        }
        contract A {
            function foo() public {}
        }
        contract B is A {
            function bar() public {}
        }
        contract C is B, L {
            function baz() public {}
        }
        """
        with TestSourceCode(code) as slither:
            c = slither.get_contract_from_name("C")[0]
            self.assertEqual(len(c.inheritance), 3)

    def test_low_level_call(self):
        code = """
        contract A {
            function foo() public {
                address(0).call("");
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            self.assertEqual(len(a.functions[0].low_level_calls), 1)

    def test_data_flow(self):
        code = """
        pragma solidity ^0.8.0;

        contract DataDependency {
            uint m;
            mapping(uint=>uint) a;
            uint b;
            Dep dep;

            function setA_1(uint idx, uint _a_) public {
                setA(idx, _a_+1);
            }

            function setA(uint idx, uint _a) public {
                a[idx] = _a + m;
            }

            function setB(uint _b) public {
                uint __b = _b + 1;
                uint _a = getA(_b, __b);
                if (_a == 0) {
                    (uint x1, uint x2) = dep.getX();
                    b = x1 + x2 + __b + a[_b];
                }
            }

            function getA(uint idx, uint y) public view returns (uint) {
                if (y > 10) {
                    assert(y > 0);
                    return a[idx] + y;
                } else {
                    revert();
                }
            }
        }

        contract Dep {
            uint public x;

            function getX() public view returns (uint, uint) {
                return (x, x);
            }
        }
        """
        with TestSourceCode(code) as slither:
            dataDependency = slither.get_contract_from_name("DataDependency")[0]
            setB = dataDependency.get_function_from_signature("setB(uint256)")
            _a = setB.get_local_variable_from_name("_a")
            _b = setB.get_local_variable_from_name("_b")
            a = dataDependency.get_state_variable_from_name("a")
            b = dataDependency.get_state_variable_from_name("b")
            m = dataDependency.get_state_variable_from_name("m")
            self.assertTrue(is_dependent(b, a, setB))
            self.assertFalse(is_dependent(b, m, setB))

    def test_transfer(self):
        code = """
        interface ERC20 {
            function transfer(address to, uint256 value) payable external returns (bool);
        }
        contract A {
            ERC20 token;
            event Transfer(address indexed from, address indexed to, uint256 value);
            function foo() public {
                require(token.transfer(address(0), 1));
                payable(msg.sender).transfer(1);
                payable(address(0)).send(1);
                token.transfer{value: 1}(address(0), 1);
                payable(address(0)).call{value: 1}("");
                assembly {
                    let r := callcode(gas(), 0x0, 1, 0, 0, 0, 0)
                }
                emit Transfer(msg.sender, address(0), 1);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            ops = a.functions[0].slithir_ssa_operations
            self.assertEqual(len(a.functions[0].high_level_calls), 1)

    def test_event(self):
        code = """
        contract A {
            event Foo(uint256 indexed a, uint256 indexed b);
            function foo() public {
                emit Foo(1, 2);
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            self.assertEqual(len(a.functions), 1)

    def test_dynamic_internal_call(self):
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
            self.assertEqual(len(a.functions[0].internal_calls), 1)

    def test_field_sensitivity(self):
        code = """
        contract A {
            struct SS {
                uint[] arr;
            }
            struct S {
                uint x;
                uint[] y;
                mapping(uint=>uint) z;
                SS ss;
            }
            S s;
            SS ss;
            function foo() public {
                s.x = 1 + s.ss.arr[0];
                s.y.push(s.y[0]);
                s.z[1] = s.z[0] + 1;
                s.ss = ss;
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            foo = a.get_function_from_signature("foo()")
            dep = foo.context[KEY_SSA]
            ops = foo.slithir_ssa_operations
            self.assertEqual(len(ops), 4)

    def test_array_init_bug(self):
        code = """
        contract A {
            uint[] arr;
            function foo(uint i) public returns (uint) {
                arr = [1];
                return arr[i];
            }
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_data_flow_1(self):
        code = """
           contract A {
               uint[] arr;
               function foo(uint i) public returns (uint) {
                   arr = [1, 2];
                   return arr[i];
               }
               function bar(uint i) public {
                    arr[i] = 10;
               }
           }
           """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_type_info(self):
        code = """
           contract B {
                function bar(uint i) public {
                    i = i+1;
                }
           }
           contract A {
               function foo(uint i) public {
                  string memory n = type(B).name;
                  uint max = type(uint).max;
               }
           }
           """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_abi_decode(self):
        code = """
            library L {
                enum E { A, B }
            }
            contract A {
                function foo(bytes memory data) public {
                    (L.E x) = abi.decode(data, (L.E));
                    (L.E y, uint z) = abi.decode(data, (L.E, uint));
                    (uint m) = abi.decode(data, (uint));
                }
            }
           """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_loop(self):
        code = """
            contract A {
                function foo() public {
                    uint i = 0;
                    for (uint j = 0; j < 10; j++) {
                        i++;
                    }

                }
            }
           """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_array_push(self):
        code = """
        contract A {
            uint[] arr;
            uint x;
            function foo() public {
                x = arr.push(1);
            }
        }
        """
        with TestSourceCode(code, solc_version="0.6.12") as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_ternary(self):
        code = """
        contract A {
            function foo(uint x) public returns (uint) {
                return (x != 10 ? x > 10 : x < 10) ? 1 : 2;
            }
        }
        """
        with TestSourceCode(code, solc_version="0.6.12") as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_loop(self):
        code = """
        contract A {
            function foo() public {
                uint i = 0;
                while (true) {
                    i++;
                    break;
                }
            }
        }
        """
        with TestSourceCode(code, solc_version="0.6.12") as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)

    def test_try(self):
        code = """
        contract A {
            function foo() public {
                try this.foo() {
                    int a = 1;
                } catch {
                    int x = 1;
                }
                int y = 1;
            }
        }
        """
        with TestSourceCode(code, solc_version="0.6.12") as slither:
            a = slither.get_contract_from_name("A")[0]
            fn = a.functions[0]
            print(fn)


if __name__ == "__main__":
    unittest.main()
