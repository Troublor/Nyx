import unittest

from nyx.lib.slither_util import is_compatible
from nyx.lib.test_util import TestSourceCode


class SlitherUtil(unittest.TestCase):
    def test_is_compatible_inheritance(self):
        code = """
        contract A {
            function foo() public {}
        }
        contract B is A {
            function bar() public {}
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            b = slither.get_contract_from_name("B")[0]
            self.assertFalse(is_compatible(a, b))
            self.assertTrue(is_compatible(b, a))

    def test_is_compatiable_function_match(self):
        code = """
        interface A {
            function foo() external;
        }
        interface B {
            function foo() external;
            function bar() external;
        }
        contract C {
            function foo() public {}
        }
        """
        with TestSourceCode(code) as slither:
            a = slither.get_contract_from_name("A")[0]
            b = slither.get_contract_from_name("B")[0]
            c = slither.get_contract_from_name("C")[0]
            self.assertTrue(is_compatible(c, a))
            self.assertFalse(is_compatible(c, b))


if __name__ == "__main__":
    unittest.main()
