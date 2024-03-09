from typing import Union

import z3

Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.BitVecRef, z3.SeqRef, z3.DatatypeRef]
