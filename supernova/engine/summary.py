from typing import Dict, List

import z3

from hfg.flow import *
from lib.assets import AssetTransfer


class FunctionSymbolicSummary(object):
    """
    Function symbolic summary summarizes the following information of a function:
    - return values,
    - call arguments,
    - state assignments,
    - asset transfer
    Using the following values as uninterpreted variable:
    - parameters
    - call return values
    - state variable
    """

    def __init__(self):
        self._returns: Dict[FunctionReturnVariable, List[z3.ExprRef]] = dict()
        self._call_args: Dict[CallArgVariable, List[z3.ExprRef]] = dict()
        self._state_assignments: Dict[StateVariable, List[z3.ExprRef]] = dict()
        self._asset_transfers: Dict[AssetTransfer, List[z3.ExprRef]] = dict()
