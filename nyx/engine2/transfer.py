from copy import copy
from typing import Union, Literal, TYPE_CHECKING

import z3
from slither.slithir.operations import Operation

from engine2.value import zero_value, type_to_sort, sort_conversion
from lib.assets import AssetTransfer

if TYPE_CHECKING:
    from engine2.env import Env


class Profit:
    def __init__(
        self, account: z3.BitVecRef, amount: z3.ArithRef | z3.BitVecRef, asset: str
    ):
        self.account: str = str(account)
        self.amount: z3.ArithRef | z3.BitVecRef = amount
        self.asset: str = asset


class ResolvedTransfer(object):
    """
    Symbolic asset transfer information.
    """

    def __init__(
        self,
        env: "Env",
        asset_transfer: AssetTransfer,
        path_condition: z3.BoolRef | None,
    ):
        self.path_condition: z3.BoolRef | None = path_condition
        # the SlithIR operation
        self.op: Operation = asset_transfer.op

        self.typ: Union[
            Literal["ETHER"],
            Literal["ERC20"],
            Literal["ERC721"],
            Literal["ERC777"],
            Literal["ERC1155"],
        ] = asset_transfer.typ

        # the token contract address variable
        # None for ETHER transfer
        if asset_transfer.contract is None:
            self.contract = None
        else:
            c = env.use(asset_transfer.contract)
            self.contract = c.val

        # from address variable
        sender = env.use(asset_transfer.sender)
        val = sender.val
        assert isinstance(val, z3.BitVecRef)
        self.sender: z3.BitVecRef = val

        # to address variable
        receiver = env.use(asset_transfer.receiver)
        val = receiver.val
        assert isinstance(val, z3.BitVecRef)
        self.receiver = val

        # token id variable
        # None for ERC20, ERC777, ETHER transfer
        if asset_transfer.token_id is None:
            self.token_id = None
        else:
            token_id = env.use(asset_transfer.token_id)
            self.token_id = token_id.val

        # token amount variable
        amount = env.use(asset_transfer.amount)
        val = amount.val
        assert isinstance(val, (z3.ArithRef, z3.BitVecRef))
        self.amount = val

    def simplify(self) -> None:
        self.contract = (
            z3.simplify(self.contract) if self.contract is not None else None
        )
        self.sender = z3.simplify(self.sender)
        self.receiver = z3.simplify(self.receiver)
        self.token_id = (
            z3.simplify(self.token_id) if self.token_id is not None else None
        )
        self.amount = z3.simplify(self.amount)

    def substitute(
        self, strategy: list[tuple[z3.ExprRef, z3.ExprRef]]
    ) -> "ResolvedTransfer":
        cp = copy(self)
        if cp.path_condition is not None:
            cp.path_condition = z3.substitute(cp.path_condition, *strategy)
        if cp.contract is not None:
            cp.contract = z3.substitute(cp.contract, *strategy)
        cp.sender = z3.substitute(cp.sender, *strategy)
        cp.receiver = z3.substitute(cp.receiver, *strategy)
        if cp.token_id is not None:
            cp.token_id = z3.substitute(cp.token_id, *strategy)
        cp.amount = z3.substitute(cp.amount, *strategy)
        return cp

    @property
    def profits(self) -> list[Profit]:
        zero = zero_value(type_to_sort("uint"))
        assert isinstance(zero, (z3.ArithRef, z3.BitVecRef))
        profits = []
        if self.typ == "ETHER":
            asset = "ETHER"
        elif self.typ == "ERC20":
            asset = str(self.contract)
        elif self.typ == "ERC721":
            asset = str(self.contract)
        elif self.typ == "ERC777":
            asset = str(self.contract)
        elif self.typ == "ERC1155":
            asset = str(self.contract)
        else:
            raise ValueError()

        amount = sort_conversion(zero.sort(), self.amount, False)
        if self.path_condition is not None:
            amount = z3.If(self.path_condition, amount, zero)
        profits.append(Profit(self.sender, zero - amount, asset))
        profits.append(Profit(self.receiver, amount, asset))
        return profits

    def __str__(self):
        return f"{self.typ} {self.contract} {self.sender} {self.receiver} {self.token_id} {self.amount}"
