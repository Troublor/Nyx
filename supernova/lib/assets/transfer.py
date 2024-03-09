from __future__ import annotations

from typing import Union, Literal, Optional, List

from slither.core.declarations import Event, SolidityVariable
from slither.core.solidity_types import Type, ElementaryType
from slither.slithir.operations import Operation, EventCall
from slither.slithir.variables.variable import Variable


class PseudoTransferVariable(Variable):
    def __init__(self, name: str, typ: Type):
        super().__init__()
        self.name = name
        self.type = typ


THIS = SolidityVariable("this")
BLACKHOLE = PseudoTransferVariable("blackhole", ElementaryType("address"))
WHITEHOLE = PseudoTransferVariable("whitehole", ElementaryType("address"))


def find_event(op: EventCall) -> Optional[Event]:
    try:
        return next(filter(lambda e: e.name == op.name, op.contract.events))
    except StopIteration:
        return None


class AssetTransfer(object):
    ETHER = "ETHER"
    ERC20 = "ERC20"
    ERC721 = "ERC721"
    ERC777 = "ERC777"
    ERC1155 = "ERC1155"

    """
    Symbolic asset transfer information.
    """

    def __init__(
        self,
        op: Operation,
        typ: Union[
            Literal["ETHER"],
            Literal["ERC20"],
            Literal["ERC721"],
            Literal["ERC777"],
            Literal["ERC1155"],
        ],
        contract: Optional[Variable | SolidityVariable],
        sender: Variable | SolidityVariable,
        receiver: Variable | SolidityVariable,
        token_id: Optional[Variable | SolidityVariable],
        amount: Variable | SolidityVariable,
    ):
        # the SlithIR operation
        self.op: Operation = op

        self.typ: Union[
            Literal["ETHER"],
            Literal["ERC20"],
            Literal["ERC721"],
            Literal["ERC777"],
            Literal["ERC1155"],
        ] = typ

        # the token contract address variable
        # None for ETHER transfer
        self.contract: Optional[Variable | SolidityVariable] = contract

        # from address variable
        self.sender: Variable | SolidityVariable = sender

        # to address variable
        self.receiver: Variable | SolidityVariable = receiver

        # token id variable
        # None for ERC20, ERC777, ETHER transfer
        self.token_id: Optional[Variable | SolidityVariable] = token_id

        # token amount variable
        self.amount: Variable | SolidityVariable = amount


class NotAssetTransferError(Exception):
    pass


class AssetDefinition(object):
    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        pass

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        pass

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        pass
