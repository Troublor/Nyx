from typing import List

from slither.slithir.operations import Operation, EventCall, HighLevelCall
from slither.slithir.variables import Constant

from lib.assets.transfer import AssetDefinition, AssetTransfer, THIS, find_event


class ERC721(AssetDefinition):
    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return []
            if op.function.solidity_signature in [
                "safeTransferFrom(address,address,uint256)",
                "safeTransferFrom(address,address,uint256,bytes)",
                "transferFrom(address,address,uint256)",
            ]:
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC721",
                        contract=op.destination,
                        sender=op.arguments[0],
                        receiver=op.arguments[1],
                        token_id=op.arguments[2],
                        amount=Constant("1"),
                    )
                ]
        # TODO handle low level call and assembly call
        return []

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        ev = find_event(op)
        if ev is None:
            return []
        if ev.full_name == "Transfer(address,address,uint256)":
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC721",
                    contract=THIS,
                    sender=op.arguments[0],
                    receiver=op.arguments[1],
                    token_id=op.arguments[2],
                    amount=Constant("1"),
                )
            ]
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        signatures = [
            "balanceOf(address)",
            "ownerOf(uint256)",
            "safeTransferFrom(address,address,uint256)",
            "safeTransferFrom(address,address,uint256,bytes)",
            "transferFrom(address,address,uint256)",
            "approve(address,uint256)",
            "setApprovalForAll(address,bool)",
            "getApproved(uint256)",
            "isApprovedForAll(address,address)",
        ]
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return False
            return op.function.solidity_signature in signatures
        else:
            # TODO handle low level call and assembly call
            return False
