from typing import List

from slither.slithir.operations import Operation, HighLevelCall, EventCall

from lib.assets.transfer import AssetDefinition, AssetTransfer, find_event, THIS


class ERC1155(AssetDefinition):
    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return []
            if op.function.solidity_signature in [
                "safeTransferFrom(address,address,uint256,uint256,bytes)",
                # FIXME: unfold batch transfer
                "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)",
            ]:
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC1155",
                        contract=op.destination,
                        sender=op.arguments[0],
                        receiver=op.arguments[1],
                        token_id=op.arguments[2],
                        amount=op.arguments[3],
                    )
                ]
        # TODO handle low level call and assembly call
        return []

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        ev = find_event(op)
        if ev is None:
            return []
        if ev.full_name in [
            "TransferSingle(address,address,address,uint256,uint256)",
            # FIXME: unfold batch transfer
            "TransferBatch(address,address,address,uint256[],uint256[])",
        ]:
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC1155",
                    contract=THIS,
                    sender=op.arguments[1],
                    receiver=op.arguments[2],
                    token_id=op.arguments[3],
                    amount=op.arguments[4],
                )
            ]
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        signatures = [
            "balanceOf(address,uint256)",
            "balanceOfBatch(address[],uint256[])",
            "setApprovalForAll(address,bool)",
            "isApprovedForAll(address,address)",
            "safeTransferFrom(address,address,uint256,uint256,bytes)",
            "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)",
        ]
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return False
            return op.function.solidity_signature in signatures
        else:
            return False
