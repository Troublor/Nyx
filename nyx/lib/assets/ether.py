from typing import List

from slither.slithir.operations import (
    Operation,
    Transfer,
    Send,
    HighLevelCall,
    LowLevelCall,
    SolidityCall,
    EventCall,
    InternalCall,
    InternalDynamicCall,
    LibraryCall,
)

from lib.assets.transfer import AssetDefinition, AssetTransfer, THIS


class Ether(AssetDefinition):
    function_signatures: List[str] = [
        "safeTransferETH(address,uint256)",
    ]

    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if (
            isinstance(op, (Transfer, Send, HighLevelCall, LowLevelCall))
            and not isinstance(op, LibraryCall)
            and op.call_value is not None
        ):
            return [
                AssetTransfer(
                    op=op,
                    typ="ETHER",
                    contract=None,
                    sender=THIS,
                    receiver=op.destination,
                    token_id=None,
                    amount=op.call_value,
                )
            ]
        elif isinstance(op, SolidityCall) and op.function.full_name in [
            "call(uint256,uint256,uint256,uint256,uint256,uint256,uint256)",
            "callcode(uint256,uint256,uint256,uint256,uint256,uint256,uint256)",
        ]:
            return [
                AssetTransfer(
                    op=op,
                    typ="ETHER",
                    contract=None,
                    sender=THIS,
                    receiver=op.arguments[1],
                    token_id=None,
                    amount=op.arguments[2],
                )
            ]
        elif isinstance(op, (InternalCall, InternalDynamicCall, LibraryCall)):
            if op.function.solidity_signature == "safeTransferETH(address,uint256)":
                return [
                    AssetTransfer(
                        op=op,
                        typ="ETHER",
                        contract=None,
                        sender=THIS,
                        receiver=op.arguments[0],
                        token_id=None,
                        amount=op.arguments[1],
                    )
                ]
        return []

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        if isinstance(
            op, (HighLevelCall, InternalCall, InternalDynamicCall, LibraryCall)
        ):
            if op.function is None:
                return False
            return op.function.solidity_signature in Ether.function_signatures
        # TODO handle low level call and assembly call
        return False
