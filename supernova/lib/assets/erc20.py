from __future__ import annotations

from typing import List

from slither.slithir.operations import (
    Operation,
    HighLevelCall,
    EventCall,
    LibraryCall,
    InternalCall,
    InternalDynamicCall,
)

from lib.assets.transfer import AssetDefinition, AssetTransfer, THIS, find_event


class ERC20(AssetDefinition):
    function_signatures: List[str] = [
        "name()",
        "symbol()",
        "decimals()",
        "totalSupply()",
        "balanceOf(address)",
        "allowance(address,address)",
        "approve(address,uint256)",
        "increaseAllowance(address,uint256)",
        "decreaseAllowance(address,uint256)",
        "transfer(address,uint256)",
        "transferFrom(address,address,uint256)",
        "safeTransfer(address,address,uint256)",
        "safeTransferFrom(address,address,address,uint256)",
        "_safeTransfer(address,address,uint256)",
    ]
    event_signatures: List[str] = [
        "Transfer(address,address,uint256)",
        "Approval(address,address,uint256)",
    ]

    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if isinstance(op, HighLevelCall) and not isinstance(op, LibraryCall):
            if op.function is None:
                return []
            if op.function.solidity_signature == "transfer(address,uint256)":
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.destination,
                        sender=THIS,
                        receiver=op.arguments[0],
                        token_id=None,
                        amount=op.arguments[1],
                    )
                ]
            elif (
                op.function.solidity_signature
                == "transferFrom(address,address,uint256)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.destination,
                        sender=op.arguments[0],
                        receiver=op.arguments[1],
                        token_id=None,
                        amount=op.arguments[2],
                    )
                ]
        elif isinstance(op, (InternalCall, InternalDynamicCall, LibraryCall)):
            if (
                op.function.solidity_signature
                == "safeTransfer(address,address,uint256)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.arguments[0],
                        sender=THIS,
                        receiver=op.arguments[1],
                        token_id=None,
                        amount=op.arguments[2],
                    )
                ]
            elif (
                op.function.solidity_signature
                == "safeTransferFrom(address,address,address,uint256)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.arguments[0],
                        sender=op.arguments[1],
                        receiver=op.arguments[2],
                        token_id=None,
                        amount=op.arguments[3],
                    )
                ]
            elif (
                op.function.solidity_signature
                == "_safeTransfer(address,address,uint256)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.arguments[0],
                        sender=THIS,
                        receiver=op.arguments[1],
                        token_id=None,
                        amount=op.arguments[2],
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
            # Bug in slither==0.9.1: https://github.com/crytic/slither/issues/1438
            # No event call arguments
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC20",
                    contract=THIS,
                    sender=op.arguments[0],
                    receiver=op.arguments[1],
                    token_id=None,
                    amount=op.arguments[2],
                )
            ]
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        if isinstance(
            op, (HighLevelCall, InternalCall, InternalDynamicCall, LibraryCall)
        ):
            if op.function is None:
                return False
            return op.function.solidity_signature in ERC20.function_signatures
        # TODO handle low level call and assembly call
        return False
