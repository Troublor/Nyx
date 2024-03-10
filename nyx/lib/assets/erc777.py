from typing import List

from slither.slithir.operations import Operation, HighLevelCall, EventCall

from lib.assets.transfer import (
    AssetDefinition,
    AssetTransfer,
    THIS,
    BLACKHOLE,
    find_event,
    WHITEHOLE,
)


class ERC777(AssetDefinition):
    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return []
            if op.function.solidity_signature == "send(address,uint256,bytes)":
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC777",
                        contract=op.destination,
                        sender=THIS,
                        receiver=op.arguments[0],
                        token_id=None,
                        amount=op.arguments[1],
                    )
                ]
            elif (
                op.function.solidity_signature
                == "operatorSend(address,address,uint256,bytes,bytes)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC777",
                        contract=op.destination,
                        sender=op.arguments[0],
                        receiver=op.arguments[1],
                        token_id=None,
                        amount=op.arguments[2],
                    )
                ]
            elif op.function.solidity_signature == "burn(uint256,bytes)":
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC777",
                        contract=op.destination,
                        sender=THIS,
                        receiver=BLACKHOLE,
                        token_id=None,
                        amount=op.arguments[0],
                    )
                ]
            elif (
                op.function.solidity_signature
                == "operatorBurn(address,uint256,bytes,bytes)"
            ):
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC777",
                        contract=op.destination,
                        sender=op.arguments[0],
                        receiver=BLACKHOLE,
                        token_id=None,
                        amount=op.arguments[1],
                    )
                ]
        # TODO handle low level call and assembly call
        return []

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        ev = find_event(op)
        if ev is None:
            return []
        if ev.full_name == "Sent(address,address,address,uint256,bytes,bytes)":
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC777",
                    contract=THIS,
                    sender=op.arguments[1],
                    receiver=op.arguments[2],
                    token_id=None,
                    amount=op.arguments[3],
                )
            ]
        elif ev.full_name == "Minted(address,address,uint256,bytes,bytes)":
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC777",
                    contract=THIS,
                    sender=WHITEHOLE,
                    receiver=op.arguments[1],
                    token_id=None,
                    amount=op.arguments[2],
                )
            ]
        elif ev.full_name == "Burned(address,address,uint256,bytes,bytes)":
            return [
                AssetTransfer(
                    op=op,
                    typ="ERC777",
                    contract=THIS,
                    sender=op.arguments[1],
                    receiver=BLACKHOLE,
                    token_id=None,
                    amount=op.arguments[2],
                )
            ]
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        signatures = [
            "name()",
            "symbol()",
            "totalSupply()",
            "balanceOf(address)",
            "granularity()",
            "defaultOperators()",
            "isOperatorFor(address,address)",
            "authorizeOperator(address)",
            "revokeOperator(address)",
            "send(address,uint256,bytes)",
            "operatorSend(address,address,uint256,bytes,bytes)",
            "burn(uint256,bytes)",
            "operatorBurn(address,uint256,bytes,bytes)",
        ]
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return False
            return op.function.solidity_signature in signatures
        else:
            return False
