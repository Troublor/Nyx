from typing import List

from slither.slithir.operations import Operation, HighLevelCall, EventCall

from lib.assets.transfer import AssetDefinition, AssetTransfer, THIS


class WETH9(AssetDefinition):
    @staticmethod
    def resolve_transfer(op: Operation) -> List[AssetTransfer]:
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return []
            if (
                op.function.solidity_signature == "deposit()"
                and op.call_value is not None
            ):
                # TODO: what if deposit via fallback function?
                return [
                    # we don't add ether transfer here since it is handled by Ether class
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.destination,
                        sender=op.destination,
                        receiver=THIS,
                        token_id=None,
                        amount=op.call_value,
                    )
                ]
            elif op.function.solidity_signature == "withdraw(uint256)":
                return [
                    AssetTransfer(
                        op=op,
                        typ="ERC20",
                        contract=op.destination,
                        sender=THIS,
                        receiver=op.destination,
                        token_id=None,
                        amount=op.arguments[0],
                    ),
                    AssetTransfer(
                        op=op,
                        typ="ETHER",
                        contract=None,
                        sender=op.destination,
                        receiver=THIS,
                        token_id=None,
                        amount=op.arguments[0],
                    ),
                ]
            else:
                return []
        else:
            # TODO handle low level call and assembly call
            return []

    @staticmethod
    def resolve_event(op: EventCall) -> List[AssetTransfer]:
        return []

    @staticmethod
    def is_function_call(op: Operation) -> bool:
        if isinstance(op, HighLevelCall):
            if op.function is None:
                return False
            return op.function.solidity_signature in [
                "deposit()",
                "withdraw(uint256)",
            ]
        else:
            return False
