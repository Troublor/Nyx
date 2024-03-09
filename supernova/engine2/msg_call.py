import z3
from slither.core.declarations import SolidityVariable, SolidityVariableComposed

from engine2.variable import Var


class MsgCall:
    def __init__(
        self,
        sender: z3.ExprRef = None,
        value: z3.ExprRef = None,
        this: z3.ExprRef = None,
        origin: z3.ExprRef = None,
    ):
        self.sender = Var(SolidityVariableComposed("msg.sender"), free=True)
        if sender is not None:
            self.sender.val = sender

        self.value = Var(SolidityVariableComposed("msg.value"), free=True)
        if value is not None:
            self.value.val = value

        self.this = Var(SolidityVariable("this"), free=True)
        if this is not None:
            self.this.val = this

        self.origin: Var = Var(SolidityVariableComposed("msg.value"), free=True)
        self.origin.val = self.sender.val
        if origin is not None:
            self.origin.val = origin

    def substitute_strategy(
        self, call: "MsgCall"
    ) -> list[tuple[z3.ExprRef, z3.ExprRef]]:
        return [
            (self.sender.val, call.sender.val),
            (self.value.val, call.value.val),
            (self.this.val, call.this.val),
        ]

    def internal_call(self) -> "MsgCall":
        return self

    def external_call(
        self,
        sender: z3.ExprRef = None,
        value: z3.ExprRef = None,
        this: z3.ExprRef = None,
    ):
        if sender is None:
            sender = self.sender.val

        if value is None:
            value = self.value.val

        if this is None:
            this = self.this.val

        call = MsgCall(sender, value, this, self.origin.val)
        return call
