from collections import defaultdict

import z3

from engine2.transfer import ResolvedTransfer, Profit
from engine2.value import zero_value, type_to_sort


class ProfitCollection:
    def __init__(self, accounts: list[z3.ExprRef], revert_condition: z3.BoolRef | None):
        self.accounts: set[str] = {str(a) for a in accounts}
        self.revert_condition: z3.BoolRef = revert_condition
        zero = zero_value(type_to_sort("uint"))
        self.profits: defaultdict[str, z3.ExprRef] = defaultdict(lambda: zero)

    def add_transfer(self, *transfers: "ResolvedTransfer"):
        for t in transfers:
            for p in t.profits:
                if any(account in p.account for account in self.accounts):
                    self.add_profit(p)

    def add_profit(self, p: Profit):
        origin = self.profits[p.asset]
        self.profits[p.asset] = origin + p.amount

    def __getitem__(self, item):
        val = self.profits[item]
        if self.revert_condition is not None:
            zero = zero_value(type_to_sort("uint"))
            val = z3.If(self.revert_condition, zero, val)
        return val

    def __gt__(self, other: "ProfitCollection") -> z3.BoolRef:
        cs_base = []
        cs_agile = []
        for asset in set(self.profits.keys()).union(other.profits.keys()):
            if isinstance(self[asset], z3.ArithRef):
                cs_base.append(self[asset] >= other[asset])
                cs_agile.append(self[asset] > other[asset])
            elif isinstance(self[asset], z3.BitVecRef):
                cs_base.append(z3.UGE(self[asset], other[asset]))
                cs_agile.append(z3.UGT(self[asset], other[asset]))
            else:
                raise TypeError(f"Unknown type {type(self[asset])}")
        return z3.And(z3.And(*cs_base), z3.Or(*cs_agile))

    def __ge__(self, other: "ProfitCollection") -> z3.BoolRef:
        cs_base = []
        for asset in set(self.profits.keys()).union(other.profits.keys()):
            if isinstance(self[asset], z3.ArithRef):
                cs_base.append(self[asset] >= other[asset])
            elif isinstance(self[asset], z3.BitVecRef):
                cs_base.append(z3.UGE(self[asset], other[asset]))
            else:
                raise TypeError(f"Unknown type {type(self[asset])}")
        return z3.And(*cs_base)

    def __lt__(self, other):
        return other > self

    def __le__(self, other):
        return other >= self

    def __eq__(self, other):
        cs_base = []
        for asset in set(self.profits.keys()).union(other.profits.keys()):
            cs_base.append(self[asset] == other[asset])
        return z3.And(*cs_base)

    def __ne__(self, other):
        return z3.Not(self == other)
