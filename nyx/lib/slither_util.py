from slither.core.declarations import Contract


class SlithIRDisorder(Exception):
    def __init__(self, msg: str):
        super().__init__(f"Slither IR disorder: {msg}")
        self.msg = msg


def does_inherit(c: Contract, ancestor: Contract):
    """
    Whether one contract inherits from another (transitively).
    Contracts are treated as objects.
    Two contracts with literally the same content are not considered equal.
    This is a reflexive relation.
    :param c:
    :param ancestor:
    :return:
    """
    if c == ancestor:
        return True
    for base in c.inheritance:
        if does_inherit(base, ancestor):
            return True
    return False


def is_compatible(c1: Contract, c2: Contract):
    """
    Whether c1 is compatible to c2.
    (Analogy: c1 is assignable to c2)
    This is a reflexive relation.
    Note that the c2 may or may not be an actual interface.
    Contracts are treated as literal texts.
    If c1 implements the interface c2, or have the subset of public functions, then they are compatible.
    :param c1:
    :param c2:
    :return:
    """
    if c1 == c2:
        # same contract is compatible
        return True
    if does_inherit(c1, c2):
        # inheritance is compatible
        return True
    # compare public function signatures
    return set(c1.functions_signatures) >= set(c2.functions_signatures)
