from collections import OrderedDict
from enum import Enum

import z3
from eth_typing import HexStr
from slither.core.declarations import Structure, Contract
from slither.core.solidity_types import (
    ElementaryType,
    UserDefinedType,
    Type,
    MappingType,
    ArrayType,
)
from slither.core.solidity_types.elementary_type import Uint, Int, Byte
from web3 import Web3

symbolic_value_index = 0


def gen_unique_name(prefix: str = "sym") -> str:
    global symbolic_value_index
    name = f"{prefix}_{symbolic_value_index}"
    symbolic_value_index += 1
    return name


def is_signed_type(typ: Type) -> bool:
    assert typ is not None
    if isinstance(typ, ElementaryType):
        return typ.type in Int
    else:
        return False


def type_to_expr(
    typ: Type | list[Type],
    value: str | int | bool = None,
    identifier: str = None,
    zero: bool = False,
) -> z3.ExprRef | list[z3.ExprRef]:
    if isinstance(typ, ElementaryType):
        return elementary_type_to_expr(typ, value, identifier, zero)
    elif isinstance(typ, UserDefinedType):
        return user_defined_type_to_expr(typ, zero)
    elif isinstance(typ, (MappingType, ArrayType)):
        return map_array_type_to_expr(typ, identifier, zero)
    elif isinstance(typ, list):
        return tuple_type_to_expr(typ, identifier, zero)
    else:
        raise NotImplementedError(typ)


def elementary_type_to_expr(
    typ: ElementaryType | str,
    value: str | int | bool = None,
    identifier: str = None,
    zero: bool = False,
) -> z3.BitVecRef | z3.SeqRef:
    """
    Generate a z3 expression based on the elementary type with optionally a constant value.
    :param zero:
    :param typ:
    :param value: value obtained from Constant
    :param identifier: the name of the symbolic value to create
    :return:
    """
    assert isinstance(typ, ElementaryType)

    if value is None and not zero:
        # create a unconstrained symbolic value
        if not typ.is_dynamic and typ.type in Byte + ["address"]:
            sort = z3.BitVecSort(typ.size)
        elif not typ.is_dynamic and typ.type in Uint + Int:
            sort = z3.IntSort()
        elif typ.is_dynamic:
            if typ.type == "string":
                sort = z3.StringSort()
            elif typ.type == "bytes":
                sort = z3.BitVecSort(512)
            else:
                raise ValueError()
        elif typ.type == "bool":
            sort = z3.BoolSort()
        else:
            raise ValueError()

        global symbolic_value_index
        name = identifier if identifier is not None else gen_unique_name()
        symbolic_value_index += 1
        return z3.Const(name, sort)
    else:
        if not typ.is_dynamic and typ.type in Byte + ["address"]:
            if isinstance(value, int):
                val = value
            elif isinstance(value, str):
                val = Web3.toInt(hexstr=HexStr(value))
            elif zero:
                val = 0
            else:
                raise ValueError()
            return z3.BitVecVal(val, typ.size)
        elif not typ.is_dynamic and typ.type in Int + Uint:
            if isinstance(value, int):
                val = value
            elif isinstance(value, str):
                val = Web3.toInt(hexstr=HexStr(value))
            elif zero:
                val = 0
            else:
                raise ValueError()
            return z3.IntVal(val)
        elif typ.is_dynamic:
            if typ.type == "string":
                if isinstance(value, str):
                    val = value
                elif zero:
                    val = ""
                else:
                    raise ValueError()
                return z3.StringVal(val)
            elif typ.type == "bytes":
                # TODO: dynamic bytes needs better handling
                if isinstance(value, str):
                    val = Web3.toInt(hexstr=HexStr(value))
                elif zero:
                    val = 0
                else:
                    raise ValueError()
                return z3.BitVecVal(val, 512)
        elif typ.type == "bool":
            return z3.BoolVal(value) if value is not None else z3.BoolVal(False)
        raise ValueError()


ACCESSOR_MAP = "accessor_map"
DATATYPE_SORT = "datatype_sort"


def user_defined_type_to_expr(
    typ: UserDefinedType,
    zero: bool = True,
) -> z3.DatatypeRef:
    assert isinstance(typ, UserDefinedType)
    global symbolic_value_index
    symbolic_value_index += 1
    if isinstance(typ.type, Enum):
        if zero:
            return z3.IntVal(0)
        else:
            return z3.Int(gen_unique_name(typ.type.name))
        # enums = typ.type.values
        # sort = z3.EnumSort(
        #     typ.type.canonical_name,
        #     enums,
        # )
        # if zero:
        #     return getattr(sort, enums[0])()
        # else:
        #     return z3.Const(gen_unique_name(typ.type.name), sort)
    elif isinstance(typ.type, Structure):
        if ACCESSOR_MAP in typ.type.context and DATATYPE_SORT in typ.type.context:
            sort = typ.type.context[DATATYPE_SORT]
            field_exprs = []
            for field in typ.type.elems_ordered:
                expr = type_to_expr(field.type, zero=zero)
                field_exprs.append(expr)
        else:
            datatype = z3.Datatype(typ.type.canonical_name)
            accessors_map = OrderedDict()
            field_declares = []
            field_exprs = []
            for field in typ.type.elems_ordered:
                expr = type_to_expr(field.type, zero=zero)
                field_exprs.append(expr)
                field_declares.append((field.name, expr.sort()))
            datatype.declare(typ.type.name, *field_declares)
            sort = datatype.create()
            for field in typ.type.elems_ordered:
                accessors_map[field.name] = getattr(sort, field.name)
            typ.type.context[ACCESSOR_MAP] = accessors_map
            typ.type.context[DATATYPE_SORT] = sort
        return sort.constructor(0)(*field_exprs)
    elif isinstance(typ.type, Contract):
        # we treat contract variables just as addresses
        return elementary_type_to_expr(
            ElementaryType("address"),
            identifier=gen_unique_name(typ.type.name),
        )

    else:
        # FIXME: then the type is Enum of another contract,
        # typ.type may be the Enum declaration directly
        if zero:
            return z3.IntVal(0)
        else:
            return z3.Int(gen_unique_name(str(typ.type)))


def map_array_type_to_expr(
    typ: MappingType | ArrayType,
    identifier: str = None,
    zero: bool = True,
) -> z3.ExprRef:
    global symbolic_value_index
    name = identifier if identifier is not None else gen_unique_name()
    symbolic_value_index += 1
    if isinstance(typ, MappingType):
        key_sort = type_to_expr(typ.type_from, zero=zero).sort()
        value_sort = type_to_expr(typ.type_to, zero=zero).sort()
        sort = z3.ArraySort(key_sort, value_sort)
    elif isinstance(typ, ArrayType):
        value_sort = type_to_expr(typ.type, zero=zero).sort()
        sort = z3.ArraySort(z3.IntSort(), value_sort)
    else:
        raise ValueError()
    return z3.Const(name, sort)


def tuple_type_to_expr(
    types: list[Type],
    identifier: str = None,
    zero: bool = True,
) -> list[z3.ExprRef]:
    name = identifier if identifier is not None else gen_unique_name()
    return [
        type_to_expr(t, identifier=f"{name}_{i}", zero=zero)
        for i, t in enumerate(types)
    ]
