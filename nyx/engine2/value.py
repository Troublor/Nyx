from collections import OrderedDict

import z3
from slither.core.declarations import Enum, Structure, Contract
from slither.core.solidity_types import *
from slither.core.solidity_types.elementary_type import Uint, Int, Byte
from slither.slithir.operations import Operation, Call

symbolic_value_index = 0

# sort name to structure declaration
structures: dict[str, Structure] = dict()


def zero_value(sort: z3.SortRef) -> z3.ExprRef:
    if isinstance(sort, z3.ArithSortRef):
        if sort.is_int():
            return z3.IntVal(0)
        elif sort.is_real():
            return z3.RealVal(0)
        else:
            raise ValueError(sort)
    elif isinstance(sort, z3.BitVecSortRef):
        return z3.BitVecVal(0, sort.size())
    elif isinstance(sort, z3.SeqSortRef):
        return z3.StringVal("")
    elif isinstance(sort, z3.BoolSortRef):
        return z3.BoolVal(False)
    elif isinstance(sort, z3.ArraySortRef):
        return z3.K(sort.domain(), zero_value(sort.range()))
    elif isinstance(sort, z3.DatatypeSortRef):
        assert get_sort_name(sort) in structures
        structure = structures[get_sort_name(sort)]
        fields = []
        for var in structure.elems_ordered:
            f_sort = type_to_sort(var.type)
            f_value = zero_value(f_sort)
            fields.append(f_value)
        return sort.constructor(0)(*fields)
    else:
        raise ValueError(sort)


def sort_value(
    value: int | float | str | bool | dict,
    sort: z3.SortRef,
) -> z3.ExprRef:
    if isinstance(sort, z3.ArithSortRef):
        assert isinstance(value, (int, float))
        if sort.is_int():
            return z3.IntVal(value)
        elif sort.is_real():
            return z3.RealVal(value)
        else:
            raise ValueError(sort)
    elif isinstance(sort, z3.BitVecSortRef):
        if isinstance(value, int):
            return z3.BitVecVal(value, sort.size())
        elif isinstance(value, bytes):
            assert len(value) * 8 <= sort.size()
        else:
            raise ValueError(sort, value)
    elif isinstance(sort, z3.SeqSortRef):
        assert isinstance(value, str)
        return z3.StringVal(value)
    elif isinstance(sort, z3.BoolSortRef):
        assert isinstance(value, bool)
        return z3.BoolVal(value)
    elif isinstance(sort, z3.ArraySortRef):
        return z3.K(sort.domain(), sort_value(value, sort.range()))
    elif isinstance(sort, z3.DatatypeSortRef):
        assert get_sort_name(sort) in structures
        assert isinstance(value, dict)
        structure = structures[get_sort_name(sort)]
        fields = []
        for var in structure.elems_ordered:
            f_sort = type_to_sort(var.type)
            if var.name in value:
                val = value[var.name]
            else:
                val = z3.Const(unique_name(), f_sort)
            f_value = sort_value(val, f_sort)
            fields.append(f_value)
        return sort.constructor(0)(*fields)
    else:
        raise ValueError(sort)


def sort_conversion(
    to_sort: z3.SortRef, arg_val: z3.ExprRef, signed: bool
) -> z3.ExprRef:
    from_sort = arg_val.sort()

    if isinstance(from_sort, z3.BitVecSortRef) and isinstance(
        to_sort, z3.BitVecSortRef
    ):
        if from_sort.size() > to_sort.size():
            expr = z3.Extract(to_sort.size() - 1, 0, arg_val)
        elif from_sort.size() < to_sort.size():
            if signed:
                expr = z3.SignExt(to_sort.size() - from_sort.size(), arg_val)
            else:
                expr = z3.ZeroExt(to_sort.size() - from_sort.size(), arg_val)
        else:
            expr = arg_val
    elif isinstance(from_sort, z3.ArithSortRef) and isinstance(
        to_sort, z3.BitVecSortRef
    ):
        if from_sort.is_int():
            expr = z3.Int2BV(arg_val, to_sort.size())
        elif from_sort.is_real():
            # real cannot be converted to bitvector
            # use a free symbolic variable instead
            expr = z3.Const(unique_name(), to_sort)
        else:
            raise ValueError(from_sort)
    elif isinstance(from_sort, z3.BitVecSortRef) and isinstance(to_sort, z3.ArithRef):
        if to_sort.is_int():
            expr = z3.BV2Int(arg_val)
        elif to_sort.is_real():
            expr = z3.ToReal(z3.BV2Int(arg_val))
        else:
            raise ValueError(to_sort)
    elif isinstance(from_sort, z3.BoolSortRef) and isinstance(
        to_sort, z3.BitVecSortRef
    ):
        expr = z3.If(
            arg_val, z3.BitVecVal(1, to_sort.size()), z3.BitVecVal(0, to_sort.size())
        )
    elif isinstance(from_sort, z3.BitVecSortRef) and isinstance(
        to_sort, z3.BoolSortRef
    ):
        expr = z3.If(
            arg_val == z3.BitVecVal(0, from_sort.size()),
            z3.BoolVal(False),
            z3.BoolVal(True),
        )
    elif isinstance(from_sort, z3.BoolSortRef) and isinstance(to_sort, z3.ArithSortRef):
        if to_sort.is_int():
            expr = z3.If(arg_val, z3.IntVal(1), z3.IntVal(0))
        elif to_sort.is_real():
            expr = z3.If(arg_val, z3.RealVal(1), z3.RealVal(0))
        else:
            raise ValueError(to_sort)
    elif isinstance(from_sort, z3.ArithSortRef) and isinstance(to_sort, z3.BoolSortRef):
        if from_sort.is_int():
            expr = z3.If(arg_val == z3.IntVal(0), z3.BoolVal(False), z3.BoolVal(True))
        elif from_sort.is_real():
            expr = z3.If(arg_val == z3.RealVal(0), z3.BoolVal(False), z3.BoolVal(True))
        else:
            raise ValueError(from_sort)
    elif isinstance(from_sort, z3.SeqSortRef) and isinstance(to_sort, z3.BitVecSortRef):
        # string to bytes
        expr = z3.BitVec(unique_name("str2bytes"), to_sort.size())
    else:
        # dynamic types, e.g., string, bytes
        expr = arg_val
    return expr


def unique_name(prefix: str = "sym") -> str:
    global symbolic_value_index
    name = f"{prefix}_{symbolic_value_index}"
    symbolic_value_index += 1
    return name


def type_to_sort(typ: Type | list[Type] | str) -> z3.SortRef | list[z3.SortRef]:
    """
    Only elementary types, array, mapping, user-defined enums and structs are supported.
    Others will trigger an exception.
    :param typ:
    :return:
    """
    if isinstance(typ, TypeAlias):
        typ = typ.type
    if isinstance(typ, str):
        typ = ElementaryType(typ)
    if isinstance(typ, ElementaryType):
        return elementary_type_to_sort(typ)
    elif isinstance(typ, UserDefinedType):
        return user_defined_type_to_sort(typ)
    elif isinstance(typ, MappingType):
        return map_to_sort(typ)
    elif isinstance(typ, ArrayType):
        return array_to_sort(typ)
    elif isinstance(typ, list):
        return [type_to_sort(t) for t in typ]
    else:
        raise NotImplementedError(typ)


def is_signed_type(typ: Type) -> bool:
    assert typ is not None
    if isinstance(typ, ElementaryType):
        return typ.type in Int
    else:
        return False


def elementary_type_to_sort(
    typ: ElementaryType | str,
) -> z3.SortRef:
    if isinstance(typ, str):
        typ = ElementaryType(typ)
    if typ.type in Uint + Int:
        # return z3.IntSort()
        size = 32 if typ.size > 32 else typ.size
        return z3.BitVecSort(size)
        # return z3.RealSort()
    elif typ.type == "string":
        return z3.StringSort()
    elif typ.type == "bytes":
        return z3.BitVecSort(256)
    elif typ.type == "address":
        return z3.BitVecSort(160)
    elif typ.type in Byte:
        return z3.BitVecSort(typ.size)
    elif typ.type == "bool":
        return z3.BoolSort()
    else:
        raise ValueError(typ)


def user_defined_type_to_sort(
    typ: UserDefinedType,
) -> z3.SortRef:
    typ_typ = typ.type
    if isinstance(typ_typ, Enum):
        # return z3.IntSort()
        sort = type_to_sort("uint")
        return sort
        # return z3.BitVecSort(8)
    elif isinstance(typ_typ, Structure):
        return struct_to_sort(typ_typ)
    elif isinstance(typ_typ, Contract):
        return type_to_sort("address")
        # return z3.BitVecSort(160)
    else:
        raise ValueError(typ)


def _symbol2py(ctx, s):
    """Convert a Z3 symbol back into a Python object."""
    if z3.Z3_get_symbol_kind(ctx.ref(), s) == z3.Z3_INT_SYMBOL:
        return "k!%s" % z3.Z3_get_symbol_int(ctx.ref(), s)
    else:
        return z3.Z3_get_symbol_string(ctx.ref(), s)


def get_sort_name(sort: z3.SortRef) -> str:
    return _symbol2py(sort.ctx, z3.Z3_get_sort_name(sort.ctx_ref(), sort.ast))


def struct_to_sort(typ: Structure) -> z3.DatatypeSortRef:
    if "sort" not in typ.context:
        datatype = z3.Datatype(typ.canonical_name)
        accessors = OrderedDict()
        field_declares = []
        for field in typ.elems_ordered:
            f_sort = type_to_sort(field.type)
            field_declares.append((field.name, f_sort))
        datatype.declare(typ.name, *field_declares)
        sort = datatype.create()
        # sometimes, there is a field named "name", which shadows the name function of the z3 sort.
        # therefore, we copy the implementation of "name" function here.
        name = get_sort_name(sort)
        structures[name] = typ
        typ.context["sort"] = sort

        for field in typ.elems_ordered:
            accessors[field.name] = getattr(sort, field.name)
        typ.context["accessors"] = accessors

    assert "sort" in typ.context
    assert "accessors" in typ.context
    return typ.context["sort"]


def structure_accessor(typ: Structure, field: str) -> z3.FuncDeclRef:
    if "accessors" not in typ.context:
        struct_to_sort(typ)
    assert "accessors" in typ.context
    assert field in typ.context["accessors"], f"{field} not in {typ}"
    return typ.context["accessors"][field]


def structure_accessors(typ: Structure) -> OrderedDict[str, z3.FuncDeclRef]:
    if "accessors" not in typ.context:
        struct_to_sort(typ)
    assert "accessors" in typ.context
    return typ.context["accessors"]


def map_to_sort(typ: MappingType) -> z3.ArraySortRef:
    return z3.ArraySort(type_to_sort(typ.type_from), type_to_sort(typ.type_to))


def array_to_sort(typ: ArrayType) -> z3.ArraySortRef:
    # return z3.ArraySort(z3.IntSort(), type_to_sort(typ.type))
    key_sort = type_to_sort("uint")
    return z3.ArraySort(key_sort, type_to_sort(typ.type))


collision_free_constraints: list[z3.BoolRef] = []

abi_encode_val_map: dict[str, z3.FuncDeclRef] = {}
abi_encode_keys: dict[str, list[tuple[z3.ExprRef]]] = {}


def abi_encode(fn_name: str, args: tuple[z3.ExprRef, ...]) -> z3.BitVecRef:
    name = f"{fn_name}<{','.join([str(arg.sort()) for arg in args])}>"
    if name not in abi_encode_val_map:
        fn = z3.Function(name, *[arg.sort() for arg in args], type_to_sort("bytes"))
        abi_encode_val_map[name] = fn
        abi_encode_keys[name] = []
    fn = abi_encode_val_map[name]
    r = fn(*args)
    for previous_args in abi_encode_keys[name]:
        collision_free_constraints.append(
            z3.Not(
                z3.Xor(
                    r == fn(*previous_args),
                    z3.And(*[a == b for a, b in zip(args, previous_args)]),
                )
            )
        )
    abi_encode_keys[name].append(args)
    return r


crypto_hash_sym_fns: dict[Operation, z3.FuncDeclRef] = {}
crypto_hash_keys: dict[Operation, list[z3.ExprRef]] = {}


def crypto_hash(fn_name: Call, arg: z3.ExprRef) -> z3.BitVecRef:
    if fn_name not in crypto_hash_sym_fns:
        fn = z3.Function(
            fn_name.function.name, type_to_sort("bytes"), type_to_sort("bytes32")
        )
        crypto_hash_sym_fns[fn_name] = fn
        crypto_hash_keys[fn_name] = []
        # arg0, arg1 = z3.Consts(
        #     f"{fn_name}_args0 {fn_name}_args1", type_to_sort("bytes")
        # )
        # collision_free_constraints.append(
        #     z3.ForAll(
        #         [arg0, arg1],
        #         z3.Implies(
        #             fn(arg0) == fn(arg1),
        #             arg0 == arg1,
        #         ),
        #         patterns=[z3.MultiPattern(fn(arg0), fn(arg1))],
        #     )
        # )
    fn = crypto_hash_sym_fns[fn_name]
    r = fn(arg)
    previous_keys = crypto_hash_keys[fn_name]
    for key in previous_keys:
        collision_free_constraints.append(z3.Not(z3.Xor(arg == key, r == fn(key))))
    previous_keys.append(arg)
    return r


ecrecover_args_sort = z3.Datatype("ecrecover_args")
ecrecover_args_sort.declare(
    "ecrecover_args",
    ("hash", type_to_sort("bytes32")),
    ("v", type_to_sort("uint8")),
    ("r", type_to_sort("bytes32")),
    ("s", type_to_sort("bytes32")),
)
ecrecover_args_sort = ecrecover_args_sort.create()
ecrecover_sym_fn: z3.FuncDeclRef = z3.Function(
    "ecrecover(bytes32,uint8,bytes32,bytes32)",
    ecrecover_args_sort,
    type_to_sort("address"),
)
ecrecover_keys: list[z3.DatatypeRef] = []


# ecrecover_args0, ecrecover_args1 = z3.Consts(
#     "ecrecover_args0 ecrecover_args1", ecrecover_args_sort
# )
# collision_free_constraints.append(
#     z3.ForAll(
#         [ecrecover_args0, ecrecover_args1],
#         z3.Implies(
#             ecrecover_args0 != ecrecover_args1,
#             ecrecover_sym_fn(ecrecover_args0) != ecrecover_sym_fn(ecrecover_args1),
#         ),
#         patterns=[
#             z3.MultiPattern(
#                 ecrecover_sym_fn(ecrecover_args0), ecrecover_sym_fn(ecrecover_args1)
#             )
#         ],
#     )
# )


def ecrecover(args: tuple[z3.ExprRef, ...]) -> z3.BitVecRef:
    assert len(args) == 4
    key = ecrecover_args_sort.constructor(0)(*args)
    r = ecrecover_sym_fn(key)
    for previous_key in ecrecover_keys:
        collision_free_constraints.append(
            z3.Not(
                z3.Xor(
                    key == previous_key,
                    r == ecrecover_sym_fn(previous_key),
                )
            )
        )
    ecrecover_keys.append(key)
    return r
