from __future__ import annotations

import functools
from typing import List

from slither.slithir.operations import (
    Operation,
    EventCall,
    SolidityCall,
    LowLevelCall,
    HighLevelCall,
    Send,
    Transfer,
    InternalCall,
    InternalDynamicCall,
    LibraryCall,
)

from lib.assets.erc1155 import ERC1155
from lib.assets.erc20 import ERC20
from lib.assets.erc721 import ERC721
from lib.assets.erc777 import ERC777
from lib.assets.ether import Ether
from lib.assets.transfer import THIS, AssetTransfer
from lib.assets.weth9 import WETH9

ASSETS_DEFINITIONS = [
    Ether,
    WETH9,
    ERC20,
    ERC721,
    ERC777,
    ERC1155,
]


def resolve_asset_transfer_op(op: Operation) -> List[AssetTransfer]:
    transfers = []
    if isinstance(op, EventCall):
        transfers += list(
            functools.reduce(
                lambda acc, c: acc + c.resolve_event(op), ASSETS_DEFINITIONS, []
            )
        )
    elif isinstance(
        op,
        (
            Transfer,
            Send,
            HighLevelCall,
            LowLevelCall,
            SolidityCall,
            InternalCall,
            InternalDynamicCall,
            LibraryCall,
        ),
    ):
        transfers += list(
            functools.reduce(
                lambda acc, c: acc + c.resolve_transfer(op), ASSETS_DEFINITIONS, []
            )
        )
    return transfers


def is_token_function_call(op: Operation) -> bool:
    return any([asset.is_function_call(op) for asset in ASSETS_DEFINITIONS])
