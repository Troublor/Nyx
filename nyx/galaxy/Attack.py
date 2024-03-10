import json
from pathlib import Path
from typing import TypedDict

from nyx.galaxy.ContractGroup import ContractGroup
from nyx.galaxy.ContractRepo import ContractRepoRaw
from nyx.lib.types import Hash, Address


class AttackMetadata(TypedDict):
    hash: Hash


class Attack(object):
    def __init__(self, root: Path):
        self.root = root
        with open(self.root.joinpath("metadata.json")) as f:
            self._metadata = json.load(f)

    @property
    def contract_group(self) -> ContractGroup:
        cs = [
            ContractRepoRaw(d, Address(d.name))
            for d in self.root.joinpath("contracts").iterdir()
            if d.is_dir()
        ]
        return ContractGroup(cs)
