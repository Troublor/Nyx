import json
from pathlib import Path
from typing import Dict

from crytic_compile import CryticCompile

from lib.solidity import get_solc_path


def get_abi(sol_file: Path) -> Dict[str, dict]:
    solc = get_solc_path("0.8.12")
    compilation = CryticCompile(str(sol_file), solc=str(solc))
    return {
        c: a
        for cu in compilation.compilation_units.values()
        for fi in cu.source_units.values()
        for c, a in fi.abis.items()
    }


if __name__ == "__main__":
    contracts_dir = Path(__name__).parent / "contracts"
    abi_dir = Path(__name__).parent / "abi"
    for f in contracts_dir.iterdir():
        if f.is_file() and f.suffix == ".sol":
            abi_dict = get_abi(f)
            for contract, abi in abi_dict.items():
                with open(abi_dir / (contract + ".json"), "w") as file:
                    json.dump(abi, file)
