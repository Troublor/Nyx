import os
import tempfile

from crytic_compile import CryticCompile
from slither.slither import Slither

from galaxy.ContractRepo import AstTransformer
from supernova.lib.solidity import get_solc_path


class TestSourceCode(object):
    def __init__(self, code: str, solc_version: str = "0.8.11"):
        self.solc_version = solc_version
        self.code = code
        _file, self._path = tempfile.mkstemp(suffix=".sol")
        f = os.fdopen(_file, "w")
        f.write(code)
        f.close()

    def __enter__(self) -> Slither:
        solc = get_solc_path(self.solc_version)
        comp = CryticCompile(self._path, solc=solc.__str__())
        for _, file in comp.compilation_units.items():
            AstTransformer(file).transform()
        return Slither(comp)

    def __exit__(self, exc_type, exc_val, exc_tb):
        os.remove(self._path)
