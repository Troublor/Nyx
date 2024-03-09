from pathlib import Path

from slither.core.declarations import Contract
from solc_select.constants import ARTIFACTS_DIR
from solc_select.solc_select import installed_versions, install_artifacts


def get_solc_path(version: str) -> Path:
    installed = installed_versions()
    if version not in installed:
        install_artifacts([version])
    return ARTIFACTS_DIR.joinpath(f"solc-{version}").joinpath(f"solc-{version}")
