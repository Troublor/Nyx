// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "./ERC20.sol";

interface WETH9 is ERC20 {
    function deposit() external payable;

    function withdraw(uint wad) external;
}

