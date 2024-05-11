pragma solidity ^0.8.0;

contract Puzzle {
    bytes32 constant public hash = 0xb5b5b97fafd9855eec9b41f74dfb6c38f5951141f9a3ecd7f44d5479b630ee0a;
    uint public reward = 1000 ether;

    constructor() public payable {} // load with ether

    function solve(bytes memory solution) public {
        // If you can find the pre image of the hash, receive 1000 ether
         // <yes> <report> FRONT_RUNNING
        require(hash == keccak256(abi.encodePacked(solution)));
        payable(msg.sender).transfer(reward);
        reward = 0;
    }
}
