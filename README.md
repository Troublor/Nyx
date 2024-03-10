# Nyx: Detecting Exploitable Front-Running Vulnerabilities in Smart Contracts

Accpeted at The 45th IEEE Symposium on Security and Privacy (S&P 2024): 
[paper](./SP2024.pdf)

**Disclaimer**: The tool is a research demo and many corner cases are not perfectly handled.
If you find any not working cases, feel free to post an issue and I will try my best to fix it.

## Technical Overview

Nyx adopts a two-phase analysis for detecting exploitable front-running vulnerabilities (not just transaction-order dependency problems).
- Phase1: A static pruning is performed on the `hybrid flow graph (HFS)`, which encodes both control and data dependencies across multiple smart contracts under analysis, to quickly filter out those function pairs that do not have any interference with each other (they are not possible to be vulnerable).
- Phase2: A symbolic validation is conducted using a symbolic execution engine to validate whether an malicious user can front-run users' transactions to make profits and exclude those benign transaction order dependency cases.

Please refer to our paper for detailed explanation.

## Install dependencies

```
pip install -e .
```

## Example Usage of Nyx

An example vulnerable contract is given in `examples/HashPuzzle`: 
Run the following command to analyze this contract using Nyx:
```
python nyx/main.py ./examples/HashPuzzle
```

An `result.json` will generated in the current working directory, with the following content, indicating the detection result of `all function pairs collection (phase0)`, `static prunning (phase1)`, `symbolic validation (phase2)` and the overall detection result.
Please refer to the paper for detailed explanation. 
```
{
  "functions": [
    "Puzzle.constructor()",
    "Puzzle.solve(bytes)"
  ],
  "phase0": 3,
  "phase1": [
    [
      "Puzzle.solve(bytes)",
      "Puzzle.solve(bytes)"
    ]
  ],
  "phase2": [
    [
      "Puzzle.solve(bytes)",
      "Puzzle.solve(bytes)",
      "vulnerable"
    ]
  ],
  "result": [
    [
      "Puzzle.solve(bytes)",
      "Puzzle.solve(bytes)"
    ]
  ],
  "interrupted": false
}
```
