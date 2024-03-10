import json
import time

from analyze.config import Config, Output, FunctionPairResult
from analyze.group import AnalyzeGroup
from analyze.observe import Observer
from analyze.prune import collect_candidate_pairs
from analyze.validate import Validator
from hfg.hybrid_flow_graph import HybridFlowGraph
from lib.signal import interrupted


def analyze_single(
    g: AnalyzeGroup, observer: Observer = None, cfg: Config = None
) -> Output:
    if observer is None:
        observer = Observer()

    if cfg is None:
        cfg = Config()

    output = Output()

    logger = cfg.logger.bind(group=g.name)

    """ phase0 """
    logger.info("Phase 0 analysis started")
    logger = logger.bind(phase=0)
    # profiling
    t0 = time.time()
    # compile and slither analysis
    for repo in g.contract_repos:
        logger.info(
            "Compiling and analyzing contracts using Slither...",
            repo=repo.name,
            path=repo.root.__str__(),
        )
        _ = repo.slither
    observer.phase0_time += time.time() - t0

    # output
    fns = []
    for c in g.analyze_contracts:
        for function in c.functions:
            if (
                function.is_implemented
                and function.visibility in ["public", "external"]
                and not function.view
            ):
                fns.append(function)
    output.functions = fns
    output.phase0_pairs_count = len(fns) * (len(fns) + 1) // 2

    # profiling
    fns = []
    for c in g.analyze_contracts:
        for function in c.functions:
            if (
                function.is_implemented
                and function.visibility in ["public", "external"]
                and not function.view
            ):
                fns.append(function)
    pairs = []
    for i in range(len(fns)):
        for j in range(i, len(fns)):
            pairs.append((fns[i], fns[j]))
    observer.full_pairs += len(pairs)
    logger = logger.unbind("phase")
    logger.info(
        "Phase 0 analysis finished",
        time=f"{time.time() - t0:.2f}s",
        pairs=len(pairs),
    )

    """ phase1 """
    logger.info("Phase 1 analysis started")
    logger = logger.bind(phase=1)
    # profiling
    t1 = time.time()
    # build HFG
    hfg = HybridFlowGraph(g.all_contracts, g.analyze_contracts)
    logger.info("Hybrid flow graph built", time=f"{time.time() - t1:.2f}s")

    # profiling
    observer.hfg_time += time.time() - t1
    t2 = time.time()

    # Prune impossible function pairs
    if not cfg.disable_pruning:
        pairs = collect_candidate_pairs(hfg)
    logger.info(
        "Potential vulnerable function pairs collected",
        time=f"{time.time() - t2:.2f}s",
        pairs=len(pairs),
    )

    # profiling
    observer.prune_time += time.time() - t2
    observer.phase1_time += time.time() - t1
    observer.candidate_pairs += len(pairs)
    logger = logger.unbind("phase")
    logger.info(
        "Phase 1 analysis finished",
        time=f"{time.time() - t1:.2f}s",
        pairs=len(pairs),
    )

    # output
    for pair in pairs:
        output.phase1_pairs.add(pair)

    """ phase2 """
    logger.info("Phase 2 analysis started")
    logger = logger.bind(phase=2)
    # profiling
    t3 = time.time()

    # Validate function pairs
    validator = Validator(g.all_contracts, observer=observer, config=cfg)
    for i, pair in enumerate(pairs):
        if interrupted():
            break

        logger.info(
            f"Validating {i + 1}/{len(pairs)}",
            fn1=pair[0].canonical_name,
            fn2=pair[1].canonical_name,
        )

        # Validate
        t4 = time.time()
        if not cfg.disable_validation:
            r = validator.validate2(pair)
        else:
            r = FunctionPairResult.VULNERABLE
        output.phase2_pairs.add((pair[0], pair[1], r))

        # profiling
        if r == FunctionPairResult.SAFE:
            observer.negatives += 1
        elif r == FunctionPairResult.VULNERABLE:
            observer.positives += 1
        else:
            observer.unknowns += 1

        logger.info(
            f"Validated {i + 1}/{len(pairs)}",
            fn1=pair[0].canonical_name,
            fn2=pair[1].canonical_name,
            result=r.value,
            time=f"{time.time() - t4:.2f}s",
        )

    # profiling
    observer.phase2_time += time.time() - t3
    logger = logger.unbind("phase")
    logger.info(
        "Phase 2 analysis finished",
        time=f"{time.time() - t3:.2f}s",
        positives=observer.positives,
        unknowns=observer.unknowns,
        negatives=observer.negatives,
    )

    # output
    with open(g.result_file, "w") as f:
        json.dump(output.to_dict(), f, indent=2)
    logger.info("Analysis result written", output=g.result_file)
    if g.profiling_file:
        with open(g.profiling_file, "w") as f:
            json.dump(observer.to_dict(), f, indent=2)
        logger.info("Profiling result written", output=g.profiling_file)
    return output


def analyze_batch(
    gs: list[AnalyzeGroup], observer: Observer = None, cfg: Config = None
) -> list[Output]:
    if observer is None:
        observer = Observer()

    if cfg is None:
        cfg = Config()

    outputs = []
    for g in gs:
        outputs.append(analyze_single(g, observer, cfg))
    return outputs
