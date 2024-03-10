import structlog
from structlog.stdlib import BoundLogger


class Observer:
    def __init__(self):
        """init"""

        self.logger: BoundLogger = structlog.get_logger()

        """ profiling """
        self.total_time = 0
        # Phase0: compilation and slither analysis
        self.phase0_time = 0

        # Phase1: HFG construction and abstract interpretation
        self.phase1_time = 0
        self.hfg_time = 0
        self.prune_time = 0

        # Phase2: symvalic analysis
        self.phase2_time = 0
        self.summarization_time = 0
        self.application_time = 0
        self.solving_time = 0

        """ ablation study """
        self.full_pairs = 0
        self.candidate_pairs = 0

        """ results """
        self.positives = 0
        self.negatives = 0
        self.unknowns = 0

    def to_dict(self):
        return {
            "total_time": self.total_time,
            "phase0_time": self.phase0_time,
            "phase1_time": self.phase1_time,
            "phase2_time": self.phase2_time,
            "hfg_time": self.hfg_time,
            "prune_time": self.prune_time,
            "summarization_time": self.summarization_time,
            "application_time": self.application_time,
            "solving_time": self.solving_time,
            "full_pairs": self.full_pairs,
            "candidate_pairs": self.candidate_pairs,
            "positives": self.positives,
            "negatives": self.negatives,
            "unknowns": self.unknowns,
        }

    def __str__(self):
        multiline = f"""
        Total time: {self.total_time:.2f}s
        Phase0: {self.phase0_time:.2f}s
        Phase1: {self.phase1_time:.2f}s
        Phase2: {self.phase2_time:.2f}s
        HFG construction: {self.hfg_time:.2f}s
        Pruning: {self.prune_time:.2f}s
        Summarization: {self.summarization_time:.2f}s
        Application: {self.application_time:.2f}s
        Solving: {self.solving_time:.2f}s
        Full pairs: {self.full_pairs}
        Candidate pairs: {self.candidate_pairs}
        Positives: {self.positives}
        Negatives: {self.negatives}
        Unknowns: {self.unknowns}
        """
        return multiline
