import Minimmit.Basic
import Minimmit.Protocol
import Minimmit.Axioms
import Minimmit.Consistency

/-!
# Minimmit

Machine-checked formalization of the *Minimmit* consensus protocol
(arXiv:2508.10862, FC'26). See `docs/formalization-strategy.md` for the proof
discipline (`axiom` / hypothesis threading, never `sorry`) and the dependency
graph.

* `Minimmit.Basic` — core types: processors, views, blocks, messages, the
  M/L/nullification quorum thresholds, the abstract `Execution`.
* `Minimmit.Protocol` — the abstract per-processor state-transition interface
  of Algorithm 1 (`StateView`, `VoteDiscipline`).
* `Minimmit.Axioms` — idealized cryptography axioms (Barrier 1).
* `Minimmit.Consistency` — Track A (safety): Lemma 5.1–5.4.
-/
