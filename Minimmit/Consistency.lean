import Minimmit.Consistency.Lemma5_1
import Minimmit.Consistency.Lemma5_2
import Minimmit.Consistency.Lemma5_3
import Minimmit.Consistency.Lemma5_4
import Minimmit.Consistency.LogLevel

/-!
# Track A — Consistency (safety)

Lemma 5.1–5.4: one-vote-per-view plus quorum intersection give the invariants
`(X1)`/`(X2)`, hence Consistency.

* `Minimmit.Consistency.Lemma5_1` — one vote per view (`lemma_5_1`).
* `Minimmit.Consistency.Lemma5_2` — invariant `(X1)`: an L-notarised block
  excludes a conflicting M-notarisation in its view (`lemma_5_2`).
* `Minimmit.Consistency.Lemma5_3` — invariant `(X2)`: an L-notarised view
  receives no nullification (`lemma_5_3`).
* `Minimmit.Consistency.Lemma5_4` — Consistency, block form: no two
  inconsistent blocks are both L-notarised (`lemma_5_4`).
* `Minimmit.Consistency.LogLevel` — Consistency, log level (§2): correct
  logs are pairwise prefix-comparable (`consistency_logs`), over the
  sequence-valued `LogView` interface with `Tr*` made well-defined by the
  `collision_resistant` axiom.
-/
