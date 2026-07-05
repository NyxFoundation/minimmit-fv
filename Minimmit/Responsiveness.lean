import Minimmit.Responsiveness.Lemma5_8
import Minimmit.Responsiveness.Lemma5_9
import Minimmit.Responsiveness.Lemma5_10

/-!
# Track C — Optimistic responsiveness

Lemma 5.8–5.10: timing-refined versions of the Track-B arguments give the
latency bound `O(f_a·Δ + δ)`.

* `Minimmit.Responsiveness.Lemma5_8` — under a correct post-GST leader, all
  correct processors finalise a view-`v` block and leave view `v` by
  `t + 3δ` (`lemma_5_8`).
* `Minimmit.Responsiveness.Lemma5_9` — with any leader, all correct
  processors leave view `v` by `t + 2Δ + 3δ` (`lemma_5_9`).
* `Minimmit.Responsiveness.Lemma5_10` — optimistic responsiveness: a
  transaction received at `t ≥ GST` is in every correct log by
  `t + 2δ + (f_a + 1)·(2Δ + 2δ + 1) + 4δ = t + O(f_a·Δ + δ)`
  (`lemma_5_10`).
-/
