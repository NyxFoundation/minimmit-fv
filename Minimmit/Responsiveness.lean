import Minimmit.Responsiveness.Lemma5_8

/-!
# Track C — Optimistic responsiveness

Lemma 5.8–5.10: timing-refined versions of the Track-B arguments give the
latency bound `O(f_a·Δ + δ)`.

* `Minimmit.Responsiveness.Lemma5_8` — under a correct post-GST leader, all
  correct processors finalise a view-`v` block and leave view `v` by
  `t + 3δ` (`lemma_5_8`).
-/
