import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Minimmit.Basic

set_option autoImplicit false

namespace Minimmit

/-- **Quorum intersection** (Barrier 2) — the deterministic engine behind
    Lemmas 5.2–5.4: under `5f + 1 ≤ n`, an L-quorum (`n − f` processors) and an
    M/nullification-quorum (`2f + 1` processors) intersect in at least
    `(n − f) + (2f + 1) − n = f + 1` processors, hence in at least one that is
    not Byzantine. Parameterized by `n`, `f` and the fault bound as hypotheses —
    `n = 5f + 1` is never assumed. -/
theorem quorum_intersect_correct {n f : Nat} (hnf : 5 * f + 1 ≤ n)
    {L Q byz : Finset (Fin n)}
    (hL : lQuorum n f ≤ L.card) (hQ : mQuorum f ≤ Q.card)
    (hbyz : byz.card ≤ f) :
    ∃ p, p ∈ L ∧ p ∈ Q ∧ p ∉ byz := by
  by_contra h
  push Not at h
  have hsub : L ∩ Q ⊆ byz := fun p hp =>
    h p (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
  have hinter : (L ∩ Q).card ≤ f := le_trans (Finset.card_le_card hsub) hbyz
  have hunion : (L ∪ Q).card ≤ n := by
    simpa using Finset.card_le_univ (L ∪ Q)
  have hcards : (L ∪ Q).card + (L ∩ Q).card = L.card + Q.card :=
    Finset.card_union_add_card_inter L Q
  simp only [lQuorum, mQuorum] at hL hQ
  omega

/-- From per-member eventual facts, monotone in time, extract one uniform
    time (there are finitely many members). -/
theorem exists_uniform_time {α : Type} {C : Finset α} {P : α → Nat → Prop}
    (hmono : ∀ r t t', t ≤ t' → P r t → P r t')
    (h : ∀ r ∈ C, ∃ t, P r t) : ∃ T, ∀ r ∈ C, P r T := by
  classical
  choose g hg using h
  refine ⟨C.attach.sup fun x => g x.1 x.2, fun r hr => ?_⟩
  exact hmono r _ _ (Finset.le_sup (Finset.mem_attach C ⟨r, hr⟩)) (hg r hr)

/-- Any `2f + 1` quorum contains a processor outside a Byzantine set of size
    `≤ f`. -/
theorem quorum_exists_nonfaulty {n f : Nat} {Q byz : Finset (Fin n)}
    (hQ : 2 * f + 1 ≤ Q.card) (hbyz : byz.card ≤ f) :
    ∃ q ∈ Q, q ∉ byz := by
  by_contra h
  push Not at h
  have hcard : Q.card ≤ byz.card := Finset.card_le_card fun q hq => h q hq
  omega

end Minimmit
