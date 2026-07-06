import Minimmit.Quorum
import Minimmit.Consistency.Lemma5_1

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- **Lemma 5.2 ((X1) is satisfied), unique-block form.** If `b` receives an
    L-notarisation, then any block of the same view receiving an
    M-notarisation is `b` itself. Paper proof, directly: let `L` contribute to
    the L-notarisation for `b` and `Q` vote for `b'`; then
    `|L ∩ Q| ≥ (n − f) + (2f + 1) − n = f + 1`, so `L ∩ Q` contains a correct
    processor (`quorum_intersect_correct` with the fault bound), which voted
    for both `b` and `b'` in one view — hence `b' = b` by Lemma 5.1. -/
theorem lemma_5_2 {n f : Nat} (sv : StateView n Block Message Tx) (e : Execution n Message)
    (hd : sv.VoteDiscipline e) (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {b b' : Block} (hv : sv.bview b' = sv.bview b)
    (hL : sv.LNotarised e f b) (hM : sv.MNotarised e f b') : b' = b := by
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  obtain ⟨L, hLcard, hLvotes⟩ := hL
  obtain ⟨Q, hQcard, hQvotes⟩ := hM
  obtain ⟨p, hpL, hpQ, hpb⟩ := quorum_intersect_correct hnf hLcard hQcard hbyz
  exact lemma_5_1 sv e hd p (hcorr p hpb) hv (hQvotes p hpQ) (hLvotes p hpL)

/-- **Lemma 5.2, paper statement.** "If `b` receives an L-notarisation, then
    no block `b' ≠ b` with `b'.view = b.view` receives an M-notarisation." -/
theorem lemma_5_2_excl {n f : Nat} (sv : StateView n Block Message Tx) (e : Execution n Message)
    (hd : sv.VoteDiscipline e) (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {b b' : Block} (hne : b' ≠ b) (hv : sv.bview b' = sv.bview b)
    (hL : sv.LNotarised e f b) : ¬ sv.MNotarised e f b' :=
  fun hM => hne (lemma_5_2 sv e hd hnf hfb hv hL hM)

end Minimmit
