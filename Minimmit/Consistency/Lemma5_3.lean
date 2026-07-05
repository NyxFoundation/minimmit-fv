import Minimmit.Quorum
import Minimmit.Consistency.Lemma5_1

set_option autoImplicit false

namespace Minimmit

/-- **Lemma 5.3 ((X2) is satisfied).** If `b` receives an L-notarisation, then
    view `b.view` does not receive a nullification.

    Paper proof, mirrored: let `L` contribute to the L-notarisation and `byz`
    be the Byzantine set; `P := L \ byz` are correct voters for `b`, with
    `|P| ≥ (n − f) − f = n − 2f` (so `|Π \ P| ≤ 2f`). By quorum intersection a
    correct voter sends `nullify(b.view)`, so there is a *first* timeslot `t₀`
    at which some correct voter `p₁` does (`Nat.find`). `p₁`'s nullify carries
    a lines 24–28 justification (`null_justified`): `≥ 2f + 1` distinct
    signers, each of a `(nullify, v)` seen at `t₀` — impossible for `q ∈ P`,
    since it was sent at `t' < t₀` (`seen_null_earlier`), contradicting
    minimality — or of a vote for a view-`v` block `≠ b` — impossible for
    `q ∈ P` by Lemma 5.1. Hence all `2f + 1` signers avoid `P`, contradicting
    `|Π \ P| ≤ 2f`. -/
theorem lemma_5_3 {n f : Nat} (sv : StateView n) (e : Execution n)
    (hd : sv.VoteDiscipline e) (hnd : sv.NullifyDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {b : Block} (hL : sv.LNotarised e f b) :
    ¬ sv.Nullified e f (sv.bview b) := by
  classical
  intro hNull
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  obtain ⟨L, hLcard, hLvotes⟩ := hL
  obtain ⟨N, hNcard, hNnulls⟩ := hNull
  -- some correct processor both contributes to the L-notarisation and nullifies
  obtain ⟨p₀, hp₀L, hp₀N, hp₀b⟩ := quorum_intersect_correct hnf hLcard hNcard hbyz
  -- so the set of timeslots at which a correct L-voter sends nullify(b.view)
  -- is nonempty; take the first one, t₀, with witness p₁
  have hex : ∃ t, ∃ p, p ∉ byz ∧ e.Signed p (sv.voteMsg b) ∧
      sv.nullsAt p t (sv.bview b) := by
    obtain ⟨t, ht⟩ :=
      hnd.signed_null p₀ (sv.bview b) (hcorr p₀ hp₀b) (hNnulls p₀ hp₀N)
    exact ⟨t, p₀, hp₀b, hLvotes p₀ hp₀L, ht⟩
  obtain ⟨p₁, hp₁b, hp₁vote, hp₁null⟩ := Nat.find_spec hex
  have hp₁c : e.Correct p₁ := hcorr p₁ hp₁b
  obtain ⟨tv, hvtv⟩ := (hd.signed_vote p₁ b hp₁c).mp hp₁vote
  -- the lines 24–28 justification behind p₁'s nullify
  obtain ⟨W, hWcard, hWforms⟩ :=
    hnd.null_justified p₁ (Nat.find hex) tv (sv.bview b) b hp₁c hp₁null hvtv rfl
  -- no correct L-voter can be among the 2f+1 signers
  have hWdisj : ∀ q ∈ W, q ∉ L \ byz := by
    intro q hqW hqLb
    obtain ⟨hqL, hqb⟩ := Finset.mem_sdiff.mp hqLb
    have hqc : e.Correct q := hcorr q hqb
    rcases hWforms q hqW with hseen | ⟨b', hb'view, hb'ne, hseen⟩
    · -- form (i): q's nullify was sent strictly before t₀ — contradicts minimality
      obtain ⟨t', ht'lt, hnull'⟩ :=
        hnd.seen_null_earlier p₁ q (Nat.find hex) (sv.bview b) hp₁c hqc hseen
      exact Nat.find_min hex ht'lt ⟨q, hqb, hLvotes q hqL, hnull'⟩
    · -- form (ii): q voted for both b and b' ≠ b in one view — contradicts Lemma 5.1
      obtain ⟨tq, hvq⟩ := (hd.signed_vote q b hqc).mp (hLvotes q hqL)
      have hsq : e.Signed q (sv.voteMsg b') :=
        hnd.seen_signed p₁ q (Nat.find hex) _ hp₁c hqc hseen
      obtain ⟨tq', hvq'⟩ := (hd.signed_vote q b' hqc).mp hsq
      exact hb'ne (one_vote_per_view sv e hd q hqc hb'view hvq' hvq)
  -- counting: W avoids L \ byz, yet |W| ≥ 2f+1 and |L \ byz| ≥ n − 2f
  have hdisj : Disjoint W (L \ byz) := Finset.disjoint_left.mpr hWdisj
  have hunion : W.card + (L \ byz).card ≤ n := by
    have h := Finset.card_le_univ (W ∪ (L \ byz))
    rw [Finset.card_union_of_disjoint hdisj] at h
    simpa using h
  have hsdiff : L.card ≤ (L \ byz).card + byz.card :=
    Finset.card_le_card_sdiff_add_card
  simp only [lQuorum] at hLcard
  omega

end Minimmit
