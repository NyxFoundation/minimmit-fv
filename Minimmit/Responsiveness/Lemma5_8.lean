import Minimmit.Liveness.Lemma5_6

set_option autoImplicit false

namespace Minimmit

/-- **Lemma 5.8 (fast finalisation under a correct leader).** If `lead(v)` is
    correct and the first correct processor to enter view `v` does so at
    `t ≥ GST`, then there is a view-`v` block `b` such that by `t + 3δ` every
    correct processor holds an L-notarisation for `b`, has finalised `b`, and
    has left view `v`.

    Paper proof: rerun Lemma 5.6 at the *actual* post-GST delay `δ ≤ Δ`
    (`leader_round_votes` at `d := δ`): every correct processor votes for the
    leader's block `b` by `t + 2δ`, and the votes — all cast at `≥ t ≥ GST` —
    are delivered by `t + 3δ`, forming an L-notarisation at every correct
    processor. Holding it, each finalises `b` (lines 31–32) and, since an
    L-notarisation contains an M-notarisation (`n − f ≥ 2f + 1` under
    `5f + 1 ≤ n`), leaves view `v` (lines 19–21). -/
theorem lemma_5_8 {n f : Nat} {GST Δ δ : Time} (sv : StateView n)
    (e : Execution n) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST δ)
    (htd : sv.TimerDiscipline e f Δ) (hδΔ : δ ≤ Δ)
    (hfd : sv.FinalityDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {t : Time} (hGST : GST ≤ t)
    (hlc : e.Correct (sv.lead v))
    {q₀ : Processor n} (hq₀ : e.Correct q₀) (hq₀v : sv.curView q₀ t = v)
    (hfirst : ∀ r, e.Correct r → ∀ t' < t, sv.curView r t' < v) :
    ∃ b, sv.bview b = v ∧ e.Signed (sv.lead v) (sv.blockMsg b) ∧
      ∀ p, e.Correct p →
        sv.SeenLNotar f p (t + 3 * δ) b ∧
        (∃ tf ≤ t + 3 * δ, sv.finalisesAt p tf b) ∧
        v < sv.curView p (t + 3 * δ + 1) := by
  classical
  obtain ⟨b, hbv, hbsig, hallvote⟩ := leader_round_votes sv e hrd hvd hnw
    hld hdd htd hδΔ hfb hv1 hGST hlc hq₀ hq₀v hfirst
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  -- votes for b are cast at times in [t, t + 2δ]
  have hvlow : ∀ (r : Processor n) (tp : Time), e.Correct r →
      sv.votesAt r tp b → t ≤ tp := by
    intro r tp hrc hvp
    by_contra h'
    push Not at h'
    have h1 := hd.vote_view r tp b hrc hvp
    have h2 := hfirst r hrc tp h'
    omega
  refine ⟨b, hbv, hbsig, ?_⟩
  intro p hp
  -- every correct vote is delivered to p by t + 3δ: an L-notarisation
  have hLN : sv.SeenLNotar f p (t + 3 * δ) b := by
    refine ⟨Finset.univ \ byz, ?_, ?_⟩
    · have hcard : (Finset.univ \ byz : Finset (Processor n)).card =
          n - byz.card := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
          Finset.inter_univ]
      simp only [lQuorum]
      omega
    · intro r hr
      have hrc := hcorr r (Finset.mem_sdiff.mp hr).2
      obtain ⟨tp, htp, hvp⟩ := hallvote r hrc
      have hge := hvlow r tp hrc hvp
      have hseen := hdd.vote_delivered_by r p tp b hrc hvp hp
      exact hnw.seen_mono p r (max GST tp + δ) (t + 3 * δ) _ hseen (by omega)
  refine ⟨hLN, hfd.finalise_on_lnotar p (t + 3 * δ) b hp hLN, ?_⟩
  -- an L-notarisation contains an M-notarisation, so p leaves view v
  have hSM : sv.SeenMNotar f p (t + 3 * δ) b := by
    obtain ⟨W, hW, hWs⟩ := hLN
    refine ⟨W, ?_, hWs⟩
    simp only [lQuorum] at hW
    omega
  have hpv : v ≤ sv.curView p (t + 3 * δ) := by
    obtain ⟨tp, htp, hvp⟩ := hallvote p hp
    have h1 := hd.vote_view p tp b hp hvp
    have h2 := hvd.curView_mono hp (show tp ≤ t + 3 * δ by omega)
    omega
  rcases hpv.lt_or_eq with hgt | heq
  · have := hvd.curView_mono hp (show t + 3 * δ ≤ t + 3 * δ + 1 by omega)
    omega
  · exact hvd.leave_on_mnotar p (t + 3 * δ) v b hp heq.symm hbv hSM

end Minimmit
