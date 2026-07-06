import Minimmit.Liveness.Lemma5_5
import Minimmit.Liveness.Lemma5_6

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- **Lemma 5.7 (Liveness).** Every transaction received by a correct
    processor eventually enters the log of every correct processor.

    Paper proof, mirrored. Suppose correct `p_i` receives `tr` at `t₀`. By
    the round-robin schedule (`hrot`) there is a view `v₁` led by `p_i` with
    `v₁ > curView p_i t₀` and `v₁ > GST`. By Lemma 5.5 some correct processor
    enters `v₁`; since reaching view `v₁` takes at least `v₁ − 1 ≥ GST`
    timeslots, the *first* correct processor to do so does so at
    `t ≥ GST`. Lemma 5.6 then yields a `p_i`-signed view-`v₁` block `b` that
    every correct processor votes for. `ProposeChild` put `tr` into the
    payload of `b` or of one of its ancestors (`propose_includes` — `p_i`
    received `tr` while still in a view `< v₁`). Every correct processor
    eventually holds the `n − f` correct votes for `b` — an L-notarisation —
    and, finalising `b`, adds `tr` to its log (`log_on_lnotar`). -/
theorem lemma_5_7 {n f : Nat} {GST Δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST Δ)
    (htd : sv.TimerDiscipline e f Δ) (htx : sv.TxDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    (hrot : ∀ (p : Processor n) (v₀ : View), ∃ v, v₀ ≤ v ∧ sv.lead v = p)
    {tr : Tx} {pᵢ : Processor n} {t₀ : Time}
    (hpc : e.Correct pᵢ) (hrecv : sv.receivedTx pᵢ t₀ tr) :
    ∀ p, e.Correct p → ∃ t', sv.inLog p t' tr := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  -- choose a view v₁ led by pᵢ, beyond pᵢ's view at receipt and beyond GST
  obtain ⟨v₁, hv₁ge, hv₁lead⟩ :=
    hrot pᵢ (max (sv.curView pᵢ t₀ + 1) (GST + 1))
  have hv₁1 : 1 ≤ v₁ := by
    have h1 := hvd.view_start pᵢ hpc
    have h2 := hvd.curView_mono hpc (Nat.zero_le t₀)
    omega
  -- some correct processor enters v₁ (Lemma 5.5); take the first timeslot
  have hEx : ∃ t, ∃ r, e.Correct r ∧ sv.curView r t = v₁ := by
    obtain ⟨t, ht⟩ := lemma_5_5 sv e hvd hnw hnf ⟨byz, hbyz, hcorr⟩ v₁ hv₁1
      pᵢ hpc
    exact ⟨t, pᵢ, hpc, ht⟩
  obtain ⟨q₀, hq₀c, hq₀v⟩ := Nat.find_spec hEx
  -- the first entry is at ≥ GST: reaching v₁ takes ≥ v₁ − 1 ≥ GST timeslots
  have hGSTle : GST ≤ Nat.find hEx := by
    have := hvd.curView_le_succ hq₀c (Nat.find hEx)
    omega
  -- nobody correct is in a view ≥ v₁ before the first entry
  have hfirst : ∀ r, e.Correct r → ∀ t' < Nat.find hEx,
      sv.curView r t' < v₁ := by
    intro r hrc t' hlt
    by_contra hge
    push Not at hge
    obtain ⟨t'', ht''le, ht''⟩ := hvd.exists_view_eq_le hrc hv₁1 t' hge
    exact absurd ⟨r, hrc, ht''⟩ (Nat.find_min hEx (by omega))
  -- Lemma 5.6: the leader pᵢ's block b is voted for by every correct processor
  have hlc : e.Correct (sv.lead v₁) := by rw [hv₁lead]; exact hpc
  obtain ⟨b, hbv, hbsig, hallvote, _⟩ :=
    lemma_5_6 sv e hd hrd hvd hnw hld hdd htd ⟨byz, hbyz, hcorr⟩ hv₁1 hGSTle
      hlc hq₀c hq₀v hfirst
  -- ProposeChild put tr into b or one of its ancestors
  obtain ⟨b', hanc, htxin⟩ := htx.propose_includes v₁ tr b t₀
    hlc (by rw [hv₁lead]; exact hrecv) (by rw [hv₁lead]; omega)
    hbsig hbv
  -- every correct processor assembles an L-notarisation for b and logs tr
  intro p hp
  set C : Finset (Processor n) := Finset.univ \ byz with hC
  obtain ⟨T, hT⟩ := exists_uniform_time (C := C)
    (P := fun r t => sv.seenAt p t r (sv.voteMsg b))
    (fun r t t' htt hs => hnw.seen_mono p r t t' _ hs htt)
    (fun r hr => by
      rw [hC] at hr
      have hrc := hcorr r (Finset.mem_sdiff.mp hr).2
      obtain ⟨tv, hv⟩ := hallvote r hrc
      exact hnw.vote_delivered r p tv b hrc hv hp)
  have hLN : sv.SeenLNotar f p T b := by
    refine ⟨C, ?_, hT⟩
    have hcard : C.card = n - byz.card := by
      rw [hC, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
        Finset.inter_univ]
    simp only [lQuorum]
    omega
  exact htx.log_on_lnotar p T b b' tr hp hLN hanc htxin

end Minimmit
