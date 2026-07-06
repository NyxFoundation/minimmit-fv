import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Minimmit.Responsiveness.Lemma5_8
import Minimmit.Responsiveness.Lemma5_9

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- **Lemma 5.10 (Minimmit is optimistically responsive).** If a transaction
    `tr` is received by a correct processor at `t ≥ GST`, then every correct
    processor adds `tr` to its log by
    `t + 2δ + (f_a + 1)·(2Δ + 2δ + 1) + 4δ` — an explicit form of the paper's
    `t + O(f_a·Δ + δ)`, where `f_a ≤ f` bounds the *actual* number of faulty
    processors.

    Paper proof, mirrored. `tr` reaches every correct processor by `t + δ`
    (`tx_delivered_by`). Let `v₀` be the greatest view any correct processor
    is in at `t + δ`, and `v₁ ∈ (v₀, v₀ + f_a + 1]` a view with a correct
    leader — the `f_a + 1` leaders of that window are pairwise distinct
    (round-robin, `hrr`), so at most `f_a` of them are faulty. All correct
    processors are in view `≥ v₀` by `t + 2δ` (`entry_propagates` from the
    maximal-view processor), and `lemma_5_9_core` advances everyone by one
    view per `2Δ + 2δ + 1` timeslots, so view `v₁` is first entered by
    `t + 2δ + (v₁ − v₀)·(2Δ + 2δ + 1)` — and after `t + δ ≥ GST`. Lemma 5.8
    then gives every correct processor an L-notarisation for the leader's
    view-`v₁` block `b` within `3δ`; `tr` sits in an ancestor of `b`
    (`propose_includes` — the leader had `tr` by `t + δ`, while still in a
    view `≤ v₀ < v₁`), so finalising `b` puts `tr` in every correct log
    within a further `δ` (`log_by`). -/
theorem lemma_5_10 {n f fa : Nat} {GST Δ δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST δ) (htd : sv.TimerDiscipline e f Δ)
    (hδΔ : δ ≤ Δ) (hfd : sv.FinalityDiscipline e f)
    (htx : sv.TxDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfa : e.FaultBound fa) (hfaf : fa ≤ f)
    (hrr : ∀ v w : View, v ≠ w → v < w + n → w < v + n →
      sv.lead v ≠ sv.lead w)
    {tr : Tx} {pᵢ : Processor n} {t : Time}
    (hpc : e.Correct pᵢ) (hGST : GST ≤ t) (hrecv : sv.receivedTx pᵢ t tr) :
    ∀ p, e.Correct p →
      ∃ t' ≤ t + 2 * δ + (fa + 1) * (2 * Δ + 2 * δ + 1) + 4 * δ,
        sv.inLog p t' tr := by
  classical
  obtain ⟨byzA, hbyzA, hcorrA⟩ := hfa
  have hfbf : e.FaultBound f := ⟨byzA, by omega, hcorrA⟩
  -- every correct processor has tr by t + δ
  have htr : ∀ q, e.Correct q → sv.receivedTx q (t + δ) tr := by
    intro q hq
    have h := hdd.tx_delivered_by pᵢ q t tr hpc hrecv hq
    rwa [Nat.max_eq_right hGST] at h
  -- the correct processors, as a Finset
  set Cc : Finset (Processor n) := Finset.univ.filter (fun r => e.Correct r)
    with hCc
  have hCcm : ∀ q, e.Correct q → q ∈ Cc := by
    intro q hq
    rw [hCc]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  have hCcmem : ∀ r ∈ Cc, e.Correct r := by
    intro r hr
    rw [hCc] at hr
    exact (Finset.mem_filter.mp hr).2
  -- v₀: the greatest view any correct processor is in at t + δ
  set v₀ : View := Finset.sup (α := Nat) Cc (fun r => sv.curView r (t + δ))
    with hv₀def
  have hv₀ : ∀ q, e.Correct q → sv.curView q (t + δ) ≤ v₀ := by
    intro q hq
    rw [hv₀def]
    exact Finset.le_sup (f := fun r => sv.curView r (t + δ)) (hCcm q hq)
  have hv₀1 : 1 ≤ v₀ := by
    have h1 := hvd.view_start pᵢ hpc
    have h2 := hvd.curView_mono hpc (Nat.zero_le (t + δ))
    have h3 := hv₀ pᵢ hpc
    omega
  -- v₁ ∈ (v₀, v₀ + fa + 1]: a view with a correct (non-faulty) leader
  obtain ⟨v₁, hv₁ge, hv₁le, hv₁c⟩ :
      ∃ v₁, v₀ + 1 ≤ v₁ ∧ v₁ ≤ v₀ + fa + 1 ∧ sv.lead v₁ ∉ byzA := by
    by_contra h
    push Not at h
    have himg : (Finset.Icc (v₀ + 1) (v₀ + fa + 1)).image sv.lead ⊆ byzA :=
      Finset.image_subset_iff.mpr fun w hw => by
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hw
        exact h w h1 h2
    have hinj : Set.InjOn sv.lead ↑(Finset.Icc (v₀ + 1) (v₀ + fa + 1)) := by
      intro a ha b hb hab
      by_contra hne
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp ha)
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp hb)
      exact hrr a b hne (by omega) (by omega) hab
    have hcard1 := Finset.card_image_of_injOn hinj
    have hcard2 := Finset.card_le_card himg
    rw [hcard1, Nat.card_Icc] at hcard2
    omega
  have hlc : e.Correct (sv.lead v₁) := hcorrA _ hv₁c
  have hv₁1 : 1 ≤ v₁ := by omega
  -- everyone is in view ≥ v₀ by t + 2δ (catch up to the maximal processor)
  have hbase : ∀ p, e.Correct p → v₀ ≤ sv.curView p (t + 2 * δ) := by
    obtain ⟨r₀, hr₀, hr₀v⟩ := Finset.exists_mem_eq_sup Cc
      ⟨pᵢ, hCcm pᵢ hpc⟩ (fun r => sv.curView r (t + δ))
    intro p hp
    have h := hdd.entry_propagates r₀ (t + δ) (sv.curView r₀ (t + δ))
      (hCcmem r₀ hr₀) rfl (by omega) p hp
    have hidx : t + δ + δ = t + 2 * δ := by omega
    rw [hidx] at h
    rw [hv₀def, hr₀v]
    exact h
  -- …and in view ≥ v₀ + k by t + 2δ + k·(2Δ + 2δ + 1) (lemma_5_9_core chain)
  have hchain : ∀ k, ∀ p, e.Correct p →
      v₀ + k ≤ sv.curView p (t + 2 * δ + k * (2 * Δ + 2 * δ + 1)) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      simpa using hbase p hp
    | succ k ih =>
      intro p hp
      have hidx : t + 2 * δ + (k + 1) * (2 * Δ + 2 * δ + 1) =
          t + 2 * δ + k * (2 * Δ + 2 * δ + 1) + 2 * Δ + 2 * δ + 1 := by
        ring
      rw [hidx]
      have hGST' : GST ≤ t + 2 * δ + k * (2 * Δ + 2 * δ + 1) :=
        le_trans hGST (le_trans (Nat.le_add_right t (2 * δ))
          (Nat.le_add_right (t + 2 * δ) _))
      have h := lemma_5_9_core sv e hvd hnw hdd htd hnf hfbf
        (show 1 ≤ v₀ + k by omega) hGST' ih p hp
      omega
  -- Tf: the first timeslot at which a correct processor is in view v₁
  have hk : v₀ + (v₁ - v₀) = v₁ := by omega
  have hreach : ∃ s ≤ t + 2 * δ + (v₁ - v₀) * (2 * Δ + 2 * δ + 1),
      sv.curView pᵢ s = v₁ := by
    have h := hchain (v₁ - v₀) pᵢ hpc
    rw [hk] at h
    exact hvd.exists_view_eq_le hpc hv₁1 _ h
  have hEx : ∃ s, ∃ r, e.Correct r ∧ sv.curView r s = v₁ := by
    obtain ⟨s, _, hs⟩ := hreach
    exact ⟨s, pᵢ, hpc, hs⟩
  obtain ⟨q₁, hq₁c, hq₁v⟩ := Nat.find_spec hEx
  have hTfle : Nat.find hEx ≤
      t + 2 * δ + (v₁ - v₀) * (2 * Δ + 2 * δ + 1) := by
    obtain ⟨s, hsle, hs⟩ := hreach
    exact le_trans (Nat.find_min' hEx ⟨pᵢ, hpc, hs⟩) hsle
  -- the first entry into v₁ is after t + δ, hence after GST
  have hTfgt : t + δ < Nat.find hEx := by
    by_contra h'
    push Not at h'
    have h1 := hvd.curView_mono hq₁c h'
    have h2 := hv₀ q₁ hq₁c
    omega
  have hTfGST : GST ≤ Nat.find hEx := by omega
  have hfirstv₁ : ∀ r, e.Correct r → ∀ s < Nat.find hEx,
      sv.curView r s < v₁ := by
    intro r hrc s hlt
    by_contra hge
    push Not at hge
    obtain ⟨s', hs'le, hs'⟩ := hvd.exists_view_eq_le hrc hv₁1 s hge
    exact absurd ⟨r, hrc, hs'⟩ (Nat.find_min hEx (by omega))
  -- Lemma 5.8 at (v₁, Tf): L-notarisations for the leader's block b
  obtain ⟨b, hbv, hbsig, hres⟩ := lemma_5_8 sv e hd hrd hvd hnw hld hdd htd
    hδΔ hfd hnf hfbf hv₁1 hTfGST hlc hq₁c hq₁v hfirstv₁
  -- tr sits in an ancestor of b
  have hℓv : sv.curView (sv.lead v₁) (t + δ) < v₁ := by
    have := hv₀ (sv.lead v₁) hlc
    omega
  obtain ⟨b', hanc, htxin⟩ := htx.propose_includes v₁ tr b (t + δ) hlc
    (htr (sv.lead v₁) hlc) hℓv hbsig hbv
  -- every correct processor logs tr by Tf + 4δ ≤ the stated bound
  intro p hp
  obtain ⟨hLN, _, _⟩ := hres p hp
  obtain ⟨t', ht'le, hlog⟩ := hdd.log_by p (Nat.find hEx + 3 * δ) b b' tr hp
    hLN hanc htxin (by omega)
  refine ⟨t', ?_, hlog⟩
  set A := (v₁ - v₀) * (2 * Δ + 2 * δ + 1) with hAdef
  set B := (fa + 1) * (2 * Δ + 2 * δ + 1) with hBdef
  have hAB : A ≤ B := by
    rw [hAdef, hBdef]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

end Minimmit
