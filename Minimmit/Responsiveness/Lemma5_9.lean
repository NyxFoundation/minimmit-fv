import Minimmit.Quorum
import Minimmit.Protocol

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- Core of Lemma 5.9, in "synchronised start" form: if every correct
    processor is in view `≥ v` at `s₀ ≥ GST`, then every correct processor is
    in view `> v` by `s₀ + 2Δ + 2δ + 1` — whether or not `lead(v)` is
    correct. (No first-entry hypothesis: it is consumed by Lemma 5.10, where
    view `v` may have been entered before GST.)

    Paper argument, timed. Suppose `p₀` is still in view `v` at the deadline.
    Then no correct processor holds a nullification for `v` or an
    M-notarisation for a view-`v` block at any `tq ≤ s₀ + 2Δ + δ` — it would
    propagate to `p₀` by `s₀ + 2Δ + 2δ` and force it out. Hence no correct
    processor leaves `v` through slot `s₀ + 2Δ + δ` (`leave_justified`), and
    each — in view `v` a full `2Δ` after `s₀` — votes for a view-`v` block or
    sends `nullify(v)` by `s₀ + 2Δ` (`vote_or_null_by`). A correct voter for
    `b` receives all these messages by `s₀ + 2Δ + δ`: at most `2f` of them are
    votes for `b` itself (else an M-notarisation for `b` assembles), leaving
    `≥ n − 3f ≥ 2f + 1` qualifying messages, and — still in view `v` at the
    next slot, as `noprogress_null_by` requires to rule out a line 20 exit
    vote — lines 24–28 fire. Thus *all* correct processors send `nullify(v)`
    by `s₀ + 2Δ + δ`; the assembled nullification reaches `p₀` by
    `s₀ + 2Δ + 2δ` and forces it out — contradiction. -/
theorem lemma_5_9_core {n f : Nat} {GST Δ δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message)
    (hvd : sv.ViewDiscipline e f) (hnw : sv.NetworkDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST δ) (htd : sv.TimerDiscipline e f Δ)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {s₀ : Time} (hGST : GST ≤ s₀)
    (hall : ∀ r, e.Correct r → v ≤ sv.curView r s₀) :
    ∀ p, e.Correct p → v < sv.curView p (s₀ + 2 * Δ + 2 * δ + 1) := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  by_contra hex
  push Not at hex
  obtain ⟨p₀, hp₀c, hp₀le⟩ := hex
  -- p₀ sits at view v throughout [s₀, s₀ + 2Δ + 2δ + 1]
  have hstay₀ : ∀ s, s₀ ≤ s → s ≤ s₀ + 2 * Δ + 2 * δ + 1 →
      sv.curView p₀ s = v := by
    intro s hs1 hs2
    have h1 := hall p₀ hp₀c
    have h2 := hvd.curView_mono hp₀c hs1
    have h3 := hvd.curView_mono hp₀c hs2
    omega
  -- no correct processor holds a view-v M-notarisation by s₀ + 2Δ + δ
  have hNoM : ∀ (q : Processor n) (tq : Time) (b : Block), e.Correct q →
      tq ≤ s₀ + 2 * Δ + δ → sv.bview b = v → ¬ sv.SeenMNotar f q tq b := by
    intro q tq b hqc htq hbv hsm
    have h1 := hdd.mnotar_propagates_by q p₀ tq b hqc hsm hp₀c
    have h3 := hnw.seenMNotar_mono h1
      (show max GST tq + δ ≤ s₀ + 2 * Δ + 2 * δ by omega)
    have h4 := hvd.leave_on_mnotar p₀ (s₀ + 2 * Δ + 2 * δ) v b hp₀c
      (hstay₀ _ (by omega) (by omega)) hbv h3
    have h5 := hstay₀ (s₀ + 2 * Δ + 2 * δ + 1) (by omega) (le_refl _)
    omega
  -- nor a nullification for v
  have hNoN : ∀ (q : Processor n) (tq : Time), e.Correct q →
      tq ≤ s₀ + 2 * Δ + δ → ¬ sv.SeenNullif f q tq v := by
    intro q tq hqc htq hsn
    have h1 := hdd.null_propagates_by q p₀ tq v hqc hsn hp₀c
    have h3 := hnw.seenNullif_mono h1
      (show max GST tq + δ ≤ s₀ + 2 * Δ + 2 * δ by omega)
    have h4 := hvd.leave_on_null p₀ (s₀ + 2 * Δ + 2 * δ) v hp₀c
      (hstay₀ _ (by omega) (by omega)) h3
    have h5 := hstay₀ (s₀ + 2 * Δ + 2 * δ + 1) (by omega) (le_refl _)
    omega
  -- so every correct processor sits at view v throughout [s₀, s₀ + 2Δ + δ + 1]
  -- (one slot past the message deadline: leaving during slot s₀ + 2Δ + δ would
  -- still need a certificate held at ≤ s₀ + 2Δ + δ, which hNoM/hNoN exclude)
  have hstayAll : ∀ q, e.Correct q → ∀ s, s₀ ≤ s → s ≤ s₀ + 2 * Δ + δ + 1 →
      sv.curView q s = v := by
    intro q hqc s hs1 hs2
    have hge : v ≤ sv.curView q s :=
      le_trans (hall q hqc) (hvd.curView_mono hqc hs1)
    rcases hge.lt_or_eq with hgt | heq
    · exfalso
      obtain ⟨s', hs'le, hs'⟩ :=
        hvd.exists_view_eq_le hqc (show 1 ≤ v + 1 by omega) s (by omega)
      obtain ⟨ts, hts, hts1⟩ := hvd.leave_step_of_reach hqc hv1 ⟨s', hs'⟩
      have htsle : ts < s := by
        by_contra h'
        push Not at h'
        have := hvd.curView_mono hqc h'
        omega
      rcases hvd.leave_justified q ts v hqc hts hts1 with hsn | ⟨b, hbv, hsm⟩
      · exact hNoN q ts hqc (by omega) hsn
      · exact hNoM q ts b hqc (by omega) hbv hsm
    · exact heq.symm
  -- by s₀ + 2Δ every correct processor has voted in v or nullified v
  have hVoN : ∀ q, e.Correct q → ∃ t' ≤ s₀ + 2 * Δ,
      (∃ b, sv.bview b = v ∧ sv.votesAt q t' b) ∨ sv.nullsAt q t' v :=
    fun q hqc => htd.vote_or_null_by q s₀ v hqc
      (hstayAll q hqc s₀ (le_refl _) (by omega))
      (hstayAll q hqc (s₀ + 2 * Δ) (by omega) (by omega))
  -- the correct processors
  set C : Finset (Processor n) := Finset.univ \ byz with hC
  have hCmem : ∀ r ∈ C, e.Correct r := by
    intro r hr
    rw [hC] at hr
    exact hcorr r (Finset.mem_sdiff.mp hr).2
  have hCcard : n - f ≤ C.card := by
    have hcard : C.card = n - byz.card := by
      rw [hC, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
        Finset.inter_univ]
    omega
  -- every correct processor sends nullify(v) by s₀ + 2Δ + δ
  have hAllNull : ∀ q, e.Correct q → ∃ t' ≤ s₀ + 2 * Δ + δ,
      sv.nullsAt q t' v := by
    intro q hqc
    obtain ⟨tq, htq, hvote | hnull⟩ := hVoN q hqc
    case inr => exact ⟨tq, by omega, hnull⟩
    obtain ⟨b, hbv, hvb⟩ := hvote
    set V : Finset (Processor n) :=
      C.filter (fun r => ∃ t' ≤ s₀ + 2 * Δ, sv.votesAt r t' b) with hV
    by_cases hVbig : 2 * f + 1 ≤ V.card
    · -- 2f+1 voters for b would assemble an M-notarisation for b at q
      exfalso
      have hSM : sv.SeenMNotar f q (s₀ + 2 * Δ + δ) b := by
        refine ⟨V, hVbig, ?_⟩
        intro r hr
        rw [hV] at hr
        obtain ⟨hrC, t', ht', hvr⟩ := Finset.mem_filter.mp hr
        have hseen := hdd.vote_delivered_by r q t' b (hCmem r hrC) hvr hqc
        exact hnw.seen_mono q r _ _ _ hseen (by omega)
      exact hNoM q (s₀ + 2 * Δ + δ) b hqc (le_refl _) hbv hSM
    · -- so ≥ n − 3f ≥ 2f + 1 qualifying messages arrive: lines 24–28 fire
      set W : Finset (Processor n) := C \ V with hW
      have hWcard : 2 * f + 1 ≤ W.card := by
        have hVC : V ∩ C = V := by
          rw [hV]
          exact Finset.inter_eq_left.mpr (Finset.filter_subset _ C)
        have h1 : W.card = C.card - V.card := by
          rw [hW, Finset.card_sdiff, hVC]
        omega
      have hforms : ∀ r ∈ W,
          sv.seenAt q (s₀ + 2 * Δ + δ) r (sv.nullifyMsg v) ∨
          ∃ b', sv.bview b' = v ∧ b' ≠ b ∧
            sv.seenAt q (s₀ + 2 * Δ + δ) r (sv.voteMsg b') := by
        intro r hr
        rw [hW] at hr
        obtain ⟨hrC, hrV⟩ := Finset.mem_sdiff.mp hr
        have hrc := hCmem r hrC
        obtain ⟨t', ht', ⟨b', hb'v, hvr⟩ | hnr⟩ := hVoN r hrc
        · have hb'b : b' ≠ b := by
            intro hbb
            rw [hV] at hrV
            exact hrV (Finset.mem_filter.mpr ⟨hrC, t', ht', hbb ▸ hvr⟩)
          have hseen := hdd.vote_delivered_by r q t' b' hrc hvr hqc
          exact Or.inr ⟨b', hb'v, hb'b,
            hnw.seen_mono q r _ _ _ hseen (by omega)⟩
        · have hseen := hdd.null_delivered_by r q t' v hrc hnr hqc
          exact Or.inl (hnw.seen_mono q r _ _ _ hseen (by omega))
      exact htd.noprogress_null_by q tq (s₀ + 2 * Δ + δ) b v hqc hvb hbv
        (hstayAll q hqc (s₀ + 2 * Δ + δ) (by omega) (by omega))
        (hstayAll q hqc (s₀ + 2 * Δ + δ + 1) (by omega) (le_refl _)) (by omega)
        ⟨W, hWcard, hforms⟩
  -- their nullifies reach p₀ by s₀ + 2Δ + 2δ: a nullification forces it out
  have hSN : sv.SeenNullif f p₀ (s₀ + 2 * Δ + 2 * δ) v := by
    refine ⟨C, by omega, ?_⟩
    intro r hr
    have hrc := hCmem r hr
    obtain ⟨t', ht', hnr⟩ := hAllNull r hrc
    have hseen := hdd.null_delivered_by r p₀ t' v hrc hnr hp₀c
    exact hnw.seen_mono p₀ r _ _ _ hseen (by omega)
  have h4 := hvd.leave_on_null p₀ (s₀ + 2 * Δ + 2 * δ) v hp₀c
    (hstay₀ _ (by omega) (by omega)) hSN
  have h5 := hstay₀ (s₀ + 2 * Δ + 2 * δ + 1) (by omega) (le_refl _)
  omega

/-- **Lemma 5.9.** If the first correct processor to enter view `v` does so
    at `t ≥ GST` then, whether or not `lead(v)` is correct, all correct
    processors leave view `v` by `t + 2Δ + 3δ` — all correct processors are
    in view `≥ v` by `t + δ` (`entry_propagates`), and `lemma_5_9_core`
    applies from `s₀ := t + δ`. -/
theorem lemma_5_9 {n f : Nat} {GST Δ δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message)
    (hvd : sv.ViewDiscipline e f) (hnw : sv.NetworkDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST δ) (htd : sv.TimerDiscipline e f Δ)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {t : Time} (hGST : GST ≤ t)
    {q₀ : Processor n} (hq₀ : e.Correct q₀) (hq₀v : sv.curView q₀ t = v) :
    ∀ p, e.Correct p → v < sv.curView p (t + 2 * Δ + 3 * δ + 1) := by
  have hall : ∀ r, e.Correct r → v ≤ sv.curView r (t + δ) :=
    hdd.entry_propagates q₀ t v hq₀ hq₀v hGST
  intro p hp
  have h := lemma_5_9_core sv e hvd hnw hdd htd hnf hfb hv1
    (show GST ≤ t + δ by omega) hall p hp
  have hmono := hvd.curView_mono hp
    (show t + δ + 2 * Δ + 2 * δ + 1 ≤ t + 2 * Δ + 3 * δ + 1 by omega)
  omega

end Minimmit
