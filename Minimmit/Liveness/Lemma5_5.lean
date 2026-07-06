import Mathlib.Data.Finset.Lattice.Fold
import Minimmit.Quorum
import Minimmit.Protocol

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- **Lemma 5.5 (Progression through views).** Every correct processor enters
    every view `v ∈ ℕ≥1`.

    Paper proof, mirrored, by induction on `v`. Suppose every correct
    processor enters view `v` but `p₀` never enters `v + 1`. Then no correct
    processor ever leaves view `v`: a leaver held a nullification or an
    M-notarisation for `v` (`leave_justified`), which propagates to `p₀`
    (lines 2–3, `null_propagates`/`mnotar_propagates`) and would make `p₀`
    leave too. In particular no correct processor ever holds an
    M-notarisation for a view-`v` block. Every correct processor, stuck in
    `v`, eventually votes for a view-`v` block or sends `nullify(v)`
    (`stuck_vote_or_null`). A correct voter for `b` receives the vote-or-
    nullify messages of all `≥ n − f` correct processors; at most `2f` of
    them are votes for `b` itself (else an M-notarisation for `b` would be
    assembled), leaving `≥ n − 3f ≥ 2f + 1` messages that are `nullify(v)` or
    votes for view-`v` blocks `≠ b` — so lines 24–28 fire and the voter sends
    `nullify(v)` (`noprogress_null`). Hence *all* correct processors send
    `nullify(v)`; their `2f + 1`-signer nullification reaches `p₀`, which
    leaves view `v` (`leave_on_null`) — a contradiction. -/
theorem lemma_5_5 {n f : Nat} (sv : StateView n Block Message Tx) (e : Execution n Message)
    (hvd : sv.ViewDiscipline e f) (hnw : sv.NetworkDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f) :
    ∀ v, 1 ≤ v → ∀ p, e.Correct p → ∃ t, sv.curView p t = v := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  intro v
  induction v with
  | zero => exact fun h => absurd h (by omega)
  | succ v ihv =>
    intro _ p₀ hp₀
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hvd.view_start p₀ hp₀, hv0]⟩
    have hv1 : 1 ≤ v := by omega
    by_contra hnever
    -- p₀'s view is capped at v forever
    have hcap₀ : ∀ t, sv.curView p₀ t ≤ v :=
      hvd.le_of_never_eq hp₀ hv1 hnever
    -- p₀ eventually sits at view v forever
    obtain ⟨t₀, ht₀⟩ := ihv hv1 p₀ hp₀
    have hstay₀ : ∀ t, t₀ ≤ t → sv.curView p₀ t = v := fun t htt =>
      le_antisymm (hcap₀ t) (ht₀ ▸ hvd.curView_mono hp₀ htt)
    -- Claim A: no correct processor ever enters view v + 1
    have hcapAll : ∀ q, e.Correct q → ∀ t, sv.curView q t ≤ v := by
      intro q hq
      by_contra hq'
      push Not at hq'
      obtain ⟨t, hqt⟩ := hq'
      obtain ⟨ts, hts, hts1⟩ := hvd.leave_step_of_reach hq hv1
        (hvd.exists_view_eq hq (by omega) t (by omega))
      -- the certificate q held when leaving reaches p₀, which then leaves — absurd
      rcases hvd.leave_justified q ts v hq hts hts1 with hsn | ⟨b, hbv, hsm⟩
      · obtain ⟨T, hT⟩ := hnw.null_propagates q p₀ ts v hq hsn hp₀
        have h1 := hnw.seenNullif_mono hT (Nat.le_max_left T t₀)
        have h2 := hvd.leave_on_null p₀ (max T t₀) v hp₀
          (hstay₀ _ (Nat.le_max_right T t₀)) h1
        have h3 := hcap₀ (max T t₀ + 1)
        omega
      · obtain ⟨T, hT⟩ := hnw.mnotar_propagates q p₀ ts b hq hsm hp₀
        have h1 := hnw.seenMNotar_mono hT (Nat.le_max_left T t₀)
        have h2 := hvd.leave_on_mnotar p₀ (max T t₀) v b hp₀
          (hstay₀ _ (Nat.le_max_right T t₀)) hbv h1
        have h3 := hcap₀ (max T t₀ + 1)
        omega
    -- every correct processor eventually sits at view v forever
    have hstayAll : ∀ q, e.Correct q → ∃ t₁, ∀ t, t₁ ≤ t → sv.curView q t = v := by
      intro q hq
      obtain ⟨t₁, ht₁⟩ := ihv hv1 q hq
      exact ⟨t₁, fun t htt =>
        le_antisymm (hcapAll q hq t) (ht₁ ▸ hvd.curView_mono hq htt)⟩
    -- Claim C: no correct processor ever holds an M-notarisation for a view-v block
    have hnoM : ∀ q, e.Correct q → ∀ t b, sv.bview b = v →
        ¬ sv.SeenMNotar f q t b := by
      intro q hq t b hbv hsm
      obtain ⟨t₁, hst⟩ := hstayAll q hq
      have h1 := hnw.seenMNotar_mono hsm (Nat.le_max_left t t₁)
      have h2 := hvd.leave_on_mnotar q (max t t₁) v b hq
        (hst _ (Nat.le_max_right t t₁)) hbv h1
      have h3 := hcapAll q hq (max t t₁ + 1)
      omega
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
    -- Claim B: every correct processor eventually votes for a view-v block
    -- or sends nullify(v)
    have hVoN : ∀ q, e.Correct q →
        ∃ t, (∃ b, sv.bview b = v ∧ sv.votesAt q t b) ∨ sv.nullsAt q t v :=
      fun q hq => hvd.stuck_vote_or_null q v hq (hcapAll q hq) (ihv hv1 q hq)
    -- Claim D: every correct processor eventually sends nullify(v)
    have hAllNull : ∀ q, e.Correct q → ∃ t, sv.nullsAt q t v := by
      intro q hq
      obtain ⟨tq, hvote | hnull⟩ := hVoN q hq
      case inr => exact ⟨tq, hnull⟩
      obtain ⟨b, hbv, hvb⟩ := hvote
      -- split the correct processors by whether they ever vote for b itself
      set V : Finset (Processor n) := C.filter (fun r => ∃ t, sv.votesAt r t b)
        with hV
      by_cases hVbig : 2 * f + 1 ≤ V.card
      · -- 2f+1 voters for b would assemble an M-notarisation for b at q
        obtain ⟨T, hT⟩ := exists_uniform_time (C := V)
          (P := fun r t => sv.seenAt q t r (sv.voteMsg b))
          (fun r t t' htt hs => hnw.seen_mono q r t t' _ hs htt)
          (fun r hr => by
            rw [hV] at hr
            obtain ⟨hrC, tr, hvr⟩ := Finset.mem_filter.mp hr
            exact hnw.vote_delivered r q tr b (hCmem r hrC) hvr hq)
        exact absurd ⟨V, hVbig, hT⟩ (hnoM q hq T b hbv)
      · -- so ≥ n − 3f ≥ 2f+1 correct processors offer nullify(v) or other votes
        set W : Finset (Processor n) := C \ V with hW
        have hWcard : 2 * f + 1 ≤ W.card := by
          have hVC : V ∩ C = V := by
            rw [hV]
            exact Finset.inter_eq_left.mpr (Finset.filter_subset _ C)
          have h1 : W.card = C.card - V.card := by
            rw [hW, Finset.card_sdiff, hVC]
          omega
        obtain ⟨T, hT⟩ := exists_uniform_time (C := W)
          (P := fun r t => sv.seenAt q t r (sv.nullifyMsg v) ∨
            ∃ b', sv.bview b' = v ∧ b' ≠ b ∧ sv.seenAt q t r (sv.voteMsg b'))
          (fun r t t' htt hs => by
            rcases hs with hs | ⟨b', hb'1, hb'2, hs⟩
            · exact Or.inl (hnw.seen_mono q r t t' _ hs htt)
            · exact Or.inr ⟨b', hb'1, hb'2, hnw.seen_mono q r t t' _ hs htt⟩)
          (fun r hr => by
            rw [hW] at hr
            obtain ⟨hrC, hrV⟩ := Finset.mem_sdiff.mp hr
            have hrc := hCmem r hrC
            obtain ⟨tr, ⟨b', hb'v, hvr⟩ | hnr⟩ := hVoN r hrc
            · have hb'b : b' ≠ b := by
                intro hbb
                rw [hV] at hrV
                exact hrV (Finset.mem_filter.mpr ⟨hrC, tr, hbb ▸ hvr⟩)
              obtain ⟨t', ht'⟩ := hnw.vote_delivered r q tr b' hrc hvr hq
              exact ⟨t', Or.inr ⟨b', hb'v, hb'b, ht'⟩⟩
            · obtain ⟨t', ht'⟩ := hnw.null_delivered r q tr v hrc hnr hq
              exact ⟨t', Or.inl ht'⟩)
        exact hvd.noprogress_null q tq T b v hq hvb hbv (hcapAll q hq)
          ⟨W, hWcard, hT⟩
    -- all correct processors' nullify(v) messages reach p₀ …
    obtain ⟨T, hT⟩ := exists_uniform_time (C := C)
      (P := fun r t => sv.seenAt p₀ t r (sv.nullifyMsg v))
      (fun r t t' htt hs => hnw.seen_mono p₀ r t t' _ hs htt)
      (fun r hr => by
        obtain ⟨tr, hnr⟩ := hAllNull r (hCmem r hr)
        exact hnw.null_delivered r p₀ tr v (hCmem r hr) hnr hp₀)
    -- … forming a nullification that makes p₀ leave view v — contradiction
    have hSN : sv.SeenNullif f p₀ (max T t₀) v :=
      hnw.seenNullif_mono ⟨C, by omega, hT⟩ (Nat.le_max_left T t₀)
    have h2 := hvd.leave_on_null p₀ (max T t₀) v hp₀
      (hstay₀ _ (Nat.le_max_right T t₀)) hSN
    have h3 := hcap₀ (max T t₀ + 1)
    omega

end Minimmit
