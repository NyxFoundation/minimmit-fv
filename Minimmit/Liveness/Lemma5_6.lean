import Minimmit.Quorum
import Minimmit.Protocol

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-- Core of Lemmas 5.6 and 5.8, parameterized by a post-GST delivery bound
    `d ≤ Δ` (`d := Δ` gives Lemma 5.6, `d := δ` gives Lemma 5.8): if
    `lead(v)` is correct and the first correct processor to enter view `v`
    does so at `t ≥ GST`, then `lead(v)` signs a view-`v` block `b` and every
    correct processor votes for `b` by `t + 2d`.

    Paper argument. All correct processors are in view `≥ v` by `t + d`
    (`entry_propagates`), so `lead(v)` is in view `v` at some
    `te ∈ [t, t + d]` and its proposal `b` plus supporting certificates reach
    every correct processor by `te + d ≤ t + 2d` (`leader_package`). Every
    correct vote for a view-`v` block is on a `lead(v)`-signed block (strong
    induction on the vote time: the first correct vote for any such block
    cannot be a line 20 vote), hence on `b` (`propose_unique`). No correct
    processor sends `nullify(v)` before `t + 2Δ`: the timeout fires `2Δ`
    after an entry `≥ t`, and the earliest lines 24–28 nullify would need
    `2f + 1` qualifying messages although its correct signers can offer
    neither an earlier `nullify(v)` (minimality) nor a vote conflicting with
    `b` (uniqueness). Hence by `t + 2d ≤ t + 2Δ` every correct processor —
    still in view `v` (lines 9–11 fire on the valid proposal) or already
    leaving it (lines 20–21 vote on the way out) — has voted for `b`. -/
theorem leader_round_votes {n f : Nat} {GST d Δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST d)
    (htd : sv.TimerDiscipline e f Δ) (hdΔ : d ≤ Δ)
    (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {t : Time} (hGST : GST ≤ t)
    (hlc : e.Correct (sv.lead v))
    {q₀ : Processor n} (hq₀ : e.Correct q₀) (hq₀v : sv.curView q₀ t = v)
    (hfirst : ∀ r, e.Correct r → ∀ t' < t, sv.curView r t' < v) :
    ∃ b, sv.bview b = v ∧ e.Signed (sv.lead v) (sv.blockMsg b) ∧
      ∀ p, e.Correct p → ∃ tp ≤ t + 2 * d, sv.votesAt p tp b := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  -- Step 1: every correct processor is in view ≥ v by t + d
  have hall : ∀ p, e.Correct p → v ≤ sv.curView p (t + d) :=
    hdd.entry_propagates q₀ t v hq₀ hq₀v hGST
  -- Step 2: the leader is in view v at some te ∈ [t, t + d]
  obtain ⟨te, hte_ge, hte_le, hteℓ⟩ :
      ∃ te, t ≤ te ∧ te ≤ t + d ∧ sv.curView (sv.lead v) te = v := by
    rcases (hall _ hlc).lt_or_eq with hlt | heq
    · obtain ⟨te, hte_le, hte⟩ :=
        hvd.exists_view_eq_le hlc hv1 (t + d) (by omega)
      have hge : t ≤ te := by
        by_contra hlt'
        push Not at hlt'
        have := hfirst _ hlc te hlt'
        omega
      exact ⟨te, hge, hte_le, hte⟩
    · exact ⟨t + d, by omega, le_refl _, heq.symm⟩
  -- Step 3: the leader's proposal package, delivered by te + d ≤ t + 2d
  obtain ⟨b, b', hbv, hbsig, hlink, hb'v, hpkg⟩ :=
    hdd.leader_package te v hlc hteℓ (by omega)
  have hteΔ : te + d ≤ t + 2 * d := by omega
  -- Step 4: every correct vote for a view-v block is on a lead(v)-signed
  -- block, hence is a vote for b
  have huniq : ∀ tr, ∀ (r : Processor n) (b'' : Block), e.Correct r →
      sv.votesAt r tr b'' → sv.bview b'' = v →
      e.Signed (sv.lead v) (sv.blockMsg b'') := by
    intro tr
    induction tr using Nat.strong_induction_on with
    | _ tr ih =>
      intro r b'' hrc hvr hb''v
      rcases hld.vote_leader_signed r tr b'' hrc hvr with hMseen | hbseen
      · obtain ⟨W, hWcard, hWseen⟩ := hMseen
        obtain ⟨r', hr'W, hr'b⟩ := quorum_exists_nonfaulty hWcard hbyz
        obtain ⟨t', ht'lt, hv'⟩ := hrd.seen_vote_earlier r r' tr b'' hrc
          (hcorr r' hr'b) (hWseen r' hr'W)
        exact ih t' ht'lt r' b'' (hcorr r' hr'b) hv' hb''v
      · rw [hb''v] at hbseen
        exact hrd.seen_signed r (sv.lead v) tr _ hrc hbseen
  have hvoteb : ∀ (r : Processor n) (tr : Time) (b'' : Block), e.Correct r →
      sv.votesAt r tr b'' → sv.bview b'' = v → b'' = b :=
    fun r tr b'' hrc hvr hb''v =>
      hld.propose_unique (sv.lead v) b'' b hlc (huniq tr r b'' hrc hvr hb''v)
        hbsig (by rw [hb''v, hbv])
  -- Step 5: no correct processor sends nullify(v) before t + 2Δ
  have hnonull : ∀ (r : Processor n) (tr : Time), e.Correct r →
      tr < t + 2 * Δ → ¬ sv.nullsAt r tr v := by
    intro r tr hrc hlt hnr
    have hex' : ∃ tm, ∃ r', e.Correct r' ∧ tm < t + 2 * Δ ∧
        sv.nullsAt r' tm v := ⟨tr, r, hrc, hlt, hnr⟩
    obtain ⟨p₁, hp₁c, ht₁lt, hn₁⟩ := Nat.find_spec hex'
    rcases htd.null_route p₁ (Nat.find hex') v hp₁c hn₁ with
      ⟨te₁, hte₁le, hte₁v, htimer⟩ |
      ⟨b₀, tv, htv, hvb₀, hb₀v, W, hWcard, hWq⟩
    · -- timeout route: entry into v is at ≥ t, so the nullify is at ≥ t + 2Δ
      have hge : t ≤ te₁ := by
        by_contra h'
        push Not at h'
        have := hfirst p₁ hp₁c te₁ h'
        omega
      omega
    · -- lines 24–28 route: a correct signer of the qualifying quorum offers
      -- an earlier nullify(v) (contradicting minimality) or a vote
      -- conflicting with b (contradicting uniqueness)
      obtain ⟨r', hr'W, hr'b⟩ := quorum_exists_nonfaulty hWcard hbyz
      have hr'c := hcorr r' hr'b
      rcases hWq r' hr'W with hs | ⟨b'', hb''v, hb''ne, hs⟩
      · obtain ⟨t', ht'lt, hn'⟩ := hrd.seen_null_earlier p₁ r'
          (Nat.find hex') v hp₁c hr'c hs
        exact absurd ⟨r', hr'c, by omega, hn'⟩ (Nat.find_min hex' ht'lt)
      · obtain ⟨t', ht'lt, hv'⟩ := hrd.seen_vote_earlier p₁ r'
          (Nat.find hex') b'' hp₁c hr'c hs
        have h1 := hvoteb r' t' b'' hr'c hv' hb''v
        have h2 := hvoteb p₁ tv b₀ hp₁c hvb₀ hb₀v
        exact hb''ne (by rw [h1, h2])
  -- Step 6: every correct processor votes for b by t + 2d
  refine ⟨b, hbv, hbsig, ?_⟩
  intro p hp
  have hTv : v ≤ sv.curView p (t + 2 * d) :=
    le_trans (hall p hp) (hvd.curView_mono hp (by omega))
  rcases hTv.lt_or_eq with hgt | heq
  · -- p already left view v: it voted on the way out
    obtain ⟨ts, hts, hts1⟩ := hvd.leave_step_of_reach hp hv1
      (hvd.exists_view_eq hp (by omega) (t + 2 * d) (by omega))
    have htsT : ts < t + 2 * d := by
      by_contra h'
      push Not at h'
      have := hvd.curView_mono hp h'
      omega
    rcases hld.leave_votes_or_null p ts v hp hts hts1 with
      ⟨t', ht', b₀, hb₀v, hv₀⟩ | ⟨t', ht', hn'⟩ | hsn
    · exact ⟨t', by omega, (hvoteb p t' b₀ hp hv₀ hb₀v) ▸ hv₀⟩
    · exact absurd hn' (hnonull p t' hp (by omega))
    · obtain ⟨W, hWcard, hWs⟩ := hsn
      obtain ⟨r', hr'W, hr'b⟩ := quorum_exists_nonfaulty hWcard hbyz
      obtain ⟨t'', ht''lt, hn''⟩ := hrd.seen_null_earlier p r' ts v hp
        (hcorr r' hr'b) (hWs r' hr'W)
      exact absurd hn'' (hnonull r' t'' (hcorr r' hr'b) (by omega))
  · -- p is in view v at t + 2d: it holds the valid proposal, so it voted
    obtain ⟨hseenb, hseenM, hseenN⟩ := hpkg p hp
    have h1 := hnw.seen_mono p (sv.lead v) (te + d) (t + 2 * d) _ hseenb hteΔ
    have h2 := hnw.seenMNotar_mono hseenM hteΔ
    have h3 : ∀ w, sv.bview b' < w → w < v →
        sv.SeenNullif f p (t + 2 * d) w :=
      fun w hw1 hw2 => hnw.seenNullif_mono (hseenN w hw1 hw2) hteΔ
    have huniq_seen : ∀ b'', sv.seenAt p (t + 2 * d) (sv.lead v)
        (sv.blockMsg b'') → sv.bview b'' = v → b'' = b := by
      intro b'' hs hb''
      have hsig := hrd.seen_signed p (sv.lead v) (t + 2 * d) _ hp hs
      exact hld.propose_unique (sv.lead v) b'' b hlc hsig hbsig
        (by rw [hb'', hbv])
    rcases hld.valid_proposal_vote_trigger p (t + 2 * d) v b b' hp heq.symm
      h1 hbv huniq_seen hlink hb'v h2 h3 with
      ⟨t', ht', b₀, hb₀v, hv₀⟩ | ⟨t', ht', hn'⟩
    · exact ⟨t', ht', (hvoteb p t' b₀ hp hv₀ hb₀v) ▸ hv₀⟩
    · exact absurd hn' (hnonull p t' hp (by omega))

/-- **Lemma 5.6 (Correct leaders finalise blocks).** If `lead(v)` is correct
    and the first correct processor to enter view `v` does so at `t ≥ GST`,
    then `lead(v)` disseminates a view-`v` block, every correct processor
    votes for it, and it receives an L-notarisation.
    (`leader_round_votes` at delivery bound `d := Δ`; `5f + 1 ≤ n` is not
    needed — only the fault bound enters.) -/
theorem lemma_5_6 {n f : Nat} {GST Δ : Time} (sv : StateView n Block Message Tx)
    (e : Execution n Message) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hdd : sv.DeliveryDiscipline e f GST Δ)
    (htd : sv.TimerDiscipline e f Δ)
    (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {t : Time} (hGST : GST ≤ t)
    (hlc : e.Correct (sv.lead v))
    {q₀ : Processor n} (hq₀ : e.Correct q₀) (hq₀v : sv.curView q₀ t = v)
    (hfirst : ∀ r, e.Correct r → ∀ t' < t, sv.curView r t' < v) :
    ∃ b, sv.bview b = v ∧ e.Signed (sv.lead v) (sv.blockMsg b) ∧
      (∀ p, e.Correct p → ∃ tp, sv.votesAt p tp b) ∧
      sv.LNotarised e f b := by
  classical
  obtain ⟨b, hbv, hbsig, hallvote⟩ := leader_round_votes sv e hrd hvd hnw
    hld hdd htd (le_refl Δ) hfb hv1 hGST hlc hq₀ hq₀v hfirst
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  refine ⟨b, hbv, hbsig,
    fun p hp => (hallvote p hp).imp fun tp h => h.2,
    Finset.univ \ byz, ?_, ?_⟩
  · have hcard : (Finset.univ \ byz : Finset (Processor n)).card =
        n - byz.card := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
        Finset.inter_univ]
    simp only [lQuorum]
    omega
  · intro p hp
    have hpc := hcorr p (Finset.mem_sdiff.mp hp).2
    obtain ⟨tp, _, hv₀⟩ := hallvote p hpc
    exact (hd.signed_vote p b hpc).mpr ⟨tp, hv₀⟩

end Minimmit
