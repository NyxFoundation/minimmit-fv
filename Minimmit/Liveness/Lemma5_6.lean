import Minimmit.Quorum
import Minimmit.Protocol

set_option autoImplicit false

namespace Minimmit

/-- **Lemma 5.6 (Correct leaders finalise blocks).** If `lead(v)` is correct
    and the first correct processor to enter view `v` does so at `t ≥ GST`,
    then `lead(v)` disseminates a view-`v` block and that block receives an
    L-notarisation.

    Paper proof, mirrored. All correct processors are in view `≥ v` by
    `t + Δ` (`entry_propagates`), so `lead(v)` is in view `v` at some
    `te ∈ [t, t + Δ]` and its proposal `b` plus supporting certificates reach
    every correct processor by `te + Δ ≤ t + 2Δ` (`leader_package`). Every
    correct vote for a view-`v` block is for a `lead(v)`-signed block (first
    correct vote for any such block is a line 11 vote, by minimality), hence
    for `b` (`propose_unique`). No correct processor sends `nullify(v)`
    before `t + 2Δ`: the timeout fires `2Δ` after an entry `≥ t`, and the
    earliest lines 24–28 nullify would need `2f + 1` qualifying messages
    although its correct signers can offer neither an earlier `nullify(v)`
    (minimality) nor a vote conflicting with `b` (uniqueness). Hence by
    `t + 2Δ` every correct processor — whether still in view `v` (lines 9–11
    fire on the valid proposal) or already leaving it (lines 20–21 vote on
    the way out) — has voted for `b`, and the `n − f` correct votes form an
    L-notarisation.

    Notably `5f + 1 ≤ n` is not needed: only the fault bound
    (`e.FaultBound f`) enters. -/
theorem lemma_5_6 {n f : Nat} {GST Δ : Time} (sv : StateView n)
    (e : Execution n) (hd : sv.VoteDiscipline e)
    (hrd : sv.ReceiptDiscipline e) (hvd : sv.ViewDiscipline e f)
    (hnw : sv.NetworkDiscipline e f) (hld : sv.LeaderDiscipline e f)
    (hsd : sv.SyncDiscipline e f GST Δ)
    (hfb : e.FaultBound f)
    {v : View} (hv1 : 1 ≤ v) {t : Time} (hGST : GST ≤ t)
    (hlc : e.Correct (sv.lead v))
    {q₀ : Processor n} (hq₀ : e.Correct q₀) (hq₀v : sv.curView q₀ t = v)
    (hfirst : ∀ r, e.Correct r → ∀ t' < t, sv.curView r t' < v) :
    ∃ b, sv.bview b = v ∧ e.Signed (sv.lead v) (sv.blockMsg b) ∧
      (∀ p, e.Correct p → ∃ tp, sv.votesAt p tp b) ∧
      sv.LNotarised e f b := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  -- Step 1: every correct processor is in view ≥ v by t + Δ
  have hall : ∀ p, e.Correct p → v ≤ sv.curView p (t + Δ) :=
    hsd.entry_propagates q₀ t v hq₀ hq₀v hGST hfirst
  -- Step 2: the leader is in view v at some te ∈ [t, t + Δ]
  obtain ⟨te, hte_ge, hte_le, hteℓ⟩ :
      ∃ te, t ≤ te ∧ te ≤ t + Δ ∧ sv.curView (sv.lead v) te = v := by
    rcases (hall _ hlc).lt_or_eq with hlt | heq
    · obtain ⟨te, hte⟩ := hvd.exists_view_eq hlc hv1 (t + Δ) (by omega)
      have hle : te ≤ t + Δ := by
        by_contra hgt
        push Not at hgt
        have := hvd.curView_mono hlc (le_of_lt hgt)
        omega
      have hge : t ≤ te := by
        by_contra hlt'
        push Not at hlt'
        have := hfirst _ hlc te hlt'
        omega
      exact ⟨te, hge, hle, hte⟩
    · exact ⟨t + Δ, by omega, le_refl _, heq.symm⟩
  -- Step 3: the leader's proposal package, delivered by te + Δ ≤ t + 2Δ
  obtain ⟨b, b', hbv, hbsig, hlink, hb'v, hpkg⟩ :=
    hsd.leader_package te v hlc hteℓ (by omega)
  have hteΔ : te + Δ ≤ t + 2 * Δ := by omega
  -- Step 4: every correct vote for a view-v block is on a lead(v)-signed
  -- block (strong induction on the vote time: the first vote for any such
  -- block cannot be a line 20 vote), hence is a vote for b
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
    rcases hsd.null_route p₁ (Nat.find hex') v hp₁c hn₁ with
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
  -- Step 6: every correct processor votes for b by t + 2Δ
  have hallvote : ∀ p, e.Correct p → ∃ tp, sv.votesAt p tp b := by
    intro p hp
    have hTv : v ≤ sv.curView p (t + 2 * Δ) :=
      le_trans (hall p hp) (hvd.curView_mono hp (by omega))
    rcases hTv.lt_or_eq with hgt | heq
    · -- p already left view v: it voted on the way out
      obtain ⟨ts, hts, hts1⟩ := hvd.leave_step_of_reach hp hv1
        (hvd.exists_view_eq hp (by omega) (t + 2 * Δ) (by omega))
      have htsT : ts < t + 2 * Δ := by
        by_contra h'
        push Not at h'
        have := hvd.curView_mono hp h'
        omega
      rcases hld.leave_votes_or_null p ts v hp hts hts1 with
        ⟨t', ht', b₀, hb₀v, hv₀⟩ | ⟨t', ht', hn'⟩ | hsn
      · exact ⟨t', (hvoteb p t' b₀ hp hv₀ hb₀v) ▸ hv₀⟩
      · exact absurd hn' (hnonull p t' hp (by omega))
      · obtain ⟨W, hWcard, hWs⟩ := hsn
        obtain ⟨r', hr'W, hr'b⟩ := quorum_exists_nonfaulty hWcard hbyz
        obtain ⟨t'', ht''lt, hn''⟩ := hrd.seen_null_earlier p r' ts v hp
          (hcorr r' hr'b) (hWs r' hr'W)
        exact absurd hn'' (hnonull r' t'' (hcorr r' hr'b) (by omega))
    · -- p is in view v at t + 2Δ: it holds the valid proposal, so it voted
      obtain ⟨hseenb, hseenM, hseenN⟩ := hpkg p hp
      have h1 := hnw.seen_mono p (sv.lead v) (te + Δ) (t + 2 * Δ) _ hseenb hteΔ
      have h2 := hnw.seenMNotar_mono hseenM hteΔ
      have h3 : ∀ w, sv.bview b' < w → w < v → sv.SeenNullif f p (t + 2 * Δ) w :=
        fun w hw1 hw2 => hnw.seenNullif_mono (hseenN w hw1 hw2) hteΔ
      have huniq_seen : ∀ b'', sv.seenAt p (t + 2 * Δ) (sv.lead v)
          (sv.blockMsg b'') → sv.bview b'' = v → b'' = b := by
        intro b'' hs hb''
        have hsig := hrd.seen_signed p (sv.lead v) (t + 2 * Δ) _ hp hs
        exact hld.propose_unique (sv.lead v) b'' b hlc hsig hbsig
          (by rw [hb'', hbv])
      rcases hld.valid_proposal_vote_trigger p (t + 2 * Δ) v b b' hp heq.symm
        h1 hbv huniq_seen hlink hb'v h2 h3 with
        ⟨t', ht', b₀, hb₀v, hv₀⟩ | ⟨t', ht', hn'⟩
      · exact ⟨t', (hvoteb p t' b₀ hp hv₀ hb₀v) ▸ hv₀⟩
      · exact absurd hn' (hnonull p t' hp (by omega))
  -- Step 7: the n − f correct votes form an L-notarisation
  refine ⟨b, hbv, hbsig, hallvote, Finset.univ \ byz, ?_, ?_⟩
  · have hcard : (Finset.univ \ byz : Finset (Processor n)).card =
        n - byz.card := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
        Finset.inter_univ]
    simp only [lQuorum]
    omega
  · intro p hp
    have hpc := hcorr p (Finset.mem_sdiff.mp hp).2
    obtain ⟨tp, hv₀⟩ := hallvote p hpc
    exact (hd.signed_vote p b hpc).mpr ⟨tp, hv₀⟩

end Minimmit
