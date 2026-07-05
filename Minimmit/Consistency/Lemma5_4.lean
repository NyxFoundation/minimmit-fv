import Minimmit.Quorum
import Minimmit.Consistency.Lemma5_2
import Minimmit.Consistency.Lemma5_3

set_option autoImplicit false

namespace Minimmit

/-- Core of Lemma 5.4, by strong induction on the view (the Lean form of the
    paper's least-counterexample choice of `v₂`): if `b₁` is L-notarised, then
    *every* M-notarised block `b₂` with `b₁.view ≤ b₂.view` has `b₁` as an
    ancestor.

    * `b₂.view = b₁.view` — Lemma 5.2 forces `b₂ = b₁`.
    * `b₂.view > b₁.view` — an M-notarisation for `b₂` contains a vote by some
      correct processor; take the *first* timeslot `t₀` at which a correct
      processor votes for `b₂` (`Nat.find`). That vote cannot be a line 20
      vote: the M-notarisation for `b₂` it would require contains a vote by a
      correct processor sent at some `t' < t₀` (`seen_vote_earlier`),
      contradicting minimality. So it is a line 11 vote on a valid proposal,
      yielding a hash-linked parent `b₀` with `b₀.view < b₂.view`, an
      M-notarisation for `b₀`, and nullifications for all views in
      `(b₀.view, b₂.view)`. If `b₀.view < b₁.view` then `b₁.view` lies in that
      interval, so view `b₁.view` receives a nullification — contradicting
      Lemma 5.3. Hence `b₁.view ≤ b₀.view < b₂.view`, the induction hypothesis
      gives `Anc b₁ b₀`, and the parent link extends it to `Anc b₁ b₂`. -/
theorem anc_of_lnotarised {n f : Nat} (sv : StateView n) (e : Execution n)
    (hd : sv.VoteDiscipline e) (hrd : sv.ReceiptDiscipline e)
    (hnd : sv.NullifyDiscipline e f) (hpd : sv.ProposalDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {b₁ : Block} (hL₁ : sv.LNotarised e f b₁) :
    ∀ v₂, ∀ b₂ : Block, sv.MNotarised e f b₂ → sv.bview b₂ = v₂ →
      sv.bview b₁ ≤ v₂ → sv.Anc b₁ b₂ := by
  classical
  obtain ⟨byz, hbyz, hcorr⟩ := hfb
  intro v₂
  induction v₂ using Nat.strong_induction_on with
  | _ v₂ ih =>
    intro b₂ hM₂ hv₂ hle
    rcases hle.lt_or_eq with hlt | heq
    · -- b₁.view < v₂: locate the first correct vote for b₂
      obtain ⟨Q, hQcard, hQvotes⟩ := hM₂
      obtain ⟨q₀, hq₀Q, hq₀b⟩ := quorum_exists_nonfaulty hQcard hbyz
      have hex : ∃ t, ∃ p, p ∉ byz ∧ sv.votesAt p t b₂ := by
        obtain ⟨t, ht⟩ := (hd.signed_vote q₀ b₂ (hcorr q₀ hq₀b)).mp
          (hQvotes q₀ hq₀Q)
        exact ⟨t, q₀, hq₀b, ht⟩
      obtain ⟨p₁, hp₁b, hp₁vote⟩ := Nat.find_spec hex
      have hp₁c : e.Correct p₁ := hcorr p₁ hp₁b
      rcases hpd.vote_justified p₁ (Nat.find hex) b₂ hp₁c hp₁vote with
        hMseen | ⟨b₀, hlink, hb₀lt, hM₀seen, hnulls⟩
      · -- line 20 vote: some correct processor voted for b₂ strictly earlier
        obtain ⟨W, hWcard, hWseen⟩ := hMseen
        obtain ⟨q, hqW, hqb⟩ := quorum_exists_nonfaulty hWcard hbyz
        obtain ⟨t', ht'lt, hv'⟩ := hrd.seen_vote_earlier p₁ q (Nat.find hex)
          b₂ hp₁c (hcorr q hqb) (hWseen q hqW)
        exact absurd ⟨q, hqb, hv'⟩ (Nat.find_min hex ht'lt)
      · -- line 11 vote on a valid proposal with parent b₀
        have hM₀ : sv.MNotarised e f b₀ := by
          obtain ⟨W₀, hW₀card, hW₀seen⟩ := hM₀seen
          exact ⟨W₀, hW₀card,
            fun q hq => hrd.seen_signed p₁ q (Nat.find hex) _ hp₁c (hW₀seen q hq)⟩
        rcases Nat.lt_or_ge (sv.bview b₀) (sv.bview b₁) with hb₀v₁ | hb₀v₁
        · -- b₀.view < b₁.view: view b₁.view receives a nullification — absurd
          obtain ⟨W₁, hW₁card, hW₁seen⟩ :=
            hnulls (sv.bview b₁) hb₀v₁ (by omega)
          have hnull : sv.Nullified e f (sv.bview b₁) :=
            ⟨W₁, hW₁card,
              fun q hq => hrd.seen_signed p₁ q (Nat.find hex) _ hp₁c (hW₁seen q hq)⟩
          exact absurd hnull
            (lemma_5_3 sv e hd hrd hnd hnf ⟨byz, hbyz, hcorr⟩ hL₁)
        · -- b₁.view ≤ b₀.view < v₂: recurse through the parent
          have hanc₀ : sv.Anc b₁ b₀ :=
            ih (sv.bview b₀) (by omega) b₀ hM₀ rfl hb₀v₁
          exact Relation.ReflTransGen.tail hanc₀ hlink
    · -- b₂.view = b₁.view: Lemma 5.2 forces b₂ = b₁
      have hb : b₂ = b₁ :=
        lemma_5_2 sv e hd hnf ⟨byz, hbyz, hcorr⟩ (by omega) hL₁ hM₂
      rw [hb]
      exact Relation.ReflTransGen.refl

/-- **Lemma 5.4 (Consistency), block form.** No two inconsistent blocks both
    receive L-notarisations: if `b` and `b'` are L-notarised then one is an
    ancestor of the other (whichever has the smaller view). This is the §5.1
    content of the paper's Consistency lemma; the log-level statement of §2
    follows from it via the finalisation mechanics (obtain all ancestors, log
    the concatenated payloads), which — together with the collision-resistant
    hash making `parentLink` functional — is outside this abstraction level. -/
theorem lemma_5_4 {n f : Nat} (sv : StateView n) (e : Execution n)
    (hd : sv.VoteDiscipline e) (hrd : sv.ReceiptDiscipline e)
    (hnd : sv.NullifyDiscipline e f) (hpd : sv.ProposalDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    {b b' : Block} (hL : sv.LNotarised e f b) (hL' : sv.LNotarised e f b') :
    sv.Anc b b' ∨ sv.Anc b' b := by
  rcases Nat.le_total (sv.bview b) (sv.bview b') with h | h
  · exact Or.inl (anc_of_lnotarised sv e hd hrd hnd hpd hnf hfb hL
      (sv.bview b') b' (StateView.MNotarised_of_LNotarised hnf hL') rfl h)
  · exact Or.inr (anc_of_lnotarised sv e hd hrd hnd hpd hnf hfb hL'
      (sv.bview b) b (StateView.MNotarised_of_LNotarised hnf hL) rfl h)

end Minimmit
