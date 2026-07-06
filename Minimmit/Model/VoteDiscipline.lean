import Minimmit.Model.Basic

/-!
# The model satisfies `VoteDiscipline` (issue #21, slice a)

`Minimmit.Model.voteDiscipline` instantiates `StateView.VoteDiscipline` for
the operational model of `Minimmit.Model.Basic`, unconditionally in the
oracle `Env`. Proof shape:

* a vote in a slot's emissions pins the decision to `vote b` (line 11) or
  `mnotarAdvance (some b)` (line 20) — `vote_emitted`;
* both decisions' guards carry `b.view = v` and `notarised = ⊥`
  (`decide_eq_vote`, `decide_eq_mnotarAdvance_some`), giving `vote_view`
  and `vote_guard`; each slot emits at most one vote (`vote_step`);
* `vote_sets`: a line 11 vote sets `notarised := b` and keeps the view;
  `notarised` then persists while the view is unchanged
  (`notarised_persists`) — the only writes are the vote action, barred by
  its `notarised = ⊥` guard, and the view advances, barred by view
  monotonicity (`view_mono`). A line 20 vote leaves the view within its
  slot, so the same-view premise is unsatisfiable at any later slot.
-/

set_option autoImplicit false

namespace Minimmit.Model

variable {n : Nat} {Tx : Type}

/-! ## Guard characterizations of `decide` -/

/-- Guard facts of a `vote` decision (lines 9–11): the chosen block is a
    valid proposal for the current view, and the line 10 test
    `notarised = ⊥ ∧ nullified = false` held. -/
theorem decide_eq_vote {f Δ : Nat} {env : Env n Tx} {p : Processor n}
    {t : Time} {s : PState Tx} {b : MBlock Tx}
    (h : decide f Δ env p t s = Action.vote b) :
    ValidProposal (S env p t) f env.lead s.view b ∧
      s.notarised = none ∧ s.nullified = false := by
  unfold decide at h
  -- `split_ifs` discharges every branch whose equation is a top-level
  -- constructor clash; only the line 9–11 branch survives.
  split_ifs at h with h1 h2 h3 h4 h5 h6
  injection h with hb
  exact hb ▸ ⟨h2.1.choose_spec, h2.2.1, h2.2.2⟩

/-- Guard facts of an `mnotarAdvance (some b)` decision (lines 19–21 with
    the line 20 vote): the voted block is of the current view, `S` holds an
    M-notarisation for it, and the line 20 test
    `notarised = ⊥ ∧ nullified = false` held. -/
theorem decide_eq_mnotarAdvance_some {f Δ : Nat} {env : Env n Tx}
    {p : Processor n} {t : Time} {s : PState Tx} {b : MBlock Tx}
    (h : decide f Δ env p t s = Action.mnotarAdvance (some b)) :
    MBlock.bview b = s.view ∧ HasMNotar (S env p t) f b ∧
      s.notarised = none ∧ s.nullified = false := by
  unfold decide at h
  -- `split_ifs` discharges every top-level constructor clash; the lines
  -- 19–21 branch survives twice, split on the inner line 20 test.
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7
  · injection h with hb
    injection hb with hb
    exact hb ▸ ⟨h5.choose_spec.1, h5.choose_spec.2, h6.1, h6.2⟩
  · injection h with hb
    injection hb

/-- A vote in a slot's emissions pins the decision: the slot decided
    `vote b` (line 11) or `mnotarAdvance (some b)` (line 20). -/
theorem vote_emitted {f Δ : Nat} {env : Env n Tx} {p : Processor n}
    {t : Time} {b : MBlock Tx} (h : MMsg.vote b ∈ emitsAt f Δ env p t) :
    decide f Δ env p t (traj f Δ env p t) = Action.vote b ∨
      decide f Δ env p t (traj f Δ env p t) =
        Action.mnotarAdvance (some b) := by
  rw [emitsAt_def] at h
  cases hd : decide f Δ env p t (traj f Δ env p t) with
  | propose b0 => rw [hd] at h; simp [emits] at h
  | vote b0 =>
      rw [hd] at h
      simp [emits] at h
      subst h
      exact Or.inl rfl
  | timeoutNull => rw [hd] at h; simp [emits] at h
  | nullAdvance => rw [hd] at h; simp [emits] at h
  | mnotarAdvance ob =>
      cases ob with
      | none => rw [hd] at h; simp [emits] at h
      | some b0 =>
          rw [hd] at h
          simp [emits] at h
          subst h
          exact Or.inr rfl
  | noprogressNull => rw [hd] at h; simp [emits] at h
  | idle => rw [hd] at h; simp [emits] at h

/-! ## View monotonicity and `notarised` persistence -/

/-- Every action either keeps the view or advances it by exactly one. -/
theorem apply_view_eq_or_succ (t : Time) (a : Action Tx) (s : PState Tx) :
    (apply t a s).view = s.view ∨ (apply t a s).view = s.view + 1 := by
  cases a <;> simp [apply]

/-- Per-slot view monotonicity. -/
theorem view_mono_succ (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    (t : Time) :
    (traj f Δ env p t).view ≤ (traj f Δ env p (t + 1)).view := by
  rw [traj_succ]
  rcases apply_view_eq_or_succ t (decide f Δ env p t (traj f Δ env p t))
      (traj f Δ env p t) with h | h <;> omega

/-- Views never decrease along the trajectory. -/
theorem view_mono (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    {t t' : Time} (htt' : t ≤ t') :
    (traj f Δ env p t).view ≤ (traj f Δ env p t').view := by
  induction t', htt' using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ u _ ih => exact ih.trans (view_mono_succ f Δ env p u)

/-- `notarised` persists while the view is unchanged: once
    `notarised = some b` at the start of slot `t`, it still holds at the
    start of any later slot `t'` whose slot-start view equals that of `t`.
    The only writes to `notarised` are the vote action — barred by its
    `notarised = ⊥` guard — and the view advances — barred by the
    equal-view premise together with view monotonicity. -/
theorem notarised_persists (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    {t t' : Time} {b : MBlock Tx} (htt' : t ≤ t')
    (hb : (traj f Δ env p t).notarised = some b)
    (hv : (traj f Δ env p t').view = (traj f Δ env p t).view) :
    (traj f Δ env p t').notarised = some b := by
  revert hv
  induction t', htt' using Nat.le_induction with
  | base => exact fun _ => hb
  | succ u hu ih =>
      intro hv
      have hvu : (traj f Δ env p u).view = (traj f Δ env p t).view := by
        have h1 := view_mono f Δ env p hu
        have h2 := view_mono_succ f Δ env p u
        omega
      have hbu := ih hvu
      cases hd : decide f Δ env p u (traj f Δ env p u) with
      | propose b0 => rw [traj_succ, hd]; simpa [apply] using hbu
      | vote b0 =>
          have hguard := (decide_eq_vote hd).2.1
          rw [hbu] at hguard
          exact absurd hguard (by simp)
      | timeoutNull => rw [traj_succ, hd]; simpa [apply] using hbu
      | nullAdvance =>
          rw [traj_succ, hd] at hv
          simp [apply] at hv
          omega
      | mnotarAdvance ob =>
          rw [traj_succ, hd] at hv
          simp [apply] at hv
          omega
      | noprogressNull => rw [traj_succ, hd]; simpa [apply] using hbu
      | idle => rw [traj_succ, hd]; simpa [apply] using hbu

/-! ## The `VoteDiscipline` fields, at the model level -/

/-- H2, `vote_view`: votes carry the slot-start view. -/
theorem bview_of_vote_emitted {f Δ : Nat} {env : Env n Tx}
    {p : Processor n} {t : Time} {b : MBlock Tx}
    (h : MMsg.vote b ∈ emitsAt f Δ env p t) :
    MBlock.bview b = (traj f Δ env p t).view := by
  rcases vote_emitted h with hd | hd
  · exact (decide_eq_vote hd).1.2.1
  · exact (decide_eq_mnotarAdvance_some hd).1

/-- H3, `vote_guard`: both vote-emitting guards require `notarised = ⊥`. -/
theorem notarised_none_of_vote_emitted {f Δ : Nat} {env : Env n Tx}
    {p : Processor n} {t : Time} {b : MBlock Tx}
    (h : MMsg.vote b ∈ emitsAt f Δ env p t) :
    (traj f Δ env p t).notarised = none := by
  rcases vote_emitted h with hd | hd
  · exact (decide_eq_vote hd).2.1
  · exact (decide_eq_mnotarAdvance_some hd).2.2.1

/-- H4, `vote_step`: a slot emits at most one vote. -/
theorem vote_emitted_unique {f Δ : Nat} {env : Env n Tx} {p : Processor n}
    {t : Time} {b b' : MBlock Tx} (h : MMsg.vote b ∈ emitsAt f Δ env p t)
    (h' : MMsg.vote b' ∈ emitsAt f Δ env p t) : b = b' := by
  rcases vote_emitted h with hd | hd <;>
      rcases vote_emitted h' with hd' | hd' <;>
      rw [hd] at hd'
  · injection hd'
  · injection hd'
  · injection hd'
  · injection hd' with hb
    injection hb

/-- H5, `vote_sets`: after voting for `b` at slot `t`, `notarised = some b`
    at every later slot whose slot-start view equals that of `t`. A line 11
    vote sets `notarised := b` keeping the view, and `notarised_persists`
    carries it; a line 20 vote advances the view within slot `t`, so by
    monotonicity the equal-view premise is unsatisfiable. -/
theorem notarised_eq_of_vote_emitted {f Δ : Nat} {env : Env n Tx}
    {p : Processor n} {t : Time} {b : MBlock Tx}
    (h : MMsg.vote b ∈ emitsAt f Δ env p t) {t' : Time} (htt' : t < t')
    (hv : (traj f Δ env p t').view = (traj f Δ env p t).view) :
    (traj f Δ env p t').notarised = some b := by
  rcases vote_emitted h with hd | hd
  · have hb1 : (traj f Δ env p (t + 1)).notarised = some b := by
      simp [traj_succ, hd, apply]
    have hv1 : (traj f Δ env p (t + 1)).view = (traj f Δ env p t).view := by
      simp [traj_succ, hd, apply]
    have hle : t + 1 ≤ t' := htt'
    exact notarised_persists f Δ env p hle hb1 (by omega)
  · have hstep : (traj f Δ env p (t + 1)).view =
        (traj f Δ env p t).view + 1 := by
      simp [traj_succ, hd, apply]
    have hmono : (traj f Δ env p (t + 1)).view ≤
        (traj f Δ env p t').view := view_mono f Δ env p htt'
    omega

/-! ## The instance -/

/-- **The operational model satisfies the voting discipline** (issue #21,
    slice a): the `toStateView` / `toExecution` instantiation proves every
    field of `StateView.VoteDiscipline`, unconditionally in the oracle
    `Env` — the discipline is enforced by the state machine alone. -/
theorem voteDiscipline (f Δ : Nat) (env : Env n Tx) :
    (toStateView f Δ env).VoteDiscipline (toExecution f Δ env) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- vote_view
    intro p t b _ hvote
    exact bview_of_vote_emitted hvote
  · -- vote_guard
    intro p t b _ hvote
    exact notarised_none_of_vote_emitted hvote
  · -- vote_sets
    intro p t b _ hvote t' htt' hview
    exact notarised_eq_of_vote_emitted hvote htt' hview
  · -- vote_step
    intro p t b b' _ hvote hvote'
    exact vote_emitted_unique hvote hvote'
  · -- signed_vote
    intro p b hp
    have hp' : p ∉ env.byz := hp
    show (if p ∈ env.byz then env.byzSigned p (MMsg.vote b)
          else ∃ t, MMsg.vote b ∈ emitsAt f Δ env p t) ↔
        ∃ t, MMsg.vote b ∈ emitsAt f Δ env p t
    rw [if_neg hp']

end Minimmit.Model
