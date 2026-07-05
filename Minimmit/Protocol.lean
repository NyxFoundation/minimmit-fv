import Minimmit.Basic

set_option autoImplicit false

namespace Minimmit

/-- **Abstract per-processor state-transition interface for Algorithm 1**
    (Barrier 3, MVP: the protocol mechanics are modeled as an interface, not
    implemented operationally). Bundles the block/message encodings and the
    per-processor local state that the voting discipline ranges over. A concrete
    operational model can later *construct* a `StateView` without changing any
    theorem statement. -/
structure StateView (n : Nat) where
  /-- The view `b.view` a block belongs to. -/
  bview     : Block → View
  /-- The vote message `(vote, b)`. -/
  voteMsg   : Block → Message
  /-- The view processor `p`'s local state is in at time `t`. -/
  curView   : Processor n → Time → View
  /-- `p`'s local variable `notarised` at time `t`; `none` is the default `⊥`
      ("`⊥` is a default value, different than any block"), to which the
      variable is initialized and reset upon entering any view (lines 17, 21). -/
  notarised : Processor n → Time → Option Block
  /-- `p` executes the "send `(vote, b)`" transition at time `t`
      (lines 10–11 and 20). -/
  votesAt   : Processor n → Time → Block → Prop

namespace StateView

/-- **Voting discipline of Algorithm 1** for correct processors, as
    per-processor state-transition hypotheses (provable in any concrete
    operational model):

    * `vote_view` — a vote is cast for a block of the current view;
    * `vote_guard` — a vote is only cast while `notarised = ⊥` (lines 10, 20);
    * `vote_sets` — upon voting for `b`, `p` either sets `notarised := b`
      (line 11) and does not redefine it before entering the next view, or
      immediately enters the next view (lines 20–21) — and views only ever
      increase, so a left view is never re-entered. Both branches give: at any
      strictly later time still in the same view, `notarised = some b` (in the
      second branch the premise is unsatisfiable);
    * `vote_step` — transitions are atomic: a single vote transition sends a
      single vote message, so at most one vote per processor per timeslot;
    * `signed_vote` — a correct processor signed `(vote, b)` iff it executed
      the vote transition at some time (links the transcript's signature
      predicate to the state machine). -/
structure VoteDiscipline {n : Nat} (sv : StateView n) (e : Execution n) : Prop where
  vote_view : ∀ (p : Processor n) (t : Time) (b : Block),
    e.Correct p → sv.votesAt p t b → sv.bview b = sv.curView p t
  vote_guard : ∀ (p : Processor n) (t : Time) (b : Block),
    e.Correct p → sv.votesAt p t b → sv.notarised p t = none
  vote_sets : ∀ (p : Processor n) (t : Time) (b : Block),
    e.Correct p → sv.votesAt p t b →
    ∀ t' : Time, t < t' → sv.curView p t' = sv.curView p t →
    sv.notarised p t' = some b
  vote_step : ∀ (p : Processor n) (t : Time) (b b' : Block),
    e.Correct p → sv.votesAt p t b → sv.votesAt p t b' → b = b'
  signed_vote : ∀ (p : Processor n) (b : Block),
    e.Correct p → (e.Signed p (sv.voteMsg b) ↔ ∃ t, sv.votesAt p t b)

end StateView

end Minimmit
