import Mathlib.Logic.Relation
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
  /-- The nullify message `(nullify, v)`. -/
  nullifyMsg : View → Message
  /-- `p` executes the "send `(nullify, v)`" transition at time `t`
      (lines 13–14 upon timeout, or lines 24–28 upon proof of no progress). -/
  nullsAt   : Processor n → Time → View → Prop
  /-- At time `t`, `p`'s message set `S` contains message `m` carrying a valid
      signature by `q`. -/
  seenAt    : Processor n → Time → Processor n → Message → Prop
  /-- `parentLink b0 b`: the hash component `h` of `b = (v, Tr, h)` equals
      `H(b0)`, i.e. `b0` is hash-linked as `b`'s parent. Kept relational: with
      an idealized collision-resistant `H` the relation is functional, but no
      lemma so far needs that. -/
  parentLink : Block → Block → Prop

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

/-- `b0` is an **ancestor** of `b` (§2): the reflexive-transitive closure of
    the hash parent-link. Two blocks are *inconsistent* if neither is an
    ancestor of the other. -/
def Anc {n : Nat} (sv : StateView n) : Block → Block → Prop :=
  Relation.ReflTransGen sv.parentLink

/-- `p` holds at time `t` an **M-notarisation for `b`**: `2f + 1` votes for
    `b` in `S`, each carrying a valid signature by a different processor. -/
def SeenMNotar {n : Nat} (sv : StateView n) (f : Nat)
    (p : Processor n) (t : Time) (b : Block) : Prop :=
  ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧
    ∀ q ∈ W, sv.seenAt p t q (sv.voteMsg b)

/-- `p` holds at time `t` a **nullification for `v`**: `2f + 1` `(nullify, v)`
    messages in `S`, each carrying a valid signature by a different
    processor. -/
def SeenNullif {n : Nat} (sv : StateView n) (f : Nat)
    (p : Processor n) (t : Time) (v : View) : Prop :=
  ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧
    ∀ q ∈ W, sv.seenAt p t q (sv.nullifyMsg v)

/-- **Receipt discipline**: how messages held in a correct processor's `S`
    relate to their signers, as abstract hypotheses (provable in any concrete
    operational model over idealized signatures):

    * `seen_signed` — a validly-signed message held by a correct processor was
      signed by its signer (idealized unforgeability, Barrier 1, at the
      interface level; the transcript-level statement is the axiom in
      `Minimmit.Axioms`);
    * `seen_null_earlier`, `seen_vote_earlier` — messages are received
      strictly after they are sent: a `(nullify, v)` / `(vote, b)` from a
      *correct* signer held at `t` was sent by an actual transition at some
      `t' < t`. -/
structure ReceiptDiscipline {n : Nat} (sv : StateView n) (e : Execution n) :
    Prop where
  seen_signed : ∀ (p q : Processor n) (t : Time) (m : Message),
    e.Correct p → sv.seenAt p t q m → e.Signed q m
  seen_null_earlier : ∀ (p q : Processor n) (t : Time) (v : View),
    e.Correct p → e.Correct q → sv.seenAt p t q (sv.nullifyMsg v) →
    ∃ t' < t, sv.nullsAt q t' v
  seen_vote_earlier : ∀ (p q : Processor n) (t : Time) (b : Block),
    e.Correct p → e.Correct q → sv.seenAt p t q (sv.voteMsg b) →
    ∃ t' < t, sv.votesAt q t' b

/-- **Nullify discipline of Algorithm 1** for correct processors, as abstract
    hypotheses (provable in any concrete operational model):

    * `signed_null` — a correct processor's signed `(nullify, v)` message
      arises from an actual nullify transition;
    * `null_justified` — the paper's key protocol fact for Lemma 5.3: a correct
      processor that voted for a view-`v` block `b` sends `nullify(v)` only via
      lines 24–28, i.e. on holding `≥ 2f + 1` messages, each signed by a
      *different* processor, and each either a `(nullify, v)` or a vote for a
      view-`v` block `≠ b`. The timeout branch (lines 13–14) is excluded
      because it requires `notarised = ⊥`: after voting via line 11,
      `notarised = b ≠ ⊥` until the view is left, a nullify-first ordering is
      barred by the `nullified = false` vote guard (lines 10, 20), and a
      line 20 vote leaves view `v` immediately (line 21). In the lines 24–28
      condition (ii), `notarised ≠ b'` specialises to `b' ≠ b` since
      `notarised = b` when the rule fires. -/
structure NullifyDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  signed_null : ∀ (p : Processor n) (v : View),
    e.Correct p → e.Signed p (sv.nullifyMsg v) → ∃ t, sv.nullsAt p t v
  null_justified : ∀ (p : Processor n) (t tv : Time) (v : View) (b : Block),
    e.Correct p → sv.nullsAt p t v → sv.votesAt p tv b → sv.bview b = v →
    ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧ ∀ q ∈ W,
      sv.seenAt p t q (sv.nullifyMsg v) ∨
      ∃ b', sv.bview b' = v ∧ b' ≠ b ∧ sv.seenAt p t q (sv.voteMsg b')

/-- **Proposal discipline of Algorithm 1** for correct processors: every vote
    is justified by the contents of `S` (provable in any concrete operational
    model). A correct `p` votes for `b` at `t` either

    * via line 20, holding an M-notarisation for `b` itself, or
    * via line 11, holding a *valid proposal* `b` for view `b.view` (§4):
      clause (i) gives the leader-signed block `(v, Tr, h)` — whence the
      hash-link `parentLink b0 b` to the block `b0` of clause (ii); clause
      (ii) gives an M-notarisation for `b0`, with `b0.view < b.view` (as in
      the §3 description: the leader builds on the greatest `v' < v` with an
      M-notarised view-`v'` block, and clause (iii)'s interval presupposes
      `v' < v`); clause (iii) gives a nullification for every view in the
      open interval `(b0.view, b.view)`. -/
structure ProposalDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  vote_justified : ∀ (p : Processor n) (t : Time) (b : Block),
    e.Correct p → sv.votesAt p t b →
    sv.SeenMNotar f p t b ∨
    ∃ b0, sv.parentLink b0 b ∧ sv.bview b0 < sv.bview b ∧
      sv.SeenMNotar f p t b0 ∧
      ∀ v, sv.bview b0 < v → v < sv.bview b → sv.SeenNullif f p t v

/-- `b` receives an **M-notarisation**: at least `2f + 1` processors send
    votes for `b` (§5.1; the `Finset` gives "each signed by a *different*
    processor"). The genesis disjunct of the paper's definition (`b_gen` is
    M/L-notarised by fiat) is omitted at this stage: `Block` is opaque and no
    lemma so far distinguishes `b_gen`; it enters with the ancestry structure
    needed by Lemma 5.4. -/
def MNotarised {n : Nat} (sv : StateView n) (e : Execution n) (f : Nat)
    (b : Block) : Prop :=
  ∃ Q : Finset (Processor n), mQuorum f ≤ Q.card ∧
    ∀ p ∈ Q, e.Signed p (sv.voteMsg b)

/-- `b` receives an **L-notarisation**: at least `n − f` processors send votes
    for `b` (§5.1). Genesis disjunct deferred as in `MNotarised`. -/
def LNotarised {n : Nat} (sv : StateView n) (e : Execution n) (f : Nat)
    (b : Block) : Prop :=
  ∃ Q : Finset (Processor n), lQuorum n f ≤ Q.card ∧
    ∀ p ∈ Q, e.Signed p (sv.voteMsg b)

/-- View `v` receives a **nullification**: at least `2f + 1` processors send
    `(nullify, v)` messages (§5.1). -/
def Nullified {n : Nat} (sv : StateView n) (e : Execution n) (f : Nat)
    (v : View) : Prop :=
  ∃ Q : Finset (Processor n), nullQuorum f ≤ Q.card ∧
    ∀ p ∈ Q, e.Signed p (sv.nullifyMsg v)

/-- Under `5f + 1 ≤ n` an L-notarisation (`n − f` votes) is in particular an
    M-notarisation (`2f + 1` votes). -/
theorem MNotarised_of_LNotarised {n f : Nat} {sv : StateView n}
    {e : Execution n} (hnf : 5 * f + 1 ≤ n) {b : Block}
    (h : sv.LNotarised e f b) : sv.MNotarised e f b := by
  obtain ⟨Q, hQ, hv⟩ := h
  refine ⟨Q, ?_, hv⟩
  simp only [lQuorum] at hQ
  simp only [mQuorum]
  omega

end StateView

end Minimmit
