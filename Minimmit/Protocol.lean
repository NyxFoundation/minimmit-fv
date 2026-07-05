import Mathlib.Data.Nat.Find
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
  /-- The round-robin leader schedule `lead(v) = p_{j+1}, j = v mod n`. Kept
      abstract; the rotation property enters as a hypothesis where needed. -/
  lead      : View → Processor n
  /-- The proposal message for block `b = (v, Tr, h)`, signed by `lead(v)`
      (lines 5–7, `ProposeChild`). -/
  blockMsg  : Block → Message
  /-- `p` has received transaction `tr` by time `t`. -/
  receivedTx : Processor n → Time → Tx → Prop
  /-- `tr ∈ b.Tr`: the transaction is in the block's payload. -/
  txIn      : Tx → Block → Prop
  /-- `tr ∈ log_p(t)`: the transaction is in `p`'s log at time `t` (§2,
      finalisation: upon holding an L-notarisation for `b` and all ancestors
      of `b`, the log extends `b.Tr*`). -/
  inLog     : Processor n → Time → Tx → Prop

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

/-- `p` holds at time `t` an **L-notarisation for `b`**: `n − f` votes for
    `b` in `S`, each carrying a valid signature by a different processor. -/
def SeenLNotar {n : Nat} (sv : StateView n) (f : Nat)
    (p : Processor n) (t : Time) (b : Block) : Prop :=
  ∃ W : Finset (Processor n), lQuorum n f ≤ W.card ∧
    ∀ q ∈ W, sv.seenAt p t q (sv.voteMsg b)

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

/-- **View discipline of Algorithm 1** for correct processors: how the local
    view `v` starts, advances, and reacts to the contents of `S` (provable in
    any concrete operational model):

    * `view_start` — `v` is initially `1` (Table 2);
    * `view_step` — lines 17 and 21 are the only updates to `v`, each
      `v := v + 1`;
    * `leave_justified` — a processor advances only upon holding a
      nullification for the current view (lines 16–17) or an M-notarisation
      for a current-view block (lines 19–21);
    * `leave_on_null`, `leave_on_mnotar` — conversely, holding such a
      certificate while in view `v` advances the view at that timeslot
      (lines 16–17, 19–21);
    * `stuck_vote_or_null` — a correct processor that enters view `v` and
      never leaves it eventually votes for a view-`v` block or sends
      `nullify(v)`: its timer reaches `T = 2Δ` (lines 13–14); the guards
      `notarised ≠ ⊥` / `nullified = true` can only block the timeout if a
      view-`v` vote / a `nullify(v)` was already sent;
    * `noprogress_null` — a correct processor that voted for a view-`v` block
      `b`, never leaves view `v`, and holds `≥ 2f + 1` messages, each signed
      by a different processor and each a `(nullify, v)` or a vote for a
      view-`v` block `≠ b`, eventually sends `nullify(v)`: either
      `nullified = true` already (so it sent one before) or lines 24–28
      fire. -/
structure ViewDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  view_start : ∀ (p : Processor n), e.Correct p → sv.curView p 0 = 1
  view_step : ∀ (p : Processor n) (t : Time), e.Correct p →
    sv.curView p (t + 1) = sv.curView p t ∨
    sv.curView p (t + 1) = sv.curView p t + 1
  leave_justified : ∀ (p : Processor n) (t : Time) (v : View), e.Correct p →
    sv.curView p t = v → sv.curView p (t + 1) = v + 1 →
    sv.SeenNullif f p t v ∨ ∃ b, sv.bview b = v ∧ sv.SeenMNotar f p t b
  leave_on_null : ∀ (p : Processor n) (t : Time) (v : View), e.Correct p →
    sv.curView p t = v → sv.SeenNullif f p t v → v < sv.curView p (t + 1)
  leave_on_mnotar : ∀ (p : Processor n) (t : Time) (v : View) (b : Block),
    e.Correct p → sv.curView p t = v → sv.bview b = v →
    sv.SeenMNotar f p t b → v < sv.curView p (t + 1)
  stuck_vote_or_null : ∀ (p : Processor n) (v : View), e.Correct p →
    (∀ t, sv.curView p t ≤ v) → (∃ t, sv.curView p t = v) →
    ∃ t, (∃ b, sv.bview b = v ∧ sv.votesAt p t b) ∨ sv.nullsAt p t v
  noprogress_null : ∀ (p : Processor n) (tv t : Time) (b : Block) (v : View),
    e.Correct p → sv.votesAt p tv b → sv.bview b = v →
    (∀ t', sv.curView p t' ≤ v) →
    (∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧ ∀ r ∈ W,
      sv.seenAt p t r (sv.nullifyMsg v) ∨
      ∃ b', sv.bview b' = v ∧ b' ≠ b ∧ sv.seenAt p t r (sv.voteMsg b')) →
    ∃ t', sv.nullsAt p t' v

namespace ViewDiscipline

variable {n f : Nat} {sv : StateView n} {e : Execution n}

/-- Views never decrease (from `view_step`). -/
theorem curView_mono (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) {t t' : Time} (htt : t ≤ t') :
    sv.curView p t ≤ sv.curView p t' := by
  induction t', htt using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ t' _ iht =>
    rcases h.view_step p t' hp with heq | heq <;> omega

/-- Views advance one at a time, so every intermediate view is visited (at
    some earlier-or-equal time). -/
theorem exists_view_eq_le (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) {u : View} (hu1 : 1 ≤ u) :
    ∀ t, u ≤ sv.curView p t → ∃ t' ≤ t, sv.curView p t' = u := by
  intro t
  induction t with
  | zero =>
    intro hut
    have h0 := h.view_start p hp
    exact ⟨0, le_refl _, by omega⟩
  | succ t iht =>
    intro hut
    by_cases hle : u ≤ sv.curView p t
    · obtain ⟨t', ht'le, ht'⟩ := iht hle
      exact ⟨t', by omega, ht'⟩
    · rcases h.view_step p t hp with heq | heq <;>
        exact ⟨t + 1, le_refl _, by omega⟩

/-- Views advance one at a time, so every intermediate view is visited. -/
theorem exists_view_eq (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) {u : View} (hu1 : 1 ≤ u) :
    ∀ t, u ≤ sv.curView p t → ∃ t', sv.curView p t' = u := by
  intro t hut
  obtain ⟨t', _, ht'⟩ := h.exists_view_eq_le hp hu1 t hut
  exact ⟨t', ht'⟩

/-- Reaching view `v` takes at least `v − 1` timeslots: the view advances by
    at most one per step from its initial value `1`. -/
theorem curView_le_succ (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) : ∀ t, sv.curView p t ≤ t + 1 := by
  intro t
  induction t with
  | zero => exact le_of_eq (h.view_start p hp)
  | succ t iht => rcases h.view_step p t hp with heq | heq <;> omega

/-- A processor that never shows view `v + 1` is capped at `v` forever. -/
theorem le_of_never_eq (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) {v : View} (hv1 : 1 ≤ v)
    (hnever : ¬ ∃ t, sv.curView p t = v + 1) : ∀ t, sv.curView p t ≤ v := by
  intro t
  by_contra hgt
  push Not at hgt
  exact hnever (h.exists_view_eq hp (by omega) t (by omega))

/-- A processor that reaches view `v + 1` crossed it in a single step from
    view `v`. -/
theorem leave_step_of_reach (h : sv.ViewDiscipline e f) {p : Processor n}
    (hp : e.Correct p) {v : View} (hv1 : 1 ≤ v)
    (hreach : ∃ t, sv.curView p t = v + 1) :
    ∃ t, sv.curView p t = v ∧ sv.curView p (t + 1) = v + 1 := by
  classical
  have ht₁ : sv.curView p (Nat.find hreach) = v + 1 := Nat.find_spec hreach
  have ht₁0 : Nat.find hreach ≠ 0 := by
    intro h0'
    rw [h0'] at ht₁
    have h0 := h.view_start p hp
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero ht₁0
  have ht' : Nat.find hreach = t + 1 := by omega
  have hmin : sv.curView p t ≠ v + 1 := fun hh =>
    Nat.find_min hreach (by omega) hh
  rw [ht'] at ht₁
  rcases h.view_step p t hp with heq | heq <;> exact ⟨t, by omega, by omega⟩

end ViewDiscipline

/-- **Network discipline** (Barrier 4, eventual-delivery fragment): the
    message set `S` only grows (Table 2), every message disseminated by a
    correct processor is eventually received by every correct processor
    ("a message sent at `t` arrives by `max{GST, t} + Δ`" — Lemma 5.5 only
    needs *eventually*), and nullifications / M-notarisations propagate as
    whole certificates because processors forward new ones on receipt
    (lines 2–3) — per-message delivery does not cover their
    Byzantine-signed members. -/
structure NetworkDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  seen_mono : ∀ (p q : Processor n) (t t' : Time) (m : Message),
    sv.seenAt p t q m → t ≤ t' → sv.seenAt p t' q m
  vote_delivered : ∀ (q p : Processor n) (t : Time) (b : Block),
    e.Correct q → sv.votesAt q t b → e.Correct p →
    ∃ t', sv.seenAt p t' q (sv.voteMsg b)
  null_delivered : ∀ (q p : Processor n) (t : Time) (v : View),
    e.Correct q → sv.nullsAt q t v → e.Correct p →
    ∃ t', sv.seenAt p t' q (sv.nullifyMsg v)
  null_propagates : ∀ (q p : Processor n) (t : Time) (v : View),
    e.Correct q → sv.SeenNullif f q t v → e.Correct p →
    ∃ t', sv.SeenNullif f p t' v
  mnotar_propagates : ∀ (q p : Processor n) (t : Time) (b : Block),
    e.Correct q → sv.SeenMNotar f q t b → e.Correct p →
    ∃ t', sv.SeenMNotar f p t' b

namespace NetworkDiscipline

variable {n f : Nat} {sv : StateView n} {e : Execution n}

theorem seenNullif_mono (h : sv.NetworkDiscipline e f) {p : Processor n}
    {t t' : Time} {v : View} (hs : sv.SeenNullif f p t v) (htt : t ≤ t') :
    sv.SeenNullif f p t' v := by
  obtain ⟨W, hW, hall⟩ := hs
  exact ⟨W, hW, fun r hr => h.seen_mono p r t t' _ (hall r hr) htt⟩

theorem seenMNotar_mono (h : sv.NetworkDiscipline e f) {p : Processor n}
    {t t' : Time} {b : Block} (hs : sv.SeenMNotar f p t b) (htt : t ≤ t') :
    sv.SeenMNotar f p t' b := by
  obtain ⟨W, hW, hall⟩ := hs
  exact ⟨W, hW, fun r hr => h.seen_mono p r t t' _ (hall r hr) htt⟩

end NetworkDiscipline

/-- **Leader/proposal discipline of Algorithm 1** for correct processors
    (provable in any concrete operational model):

    * `propose_unique` — a correct processor signs at most one proposal per
      view: `ProposeChild` runs once per view (`proposed` flag, lines 5–7,
      reset on entry) and views are never revisited;
    * `vote_leader_signed` — clause (i) of the valid-proposal definition (§4):
      a line 11 vote is cast on a proposal signed by `lead(v)` held in `S`; a
      line 20 vote is cast on a block with an M-notarisation in `S`;
    * `valid_proposal_vote_trigger` — lines 9–11 are not skipped: if a
      correct processor in view `v` holds a valid proposal `b` for `v`
      (clauses (i)–(iii)), then by that timeslot it has voted for some
      view-`v` block (line 11 fires now, or `notarised ≠ ⊥` records an
      earlier view-`v` vote) or it sent `nullify(v)` strictly earlier
      (`nullified = true`);
    * `leave_votes_or_null` — a correct processor leaving view `v` advanced
      via line 17 (holding a nullification for `v`) or via lines 20–21, and
      in the latter case it voted for a view-`v` block on the way out unless
      `notarised ≠ ⊥` (an earlier view-`v` vote) or `nullified = true` (an
      earlier `nullify(v)`). -/
structure LeaderDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  propose_unique : ∀ (p : Processor n) (b b' : Block), e.Correct p →
    e.Signed p (sv.blockMsg b) → e.Signed p (sv.blockMsg b') →
    sv.bview b = sv.bview b' → b = b'
  vote_leader_signed : ∀ (p : Processor n) (t : Time) (b : Block),
    e.Correct p → sv.votesAt p t b →
    sv.SeenMNotar f p t b ∨ sv.seenAt p t (sv.lead (sv.bview b)) (sv.blockMsg b)
  valid_proposal_vote_trigger : ∀ (p : Processor n) (t : Time) (v : View)
    (b b' : Block), e.Correct p → sv.curView p t = v →
    sv.seenAt p t (sv.lead v) (sv.blockMsg b) → sv.bview b = v →
    (∀ b'', sv.seenAt p t (sv.lead v) (sv.blockMsg b'') → sv.bview b'' = v →
      b'' = b) →
    sv.parentLink b' b → sv.bview b' < v → sv.SeenMNotar f p t b' →
    (∀ w, sv.bview b' < w → w < v → sv.SeenNullif f p t w) →
    (∃ t' ≤ t, ∃ b₀, sv.bview b₀ = v ∧ sv.votesAt p t' b₀) ∨
    (∃ t' < t, sv.nullsAt p t' v)
  leave_votes_or_null : ∀ (p : Processor n) (t : Time) (v : View),
    e.Correct p → sv.curView p t = v → sv.curView p (t + 1) = v + 1 →
    (∃ t' ≤ t, ∃ b₀, sv.bview b₀ = v ∧ sv.votesAt p t' b₀) ∨
    (∃ t' ≤ t, sv.nullsAt p t' v) ∨ sv.SeenNullif f p t v

/-- **Post-GST synchrony discipline** (Barrier 4, timed fragment), with the
    delivery rule "a message sent at `t` arrives by `max{GST, t} + Δ`" and
    the timeout `T = 2Δ` (provable in any concrete operational model):

    * `entry_propagates` — if the *first* correct processor to be in view `v`
      is there at `tq ≥ GST`, every correct processor is in view `≥ v` by
      `tq + Δ`: the certificate that let it enter (or, for `v = 1`, nothing)
      is forwarded on receipt (lines 2–3) and delivered by `tq + Δ`;
    * `leader_package` — a correct `lead(v)` in view `v` at `te ≥ GST`
      proposed a view-`v` block `b` at its first view-`v` timeslot
      (lines 5–7): `SelectParent` picked a parent `b'` with an M-notarisation
      in its `S` and, by maximality of `b'.view` over its climb history,
      nullifications for every view in `(b'.view, v)`; the proposal and the
      supporting certificates (forwarded, lines 2–3) reach every correct
      processor by `te + Δ`;
    * `null_route` — a `nullify(v)` by a correct processor is sent either
      upon timeout, `2Δ` after its entry into view `v` (lines 13–14), or via
      the lines 24–28 no-progress rule, having voted for a view-`v` block and
      holding `2f + 1` distinct-signer qualifying messages. -/
structure SyncDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) (GST Δ : Time) : Prop where
  entry_propagates : ∀ (q : Processor n) (tq : Time) (v : View),
    e.Correct q → sv.curView q tq = v → GST ≤ tq →
    (∀ r, e.Correct r → ∀ t' < tq, sv.curView r t' < v) →
    ∀ p, e.Correct p → v ≤ sv.curView p (tq + Δ)
  leader_package : ∀ (te : Time) (v : View), e.Correct (sv.lead v) →
    sv.curView (sv.lead v) te = v → GST ≤ te →
    ∃ b b', sv.bview b = v ∧ e.Signed (sv.lead v) (sv.blockMsg b) ∧
      sv.parentLink b' b ∧ sv.bview b' < v ∧
      ∀ p, e.Correct p →
        sv.seenAt p (te + Δ) (sv.lead v) (sv.blockMsg b) ∧
        sv.SeenMNotar f p (te + Δ) b' ∧
        ∀ w, sv.bview b' < w → w < v → sv.SeenNullif f p (te + Δ) w
  null_route : ∀ (p : Processor n) (tn : Time) (v : View),
    e.Correct p → sv.nullsAt p tn v →
    (∃ te ≤ tn, sv.curView p te = v ∧ te + 2 * Δ ≤ tn) ∨
    (∃ (b : Block) (tv : Time), tv ≤ tn ∧ sv.votesAt p tv b ∧
      sv.bview b = v ∧
      ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧ ∀ r ∈ W,
        sv.seenAt p tn r (sv.nullifyMsg v) ∨
        ∃ b'', sv.bview b'' = v ∧ b'' ≠ b ∧ sv.seenAt p tn r (sv.voteMsg b''))

/-- **Transaction/finalisation discipline of Algorithm 1** for correct
    processors (provable in any concrete operational model):

    * `propose_includes` — `ProposeChild` (§4): the leader of view `v` forms
      `b.Tr` from all transactions it has received that are not already in an
      ancestor's payload; so a transaction received while still in a view
      `< v` ends up in the payload of `b` or of one of its ancestors;
    * `log_on_lnotar` — finalisation (§2 and lines 31–32): a correct
      processor holding an L-notarisation for `b` finalises `b`; every
      ancestor of an L-notarised block received an M-notarisation before `b`
      was proposed (correct processors vote only on parents with
      M-notarisations in `S`), so `≥ f + 1` correct processors disseminated
      each ancestor and `p` eventually obtains them all, extending its log
      with `b.Tr*` — in particular with any `tr` in an ancestor's payload. -/
structure TxDiscipline {n : Nat} (sv : StateView n) (e : Execution n)
    (f : Nat) : Prop where
  propose_includes : ∀ (v : View) (tr : Tx) (b : Block) (t₀ : Time),
    e.Correct (sv.lead v) → sv.receivedTx (sv.lead v) t₀ tr →
    sv.curView (sv.lead v) t₀ < v →
    e.Signed (sv.lead v) (sv.blockMsg b) → sv.bview b = v →
    ∃ b', sv.Anc b' b ∧ sv.txIn tr b'
  log_on_lnotar : ∀ (p : Processor n) (t : Time) (b b' : Block) (tr : Tx),
    e.Correct p → sv.SeenLNotar f p t b → sv.Anc b' b → sv.txIn tr b' →
    ∃ t', sv.inLog p t' tr

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
