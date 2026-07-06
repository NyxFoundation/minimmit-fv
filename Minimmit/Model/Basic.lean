import Mathlib.Data.Set.Lattice
import Minimmit.Protocol

/-!
# Operational model of Algorithm 1 (issue #21, slice a)

A concrete per-processor state machine for Algorithm 1 (paper p. 11) over
idealized carriers, instantiating the abstract `StateView` / `Execution`
interface of `Minimmit.Protocol`. Design decisions (agreed on issue #21):

* **Priority-sequential semantics, one guarded block per timeslot.** The
  per-processor state is sampled at slot start: `traj f Δ env p t` is `p`'s
  state at the *start* of slot `t`; during slot `t` the processor executes
  the *first* enabled guarded block of Algorithm 1 (priority order: lines
  5–7, 9–11, 13–14, 16–17, 19–21, 24–28), producing `traj f Δ env p (t + 1)`
  and emitting messages (`emitsAt`). At most one view advance per slot keeps
  `ViewDiscipline.view_step` satisfiable (see the slot-granularity caveat in
  `docs/formalization-strategy.md`).
* **`Env` is an adversary/network oracle.** Message arrival, Byzantine
  signing, leader proposals and transaction arrival are free data;
  faithfulness constraints (delivery deadlines, authenticity, `ProposeChild`
  content) arrive as hypotheses on `Env` in later slices, not baked in here.
* **Idealized hash.** A block's hash component *is* the parent reference
  (`MBlock.node v tr parent`), collision-free by construction.
-/

set_option autoImplicit false

namespace Minimmit.Model

variable {n : Nat} {Tx : Type}

/-- Model blocks: the genesis block `b_gen`, or `(v, Tr, h)` where the
    idealized hash `h` is the parent reference itself — collision-free by
    construction (Barrier 1 discharged structurally). -/
inductive MBlock (Tx : Type) : Type where
  | gen : MBlock Tx
  | node (v : View) (tr : List Tx) (parent : MBlock Tx) : MBlock Tx

/-- The view `b.view` a model block belongs to; genesis has view `0` (§2). -/
def MBlock.bview : MBlock Tx → View
  | .gen => 0
  | .node v _ _ => v

/-- `b.Tr*` (§2): the concatenated payloads of `b` and all its ancestors,
    oldest first. -/
def trStarM : MBlock Tx → List Tx
  | .gen => []
  | .node _ tr parent => trStarM parent ++ tr

/-- Model messages: proposals, votes and nullifies. Notarisation forwarding
    (lines 2–3) is represented by delivering the member votes themselves. -/
inductive MMsg (Tx : Type) : Type where
  | block (b : MBlock Tx) : MMsg Tx
  | vote (b : MBlock Tx) : MMsg Tx
  | nullify (v : View) : MMsg Tx

/-- A signed message `⟨m⟩_q`: signer × payload (idealized signature). -/
abbrev SMsg (n : Nat) (Tx : Type) : Type := Processor n × MMsg Tx

/-- The adversary/network oracle: all the free data a model execution is
    parameterized by. No faithfulness constraints are baked in — they arrive
    as hypotheses on `Env` in later slices, keeping this slice's theorem
    unconditional. -/
structure Env (n : Nat) (Tx : Type) where
  /-- The Byzantine processors. -/
  byz : Finset (Processor n)
  /-- The leader schedule `lead(v)`. Kept abstract, as in `StateView`. -/
  lead : View → Processor n
  /-- The signed messages the network places in `p`'s message set `S` during
      slot `t` — delayed honest sends and Byzantine injections alike; timing
      and authenticity constraints are later-slice hypotheses, not baked
      in. -/
  arrival : Processor n → Time → Set (SMsg n Tx)
  /-- What the adversary lets Byzantine processors sign (`Execution.Signed`
      for `p ∈ byz`). -/
  byzSigned : Processor n → MMsg Tx → Prop
  /-- The proposal the leader of view `v` would disseminate at slot `t`
      (`ProposeChild` / `SelectParent` content deferred to a later slice;
      its faithfulness clauses become `Env` constraints there). -/
  proposal : Processor n → Time → View → MBlock Tx
  /-- Transaction arrival: `p` has received transaction `tr` by slot `t`. -/
  txArrive : Processor n → Time → Tx → Prop

/-- The initial message set (Table 2): `S` starts out holding `b_gen`
    together with its M/L-notarisations — idealized as every processor's
    genesis vote. -/
def Sinit : Set (SMsg n Tx) := {sm | sm.2 = MMsg.vote MBlock.gen}

/-- `p`'s message set `S` at the *start* of slot `t`: the initial set plus
    everything the network delivered during slots strictly before `t`.
    Slot-`t` decisions therefore read slot-start knowledge, and `S` is
    monotone by construction (`S_mono`). -/
def S (env : Env n Tx) (p : Processor n) (t : Time) : Set (SMsg n Tx) :=
  Sinit ∪ ⋃ t' < t, env.arrival p t'

/-- Membership in `S`, unfolded. -/
theorem mem_S {env : Env n Tx} {p : Processor n} {t : Time}
    {sm : SMsg n Tx} :
    sm ∈ S env p t ↔
      sm.2 = MMsg.vote MBlock.gen ∨ ∃ t' < t, sm ∈ env.arrival p t' := by
  simp [S, Sinit]

/-- The message set only grows (Table 2). -/
theorem S_mono (env : Env n Tx) (p : Processor n) {t t' : Time}
    (htt' : t ≤ t') : S env p t ⊆ S env p t' := by
  intro sm hsm
  rcases mem_S.mp hsm with h0 | ⟨u, hu, harr⟩
  · exact mem_S.mpr (Or.inl h0)
  · exact mem_S.mpr (Or.inr ⟨u, Nat.lt_of_lt_of_le hu htt', harr⟩)

/-- `T` holds an **M-notarisation for `b`**: `2f + 1` votes for `b`, each
    signed by a different processor (§5.1). -/
def HasMNotar (T : Set (SMsg n Tx)) (f : Nat) (b : MBlock Tx) : Prop :=
  ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧
    ∀ q ∈ W, (q, MMsg.vote b) ∈ T

/-- `T` holds a **nullification for `v`**: `2f + 1` `(nullify, v)` messages,
    each signed by a different processor (§5.1). -/
def HasNullif (T : Set (SMsg n Tx)) (f : Nat) (v : View) : Prop :=
  ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧
    ∀ q ∈ W, (q, MMsg.nullify v) ∈ T

/-- `T` holds an **L-notarisation for `b`**: `n − f` votes for `b`, each
    signed by a different processor (§5.1). -/
def HasLNotar (T : Set (SMsg n Tx)) (f : Nat) (b : MBlock Tx) : Prop :=
  ∃ W : Finset (Processor n), lQuorum n f ≤ W.card ∧
    ∀ q ∈ W, (q, MMsg.vote b) ∈ T

/-- `b` is a **valid proposal** for view `v` against message set `T` (§4,
    clauses (i)–(iii)): (i) `T` holds `b` signed by `lead v`, with
    `b.view = v` and `b` hash-linked to a parent `b'` of an earlier view;
    (ii) `T` holds an M-notarisation for `b'`; (iii) `T` holds a
    nullification for every view strictly between `b'.view` and `v`. -/
def ValidProposal (T : Set (SMsg n Tx)) (f : Nat)
    (lead : View → Processor n) (v : View) (b : MBlock Tx) : Prop :=
  (lead v, MMsg.block b) ∈ T ∧ MBlock.bview b = v ∧
    ∃ b', (∃ w tr, b = MBlock.node w tr b') ∧ MBlock.bview b' < v ∧
      HasMNotar T f b' ∧ ∀ w, MBlock.bview b' < w → w < v → HasNullif T f w

/-- Per-processor local state, sampled at slot start (Table 2). -/
structure PState (Tx : Type) where
  /-- The current view `v`. -/
  view : View
  /-- The slot at which the current view was entered; the timer reads
      `T = t − entry`. -/
  entry : Time
  /-- The `nullified` flag. -/
  nullified : Bool
  /-- The `proposed` flag. -/
  proposed : Bool
  /-- The `notarised` variable; `none` is the default `⊥`. -/
  notarised : Option (MBlock Tx)

/-- The initial state (Table 2): view `1` entered at slot `0`, flags clear,
    `notarised = ⊥`. -/
def PState.init : PState Tx := ⟨1, 0, false, false, none⟩

/-- The slot action: which guarded block of Algorithm 1 (if any) fires
    during a slot. `mnotarAdvance voted` records in `voted` the line 20
    vote, if its guard held. -/
inductive Action (Tx : Type) : Type where
  /-- Lines 5–7: `ProposeChild`. -/
  | propose (b : MBlock Tx) : Action Tx
  /-- Lines 9–11: vote for a valid proposal and set `notarised := b`. -/
  | vote (b : MBlock Tx) : Action Tx
  /-- Lines 13–14: nullify on timeout. -/
  | timeoutNull : Action Tx
  /-- Lines 16–17: enter the next view on a nullification. -/
  | nullAdvance : Action Tx
  /-- Lines 19–21: enter the next view on an M-notarisation for a
      current-view block, voting on the way out if line 20's guard held. -/
  | mnotarAdvance (voted : Option (MBlock Tx)) : Action Tx
  /-- Lines 24–28: nullify on proof of no progress. -/
  | noprogressNull : Action Tx
  /-- No guard enabled. -/
  | idle : Action Tx

open Classical in
/-- The slot decision: the *first* enabled guarded block of Algorithm 1,
    read against the slot-start state `s` and message set `S env p t`, in
    the pseudocode's priority order (`propose`, `vote`, `timeoutNull`,
    `nullAdvance`, `mnotarAdvance`, `noprogressNull`, `idle`).

    The timeout guard reads "`T = 2Δ`" (line 13) retriably, as
    `s.entry + 2 * Δ ≤ t` — the timer has *reached* `2Δ`: with literal
    equality, a slot busy with a higher-priority block would starve the
    timeout forever. The classical `choose` in the vote branches makes the
    function noncomputable; the model is for reasoning, not execution. -/
noncomputable def decide (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    (t : Time) (s : PState Tx) : Action Tx :=
  if env.lead s.view = p ∧ s.proposed = false then
    Action.propose (env.proposal p t s.view)
  else if hvp : (∃ b, ValidProposal (S env p t) f env.lead s.view b) ∧
      s.notarised = none ∧ s.nullified = false then
    Action.vote hvp.1.choose
  else if s.entry + 2 * Δ ≤ t ∧ s.nullified = false ∧
      s.notarised = none then
    Action.timeoutNull
  else if HasNullif (S env p t) f s.view then
    Action.nullAdvance
  else if hmn : ∃ b, MBlock.bview b = s.view ∧
      HasMNotar (S env p t) f b then
    Action.mnotarAdvance
      (if s.notarised = none ∧ s.nullified = false then some hmn.choose
       else none)
  else if s.nullified = false ∧ ∃ b, s.notarised = some b ∧
      ∃ W : Finset (Processor n), 2 * f + 1 ≤ W.card ∧ ∀ q ∈ W,
        (q, MMsg.nullify s.view) ∈ S env p t ∨
        ∃ b', MBlock.bview b' = s.view ∧ b' ≠ b ∧
          (q, MMsg.vote b') ∈ S env p t then
    Action.noprogressNull
  else Action.idle

/-- The state update of an action at slot `t` (Algorithm 1's assignments).
    View advances (lines 17, 21) reset everything and set `entry := t + 1`:
    the new view is entered at the start of slot `t + 1`. -/
def apply (t : Time) : Action Tx → PState Tx → PState Tx
  | .propose _, s => { s with proposed := true }
  | .vote b, s => { s with notarised := some b }
  | .timeoutNull, s => { s with nullified := true }
  | .nullAdvance, s => ⟨s.view + 1, t + 1, false, false, none⟩
  | .mnotarAdvance _, s => ⟨s.view + 1, t + 1, false, false, none⟩
  | .noprogressNull, s => { s with nullified := true }
  | .idle, s => s

/-- The messages an action disseminates; the `View` argument is the
    *current* view, the payload of nullifies. -/
def emits : Action Tx → View → List (MMsg Tx)
  | .propose b, _ => [MMsg.block b]
  | .vote b, _ => [MMsg.vote b]
  | .timeoutNull, v => [MMsg.nullify v]
  | .nullAdvance, _ => []
  | .mnotarAdvance (some b), _ => [MMsg.vote b]
  | .mnotarAdvance none, _ => []
  | .noprogressNull, v => [MMsg.nullify v]
  | .idle, _ => []

/-- The state trajectory of processor `p`: `traj f Δ env p t` is `p`'s
    state at the *start* of slot `t`; slot `t` applies the decided action
    to it. -/
noncomputable def traj (f Δ : Nat) (env : Env n Tx) (p : Processor n) :
    Time → PState Tx
  | 0 => PState.init
  | t + 1 =>
      apply t (decide f Δ env p t (traj f Δ env p t)) (traj f Δ env p t)

@[simp] theorem traj_zero (f Δ : Nat) (env : Env n Tx) (p : Processor n) :
    traj f Δ env p 0 = PState.init := rfl

theorem traj_succ (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    (t : Time) :
    traj f Δ env p (t + 1) =
      apply t (decide f Δ env p t (traj f Δ env p t))
        (traj f Δ env p t) := rfl

/-- The messages `p` disseminates during slot `t`. -/
noncomputable def emitsAt (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    (t : Time) : List (MMsg Tx) :=
  emits (decide f Δ env p t (traj f Δ env p t)) (traj f Δ env p t).view

theorem emitsAt_def (f Δ : Nat) (env : Env n Tx) (p : Processor n)
    (t : Time) :
    emitsAt f Δ env p t =
      emits (decide f Δ env p t (traj f Δ env p t))
        (traj f Δ env p t).view := rfl

/-- The model's instantiation of the abstract `StateView` interface of
    `Minimmit.Protocol`. -/
noncomputable def toStateView (f Δ : Nat) (env : Env n Tx) :
    StateView n (MBlock Tx) (MMsg Tx) Tx where
  bview := MBlock.bview
  voteMsg := MMsg.vote
  curView p t := (traj f Δ env p t).view
  notarised p t := (traj f Δ env p t).notarised
  votesAt p t b := MMsg.vote b ∈ emitsAt f Δ env p t
  nullifyMsg := MMsg.nullify
  nullsAt p t v := MMsg.nullify v ∈ emitsAt f Δ env p t
  seenAt p t q m := (q, m) ∈ S env p t
  parentLink b' b := ∃ v tr, b = MBlock.node v tr b'
  lead := env.lead
  blockMsg := MMsg.block
  receivedTx := env.txArrive
  txIn tr b := match b with | .gen => False | .node _ trs _ => tr ∈ trs
  inLog p t tr := ∃ b, HasLNotar (S env p t) f b ∧ tr ∈ trStarM b
  finalisesAt p t b := HasLNotar (S env p t) f b

/-- The model's instantiation of the abstract `Execution` transcript:
    correct processors sign exactly what their state machine emits;
    Byzantine signing is oracle data. -/
noncomputable def toExecution (f Δ : Nat) (env : Env n Tx) :
    Execution n (MMsg Tx) where
  Correct p := p ∉ env.byz
  Signed p m :=
    if p ∈ env.byz then env.byzSigned p m
    else ∃ t, m ∈ emitsAt f Δ env p t
  SeenByCorrect p m := ∃ q t, q ∉ env.byz ∧ (p, m) ∈ S env q t

end Minimmit.Model
