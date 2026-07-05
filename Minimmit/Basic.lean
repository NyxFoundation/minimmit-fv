import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace Minimmit

/-- A processor; there are `n` of them, of which at most `f` are Byzantine,
    under the fault bound `5*f + 1 ≤ n`. -/
abbrev Processor (n : Nat) := Fin n

/-- Views are numbered `1, 2, …` in the paper (`v ∈ ℕ≥1`), with `0` reserved
    for the genesis block. Using `Nat` uniformly loses nothing: every statement
    quantifying over views holds for `0` as well. -/
abbrev View := Nat

/-- Discrete timeslots (Barrier 4: time as `ℕ`). -/
abbrev Time := Nat

/-- Abstract block space. The concrete `(v, Tr, h)` structure with genesis
    `b_gen` is abstracted; the view `b.view` of a block is exposed by the
    protocol interface (`StateView.bview`). -/
opaque Block : Type

/-- Abstract message space (propose / vote / nullify / notarisation forwards). -/
opaque Message : Type

/-- M-notarisation quorum threshold: `2f+1` view-`v` votes advance a processor
    to view `v+1`. Parameterized by `f` only — the analysis never assumes
    `n = 5f+1`, it threads `5*f + 1 ≤ n` as a hypothesis where needed. -/
def mQuorum (f : Nat) : Nat := 2 * f + 1

/-- L-notarisation quorum threshold: `n − f` view-`v` votes finalise a block. -/
def lQuorum (n f : Nat) : Nat := n - f

/-- Nullification quorum threshold: `2f+1` `(nullify, v)` messages nullify
    view `v`. -/
def nullQuorum (f : Nat) : Nat := 2 * f + 1

/-- An execution transcript, with the signature-level predicates the lemmas
    range over. All fields are abstract (an abstract interface). -/
structure Execution (n : Nat) where
  /-- The processor is correct (not Byzantine). -/
  Correct       : Processor n → Prop
  /-- The processor actually signed (sent) the message. -/
  Signed        : Processor n → Message → Prop
  /-- A valid `⟨m⟩_p` appears in some correct processor's message set `S`.
      Existentially aggregated over correct observers, mirroring the "received
      by a correct processor" usage of the quorum-counting lemmas. -/
  SeenByCorrect : Processor n → Message → Prop

/-- The fault bound "at most `f` processors are Byzantine": there is a set
    `byz` of at most `f` processors outside of which every processor is
    correct. Threaded as a hypothesis (never `n = 5f + 1`; the quorum
    arguments only ever use `5*f + 1 ≤ n` alongside this bound). -/
def Execution.FaultBound {n : Nat} (e : Execution n) (f : Nat) : Prop :=
  ∃ byz : Finset (Processor n), byz.card ≤ f ∧ ∀ p, p ∉ byz → e.Correct p

/-- Marks executions actually produced by Algorithm 1. Opaque (no constructor),
    so adversarial structures like `⟨fun _ => True, fun _ _ => False, fun _ _ => True⟩`
    cannot be shown valid — this is what keeps the axiom in `Minimmit.Axioms`
    from proving `False`. A concrete operational model can later *define* it. -/
opaque ValidExecution {n : Nat} (e : Execution n) : Prop

/-- Idealized signature unforgeability as a *predicate* on an execution:
    a valid signature by a correct processor seen in correct view was actually
    produced by that processor. Exposed as a `def` so theorems thread it as a
    hypothesis (Barrier 1); declared to hold on valid executions in
    `Minimmit.Axioms`. -/
def SignatureUnforgeable {n : Nat} (e : Execution n) : Prop :=
  ∀ (p : Processor n) (m : Message), e.Correct p → e.SeenByCorrect p m → e.Signed p m

end Minimmit
