import Mathlib.Data.List.Basic
import Minimmit.Consistency.Lemma5_4

set_option autoImplicit false

namespace Minimmit

variable {Block Message Tx : Type}

/-!
# Log-level Consistency (§2)

Lifts the block-level `lemma_5_4` to the paper's §2 statement: correct logs
are pairwise consistent — for any correct `p`, `q` and timeslots `t`, `t'`,
one of `log_p(t)`, `log_q(t')` is a prefix of the other (`consistency_logs`).

The sequence structure enters through an abstract `LogView` (as `StateView`
abstracts Algorithm 1): `b.Tr*` is a *function* of the block, which is
precisely what `collision_resistant` (`Minimmit.Axioms`) makes realizable —
under `StateView.ParentFunctional` each block's ancestor chain is unique
(`anc_comparable`), so the concatenated-payload map is well defined. The
derivation below then needs only the `trStar_parent` concatenation equation
and the §2 shape of correct logs.
-/

/-- **Sequence-valued logs and payloads** (§2), as an abstract interface. A
    concrete operational model (issue #21) can construct one without changing
    any theorem statement. -/
structure LogView (n : Nat) (Block Tx : Type) where
  /-- `b.Tr`: the block's transaction payload, as a sequence. -/
  payload : Block → List Tx
  /-- `b.Tr*` (§2): the concatenation of the payloads along `b`'s ancestor
      chain, genesis first. Total on the opaque `Block` space; on valid
      states the chain — hence this value — is unique by
      `collision_resistant`. -/
  trStar : Block → List Tx
  /-- `log_p(t)`: processor `p`'s log at timeslot `t` (§2). Refines the
      membership predicate `StateView.inLog` with the sequence order. -/
  log : Processor n → Time → List Tx

/-- **Log discipline** (§2 finalisation, sequence form) for correct
    processors, as abstract hypotheses (provable in any concrete operational
    model):

    * `trStar_parent` — the defining recurrence of `b.Tr*`: a block's
      concatenated-ancestor payload extends its parent's by its own payload;
    * `log_shape` — the observable footprint of the §2 finalisation rule: a
      correct log is initially empty and is set to extend `b.Tr*` exactly
      upon finalising `b` while holding an L-notarisation for `b` (and all
      its ancestors), whose `n − f` valid signatures make `b` L-notarised at
      the transcript level (`seen_signed`); so at every timeslot the log
      equals `b.Tr*` for some L-notarised `b`, or is still empty. -/
structure LogDiscipline {n : Nat} (sv : StateView n Block Message Tx) (lv : LogView n Block Tx)
    (e : Execution n Message) (f : Nat) : Prop where
  trStar_parent : ∀ (b' b : Block), sv.parentLink b' b →
    lv.trStar b = lv.trStar b' ++ lv.payload b
  log_shape : ∀ (p : Processor n) (t : Time), e.Correct p →
    lv.log p t = [] ∨ ∃ b, sv.LNotarised e f b ∧ lv.log p t = lv.trStar b

namespace LogDiscipline

/-- `Tr*` is monotone along ancestry: an ancestor's `Tr*` is a prefix of the
    descendant's (`trStar_parent`, folded along the chain). -/
theorem trStar_prefix_of_anc {n f : Nat} {sv : StateView n Block Message Tx} {lv : LogView n Block Tx}
    {e : Execution n Message} (hld : LogDiscipline sv lv e f)
    {b' b : Block} (h : sv.Anc b' b) : lv.trStar b' <+: lv.trStar b := by
  have h' : Relation.ReflTransGen sv.parentLink b' b := h
  clear h
  induction h' with
  | refl => exact List.prefix_refl _
  | tail hstep hlink ih =>
    rw [hld.trStar_parent _ _ hlink]
    exact ih.trans (List.prefix_append _ _)

end LogDiscipline

/-- **Consistency, log level (§2).** "If `p_i` and `p_j` are correct then,
    for any timeslots `t` and `t'`, `log_i(t)` and `log_j(t')` are
    consistent": one is a prefix of the other. By `log_shape` each log is
    `b.Tr*` for an L-notarised `b` (or empty); `lemma_5_4` makes the two
    blocks `Anc`-comparable, and `Tr*`-monotonicity along the chain turns
    ancestry into the prefix order. -/
theorem consistency_logs {n f : Nat} (sv : StateView n Block Message Tx) (e : Execution n Message)
    (lv : LogView n Block Tx)
    (hd : sv.VoteDiscipline e) (hrd : sv.ReceiptDiscipline e)
    (hnd : sv.NullifyDiscipline e f) (hpd : sv.ProposalDiscipline e f)
    (hnf : 5 * f + 1 ≤ n) (hfb : e.FaultBound f)
    (hld : LogDiscipline sv lv e f)
    {p q : Processor n} (hp : e.Correct p) (hq : e.Correct q)
    (t t' : Time) :
    lv.log p t <+: lv.log q t' ∨ lv.log q t' <+: lv.log p t := by
  rcases hld.log_shape p t hp with hp0 | ⟨b, hLb, hpb⟩
  · rw [hp0]
    exact Or.inl List.nil_prefix
  rcases hld.log_shape q t' hq with hq0 | ⟨b', hLb', hqb⟩
  · rw [hq0]
    exact Or.inr List.nil_prefix
  rw [hpb, hqb]
  rcases lemma_5_4 sv e hd hrd hnd hpd hnf hfb hLb hLb' with hanc | hanc
  · exact Or.inl (hld.trStar_prefix_of_anc hanc)
  · exact Or.inr (hld.trStar_prefix_of_anc hanc)

end Minimmit
