import Minimmit.Protocol
import Minimmit.Axioms

set_option autoImplicit false

namespace Minimmit

/-- Strict-order core of Lemma 5.1: a correct processor cannot execute vote
    transitions at `t < t'` for two blocks of the same view. Mirrors the paper's
    argument: by `vote_view` both votes are cast in the block's view, so `p` is
    in the same view at `t` and `t'`; `vote_sets` then pins `notarised = some b`
    at `t'`, contradicting the `notarised = ⊥` guard (`vote_guard`) of the
    second vote. -/
private theorem no_earlier_vote {n : Nat} {sv : StateView n} {e : Execution n}
    (hd : sv.VoteDiscipline e) {p : Processor n} (hp : e.Correct p)
    {t t' : Time} {b b' : Block} (hlt : t < t')
    (hv : sv.bview b = sv.bview b')
    (hb : sv.votesAt p t b) (hb' : sv.votesAt p t' b') : False := by
  have hview : sv.curView p t' = sv.curView p t :=
    calc sv.curView p t' = sv.bview b' := (hd.vote_view p t' b' hp hb').symm
      _ = sv.bview b := hv.symm
      _ = sv.curView p t := hd.vote_view p t b hp hb
  have hset : sv.notarised p t' = some b := hd.vote_sets p t b hp hb t' hlt hview
  have hnone : sv.notarised p t' = none := hd.vote_guard p t' b' hp hb'
  simp [hnone] at hset

/-- **Lemma 5.1 (One vote per view), transition form.** A correct processor
    executes the vote transition for at most one block per view: if `p` is
    correct and votes for `b` at `t` and for `b'` at `t'` with
    `b.view = b'.view`, then `b = b'`. Proved directly from the per-processor
    state-transition hypotheses (`StateView.VoteDiscipline`); no `sorry`, no
    axiom reached. -/
theorem one_vote_per_view {n : Nat} (sv : StateView n) (e : Execution n)
    (hd : sv.VoteDiscipline e) (p : Processor n) (hp : e.Correct p)
    {t t' : Time} {b b' : Block} (hv : sv.bview b = sv.bview b')
    (hb : sv.votesAt p t b) (hb' : sv.votesAt p t' b') : b = b' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact (no_earlier_vote hd hp hlt hv hb hb').elim
  · subst heq
    exact hd.vote_step p t b b' hp hb hb'
  · exact (no_earlier_vote hd hp hgt hv.symm hb' hb).elim

/-- **Lemma 5.1 (One vote per view), paper statement.** "Correct processors
    vote for at most one block in each view, i.e., if `p_i` is correct then,
    for each `v ∈ ℕ≥1`, there exists at most one `b` with `b.view = v` such
    that `p_i` sends a message `(vote, b)`" — stated on the transcript's
    `Signed` predicate ("`p_i` sends `(vote, b)`") and encoding "at most one"
    as: any two such blocks are equal. `signed_vote` reduces sent messages to
    vote transitions, and the transition form applies. -/
theorem lemma_5_1 {n : Nat} (sv : StateView n) (e : Execution n)
    (hd : sv.VoteDiscipline e) (p : Processor n) (hp : e.Correct p)
    {b b' : Block} (hv : sv.bview b = sv.bview b')
    (hb : e.Signed p (sv.voteMsg b)) (hb' : e.Signed p (sv.voteMsg b')) :
    b = b' := by
  obtain ⟨t, hvote⟩ := (hd.signed_vote p b hp).mp hb
  obtain ⟨t', hvote'⟩ := (hd.signed_vote p b' hp).mp hb'
  exact one_vote_per_view sv e hd p hp hv hvote hvote'

/-- **Lemma 5.1 lifted to correct view** — the form the quorum-counting lemmas
    (5.2–5.4) consume: under idealized signature unforgeability
    (`signature_unforgeable`, threaded via `hvalid`), two same-view vote
    messages by a correct processor *seen in correct view* carry the same
    block. This is where `SignatureUnforgeable` equates a signed vote with its
    signer; the only axiom reached is the crypto one in `Minimmit.Axioms`. -/
theorem lemma_5_1_seen {n : Nat} (sv : StateView n) (e : Execution n)
    (hvalid : ValidExecution e) (hd : sv.VoteDiscipline e)
    (p : Processor n) (hp : e.Correct p)
    {b b' : Block} (hv : sv.bview b = sv.bview b')
    (hb : e.SeenByCorrect p (sv.voteMsg b))
    (hb' : e.SeenByCorrect p (sv.voteMsg b')) : b = b' := by
  have huf : SignatureUnforgeable e := signature_unforgeable e hvalid
  exact lemma_5_1 sv e hd p hp hv
    (huf p (sv.voteMsg b) hp hb) (huf p (sv.voteMsg b') hp hb')

end Minimmit
