---
title: Minimmit Lean 4 Formalization Strategy
last_updated: 2026-05-26
tags:
  - lean4
  - formal-verification
  - minimmit
  - consensus
---

# Minimmit Lean 4 Formalization Strategy

This document records *how* the Minimmit consensus protocol (arXiv:2508.10862,
FC'26) is being formalized in Lean 4, the technical barriers we hit, and the
explicit policy decision for each. The 10 numbered statements of the paper
(Lemma 5.1–5.10) are each tracked by a GitHub issue; this file is the
cross-cutting reference those issues link back to.

The statement texts and proofs live in [`notes/paper-statements.md`](../notes/paper-statements.md)
and the per-statement segments in [`notes/_segments/`](../notes/_segments/).

Minimmit is a partially-synchronous BFT SMR protocol under the **`n ≥ 5f+1`**
assumption. Its design splits two quorum thresholds: an **M-notarisation**
(`2f+1` votes) advances a processor to the next view, while an **L-notarisation**
(`n−f` votes) finalises a block. The entire analysis is **deterministic**: the
leader schedule `lead(v) = p_{j+1}, j = v mod n` is a fixed round-robin, so —
unlike Goldfish or Simplex — **liveness needs no probabilistic argument and there
are no `needs-axiom` / Phase-2 statements** (see Barrier 5).

## Proof discipline: `sorry` vs `axiom` vs hypothesis threading

These three are **not** interchangeable. The project uses the latter two and
never the first.

| Mechanism | Meaning | Soundness | Use in this project |
|---|---|---|---|
| `sorry` | Placeholder for an omitted proof; compiles but Lean warns and every downstream proof is tainted. | ✗ Not a proof; technical debt. | **Never.** |
| `axiom` | A proposition *declared* true without proof — a deliberate, explicit assumption. | ✓ Sound relative to the assumption being a genuine idealized fact. | **Only** for idealized cryptography (signature unforgeability, collision resistance). |
| Hypothesis threading | An external/idealized fact is taken as an explicit *premise* of the theorem. | ✓ The theorem is fully proved: "premise ⇒ conclusion". | Default for all of Minimmit's consistency and timing reasoning. |

Because Minimmit has no probabilistic content, every one of the 10 lemmas is
proved with **no `sorry` and no local axiom** — the only project-wide axioms are
the idealized cryptographic primitives in `Minimmit/Axioms.lean`, threaded in as
hypotheses where needed.

## Barriers and decisions

### 1. Idealized cryptography (signatures, hashes)

Votes, blocks, and `nullify` messages are signed; blocks link to their parent by
a collision-resistant hash `H`. The quorum-counting arguments rely on "`k`
messages each signed by a *different* processor" — i.e. on signature
unforgeability to equate distinct signatures with distinct processors.

Game-based cryptographic reductions are out of scope.

**Decision.** Axiomatize idealized interfaces: `SignatureUnforgeable` (a valid
signature on `m` by `p` implies `p` sent `m`) and `CollisionResistant` (equal
hashes ⇒ equal blocks, on the reachable block space). Declare each as an `axiom`
with a source comment in `Minimmit/Axioms.lean`; statements thread them in as
hypotheses. These are **permanent** idealized assumptions — there is no Phase-2
follow-up.

### 2. Quorum intersection (the safety core)

The heart of `(X1)`, `(X2)` and Consistency is: under `n ≥ 5f+1`, an
L-notarisation (`n−f` votes) and an M-notarisation / nullify quorum (`2f+1`
messages) intersect in `(n−f) + (2f+1) − n = f+1` processors, hence in at least
one **correct** processor (at most `f` are Byzantine).

**Decision.** Prove it directly over `Finset` cardinalities, **without baking in
`n = 5f+1`**. Parameterize by `n`, `f`, and the hypothesis `5*f + 1 ≤ n`, with
the quorum thresholds as `n - f` (L) and `2*f + 1` (M / nullify). The reusable
lemma is

```lean
-- an L-quorum and an M/nullify-quorum share a correct processor
lemma quorum_intersect_correct
    {n f : ℕ} (hnf : 5 * f + 1 ≤ n)
    (L Q : Finset (Fin n)) (correct : Finset (Fin n))
    (hL : n - f ≤ L.card) (hQ : 2 * f + 1 ≤ Q.card)
    (hc : correctᶜ.card ≤ f) :
    ∃ p ∈ L ∩ Q, p ∈ correct := by ...
```

No axiom; this is the deterministic engine behind Lemmas 5.2, 5.3 and 5.4.

### 3. Protocol mechanics (Algorithm 1, notarisations, nullifications)

The notes omit Algorithm 1, but the statements need: views and the round-robin
`lead(v)`; the per-processor state (`notarised`, `nullified`, `proposed`, timer
`T`, message set `S`); the vote / nullify / timeout rules; the `M-notarisation`
(`2f+1`), `L-notarisation` (`n−f`) and `nullification` (`2f+1`) quorums; and the
`ProposeChild` / `SelectParent` procedures (including the valid-proposal clauses
(i)–(iii) and the (X1)/(X2) invariants).

**Decision (MVP).** Do not implement Algorithm 1 operationally. Provide the
voting/nullify/timer behaviour, notarisation predicates and the two procedures as
an **abstract interface (a structure / typeclass of hypotheses)**, and derive the
lemmas from it. An executable state-machine model can replace the interface later
without changing the statements. Lemma 5.1 (one vote per view) is proved directly
from the state-transition hypotheses of this interface.

### 4. Partial-synchrony timing model

Lemmas 5.5–5.10 are timing arguments over `GST`, the known bound `Δ`, the actual
delay `δ ≤ Δ`, and the actual fault count `f_a ≤ f`, with the delivery rule
"a message sent at `t` arrives by `max{GST, t} + Δ`" and the timeout "`T = 2Δ`".

**Decision.** Model time as `ℕ` timeslots (or `ℝ≥0`) with `GST`, `Δ`, `δ` as
parameters and the delivery / forwarding / timeout rules as abstract hypotheses.
The timing lemmas are then ordinary inequality reasoning, fully proved.

### 5. Deterministic leader rotation ⇒ no probabilistic obligations

Liveness and optimistic responsiveness rely only on `lead(v) = p_{j+1}`
(`j = v mod n`) being a fixed round-robin: among any window of views, at most `f`
consecutive leaders are Byzantine, so a correct leader after GST is reached within
`≤ f + 1` views **deterministically**. The optimistic-responsiveness latency
`O(f_a·Δ + δ)` simply counts the `f_a` faulty leaders before a correct one.

**Decision.** There is **nothing to axiomatize probabilistically** and **no
Phase-2 issue** — a sharp contrast with Goldfish (VRF lottery + Chernoff) and
Simplex (random leader election). Every lemma closes in Phase 1.

## Track structure and dependency graph

Three layers, matching §5. All deterministic given the crypto axioms (Barrier 1).

- **Track A — consistency (safety):** Lemma 5.1–5.4. One-vote-per-view + quorum
  intersection give invariants `(X1)`/`(X2)`, hence Consistency.
- **Track B — liveness:** Lemma 5.5–5.7. View progression + correct-leader
  finalisation give Liveness.
- **Track C — optimistic responsiveness:** Lemma 5.8–5.10. Timing-refined
  versions of the Track-B arguments give latency `O(f_a·Δ + δ)`.

Dependency adjacency list (`X ← {…}` means X's proof depends on …; `[crypto]` are
the idealized-cryptography axioms of Barrier 1):

```
Lem5.1 ← {[crypto: sig-unforgeability]}        (one vote per view; state transitions)
Lem5.2 ← {Lem5.1}                              ((X1); quorum intersection)
Lem5.3 ← {Lem5.1}                              ((X2); quorum intersection)
Lem5.4 ← {Lem5.2, Lem5.3, [crypto: collision-res]}   (Consistency)

Lem5.5 ← {}                                    (Progression through views; timing)
Lem5.6 ← {}                                    (Correct leaders finalise; timing after GST)
Lem5.7 ← {Lem5.5, Lem5.6}                       (Liveness)

Lem5.8 ← {Lem5.6}                              (correct-leader O(δ) finalisation)
Lem5.9 ← {}                                    (leave view by t + O(Δ))
Lem5.10 ← {Lem5.8, Lem5.9}                      (optimistic responsiveness)
```

There is **no cyclic dependency**: the graph is a DAG, so statements can be closed
in topological order.

## Non-issue prerequisites (Lean scaffolding)

The following are **not** tracked by per-statement issues; they are prerequisite
scaffolding assumed by every statement issue. They will be introduced together
(separately from the statement issues) and live at these paths:

| Path | Contents |
|---|---|
| `lakefile.toml`, `lean-toolchain` | Lake build config; pin a Lean toolchain and depend on Mathlib. |
| `Minimmit/Basic.lean` | Core types: `Processor` (`Fin n`), the `n`/`f`/`5*f+1 ≤ n` parameters, `View` (`ℕ≥1`), `Block` `(v, Tr, h)`, genesis `b_gen`, `⊥`, the prefix/ancestor order, M-notarisation (`2f+1`) / L-notarisation (`n−f`) / nullification (`2f+1`) as quorum predicates, and the timing parameters `GST`/`Δ`/`δ`/`f_a`. |
| `Minimmit/Protocol.lean` | Abstract interface: the round-robin `lead(v)`, per-processor state + vote/nullify/timeout transition rules, `ProposeChild`/`SelectParent`, message forwarding/delivery, and the valid-proposal clauses, as a structure / typeclass of hypotheses (Barriers 3–4). |
| `Minimmit/Axioms.lean` | Declared axioms: idealized cryptography only — `SignatureUnforgeable`, `CollisionResistant` (Barrier 1), each with a source comment. No probabilistic axioms. |

Reference pattern for project layout: [`Koukyosyumei/PoL`](https://github.com/Koukyosyumei/PoL)
(Apache-2.0, Lake, `Consensus/` module layout).
