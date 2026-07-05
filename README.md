# minimmit-fv

Formal-verification notes and reference material for the **Minimmit** consensus
protocol.

## Source

B. K. Chou, Andrew Lewis-Pye, P. O'Grady —
*Minimmit: Fast Finality with Even Faster Blocks*

- arXiv: <https://arxiv.org/abs/2508.10862> (v7, 2026-01-27)
- Accepted to Financial Cryptography 2026 (FC'26)
- Plain-language overview (Dankrad Feist, Tempo blog):
  <https://dankradfeist.de/tempo/2025/12/31/minimmit-simple-fast-consensus.html>

Minimmit is a partially-synchronous BFT state-machine-replication protocol that
achieves **2-round finality** under the **`n ≥ 5f+1`** (≈80% honest) assumption,
by letting view progression (`2f+1` votes, an *M-notarisation*) and finalisation
(`n−f` votes, an *L-notarisation*) run on different quorum thresholds.

> The source PDF is **not** committed to this repository. Download it from the
> link above and place it at `2508.10862.pdf` if you want the local copy that the
> notes reference (SHA-256
> `9d5c52d38726ff8b6a2ce0c73a60797f992c676e5b8cf69d67beef13733f7e7f`).

## Contents

- `Minimmit/` — the Lean 4 formalization, **complete for all 10 statements**
  (no `sorry`): `Basic` (core types and the abstract `Execution` transcript),
  `Quorum` (quorum intersection), `Protocol` (the per-processor
  state-transition, network and timing interfaces of Algorithm 1), `Axioms`
  (idealized cryptography only), `Consistency` (Track A: Lemma 5.1–5.4),
  `Liveness` (Track B: Lemma 5.5–5.7), and `Responsiveness` (Track C:
  Lemma 5.8–5.10).
- `notes/paper-statements.md` — every numbered statement from the paper, each
  with its proof as it appears in §5, plus a glossary of recurring notation and
  data structures. Minimmit states **all** of its results — including the
  headline Consistency and Liveness lemmas — as **Lemmas** (5.1–5.10); it has
  **no** numbered Definitions, Theorems, Propositions, or Corollaries.
- `notes/_segments/` — the same statements split into one file per item
  (`lemma_*`, named by the paper's `section.index` label), each containing the
  statement text and its proof with source line references.

Algorithm 1 (the §4 pseudocode), the §4 figures/tables, and the prose of §1–§4
and §6–§7 are intentionally omitted — they are protocol description and
commentary rather than statements to formalize.

## Building

Requires [elan](https://github.com/leanprover/elan); the Lean toolchain is
pinned by `lean-toolchain` (Lean 4.29.1) and Mathlib by `lake-manifest.json`.

```sh
lake exe cache get   # fetch prebuilt Mathlib artifacts
lake build
```

## Goal

Build toward a machine-checked formalization of the Minimmit Consistency
(safety), Liveness, and optimistic-responsiveness results, using these extracted
statements as the specification target. The Lean 4 approach is recorded in
[`docs/formalization-strategy.md`](docs/formalization-strategy.md).
