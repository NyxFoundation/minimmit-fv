# Minimmit — paper statements and proofs (reference)

> **Source.** B. K. Chou, A. Lewis-Pye, P. O'Grady — *Minimmit: Fast Finality
> with Even Faster Blocks.* Accepted to Financial Cryptography 2026 (FC'26).
> arXiv:2508.10862 (v7, 2026-01-27). Plain-language overview:
> <https://dankradfeist.de/tempo/2025/12/31/minimmit-simple-fast-consensus.html>.
>
> Local PDF: `2508.10862.pdf` (not committed — see README).
> SHA-256 `9d5c52d38726ff8b6a2ce0c73a60797f992c676e5b8cf69d67beef13733f7e7f`.
> Text extracted with **PyMuPDF 1.27.1** (MuPDF 1.27.1).
>
> This file lists every numbered statement in the paper, with each proof as it
> appears in §5. Minimmit numbers its results as `<section>.<index>` and states
> **all** of them — including the headline safety and liveness results — as
> **Lemmas**: there are **10 Lemmas (5.1–5.10)** and **no numbered Definitions,
> Theorems, Propositions, or Corollaries**. The model, data structures, and the
> Consistency / Liveness / optimistic-responsiveness definitions are given as
> unnumbered prose in §2 and §4 and are summarised in the Notation glossary below.
>
> Algorithm 1 (the §4 pseudocode), the figures/tables of §4, and the prose of
> §1–§4 and §6–§7 are intentionally omitted — they are protocol description and
> commentary rather than statements to formalize. (Algorithm 1 is interleaved by
> the PDF layout between Lemma 5.2's statement and its proof; it has been removed
> from that segment.)
>
> PDF-extraction caveat — the text is preserved verbatim, with known artifacts
> inherited from the PDF: mathematical italic identifiers render as their Unicode
> math-italic codepoints (e.g. `𝑏`, `𝑝𝑖`, `𝑣`) and a following space is
> sometimes swallowed (`𝑏receives`); footnotes and running headers interleaved by
> pagination have been stripped, but footnote bodies inside a proof region are
> kept verbatim. The `(line N)` references point at the raw PyMuPDF line numbering.

## Notation

A glossary of the recurring symbols and structures defined in §2 and §4.

| Symbol | Meaning |
|---|---|
| `Π = {p_1,…,p_n}` | The `n` processors. |
| `n`, `f` | Processor count and Byzantine bound; Minimmit assumes **`n ≥ 5f+1`** (80% honest), enabling 2-round finality. |
| `f_a ≤ f` | The *actual* (unknown) number of Byzantine processors in an execution. |
| `Δ` | Known message-delay bound after GST: a message sent at `t` arrives by `max{GST, t} + Δ`. |
| `δ ≤ Δ` | The *actual* (unknown) least upper bound on message delay after GST. |
| `GST` | Global Stabilisation Time — unknown to the protocol; chosen by the adversary. |
| `v ∈ N≥1` | View number; processors proceed through views sequentially. |
| `lead(v)` | Leader of view `v`, `lead(v) := p_{j+1}` where `j = v mod n`. |
| `b = (v, Tr, h)` | A block: view `v`, transactions `Tr`, parent-hash `h`; signed by `lead(v)`. |
| `b_gen`, `⊥` | Genesis block (with M/L-notarisations by default); `⊥` the default "no block" value. |
| `H(·)` | Collision-resistant hash used for the parent link `h`. |
| `(vote, b)` | A processor's signed vote for block `b`. |
| `(nullify, v)` | A processor's signed nullify message for view `v`. |
| **M-notarisation** | A set of **`2f+1`** votes for a block (≈40% under `n=5f+1`); lets a processor advance to the next view. |
| **L-notarisation** | A set of **`n−f`** votes for a block (≈80%); suffices for **finalisation**. An L-notarisation implies an M-notarisation. |
| **Nullification** | A set of **`2f+1`** `nullify(v)` messages for view `v`; lets a processor advance past `v`. |
| `(X1)` | Key invariant: if `b` (view `v`) gets an L-notarisation, no `b'≠b` (view `v`) gets `2f+1` votes (an M-notarisation). |
| `(X2)` | Key invariant: if `b` (view `v`) gets an L-notarisation, view `v` does not receive a nullification. |
| `notarised`, `nullified`, `proposed` | Per-processor local state in Algorithm 1. |
| `T` | Per-processor view timer; a processor sends `nullify(v)` if `T = 2Δ` without progress. |
| `S` | A processor's local set of received messages (votes, notarisations, nullifications, blocks). |
| `ProposeChild`, `SelectParent` | §4 procedures: build a child block / pick the parent to extend. |
| Consistency | Safety: no two inconsistent blocks both receive L-notarisations (correct processors agree on the finalised sequence). |
| Liveness | Every transaction received by a correct processor is eventually finalised by all correct processors. |
| Optimistically responsive | Latency is `O(f_a·Δ + δ)` for transactions first received after GST (`O(δ)` when leaders act correctly). |

The paper's analysis (§5) is split into Consistency (§5.1, Lem 5.1–5.4),
Liveness (§5.2, Lem 5.5–5.7), and Optimistic responsiveness (§5.3, Lem 5.8–5.10).

## Lemmas

## Consistency (safety) — §5.1

### Lemma 5.1 — One vote per view

**Statement.** (line 476)

```
Lemma 5.1 (One vote per view). Correct processors vote for at most one block in each view, i.e., if
𝑝𝑖is correct then, for each 𝑣∈N≥1, there exists at most one 𝑏with 𝑏.view = 𝑣such that 𝑝𝑖sends a
message (vote,𝑏).
```

**Proof.** (line 479)

```
Proof. Recall that ⊥is a default value, different than any block. Each correct processor’s local
value notarised is initially set to ⊥, and is also set to ⊥upon entering any view (lines 17 and 21).
A correct processor 𝑝𝑖will only vote for a block if notarised = ⊥(lines 10 and 20). The claim of
the lemma holds because, upon voting for any block 𝑏, 𝑝𝑖either sets notarised := 𝑏(line 11) and
then does not redefine this value until entering the next view, or else immediately enters the next
view (lines 20 and 21).
```

### Lemma 5.2 — (X1) is satisfied — L-notarisation excludes a conflicting M-notarisation

**Statement.** (line 486)

```
Lemma 5.2 ((X1) is satisfied). If 𝑏receives an L-notarisation, then no block 𝑏′ ≠𝑏with 𝑏′.view =
𝑏.view receives an M-notarisation.
```

**Proof.** (line 556)

```
Proof. Given Lemma 5.1, this now follows as in Section 3. Towards a contradiction, suppose
that 𝑏receives an L-notarisation and that 𝑏′ ≠𝑏with 𝑏′.view = 𝑏.view receives an M-notarisation.
Let 𝑃be the set of processors that contribute to the L-notarisation for 𝑏, and let 𝑃′ be the set of
processors that vote for 𝑏′. Then |𝑃∩𝑃′| ≥(𝑛−𝑓) + (2𝑓+ 1) −𝑛= 𝑓+ 1. So, 𝑃∩𝑃′ contains a
correct processor, which contradicts Lemma 5.1.
```

### Lemma 5.3 — (X2) is satisfied — L-notarised view receives no nullification

**Statement.** (line 562)

```
Lemma 5.3 ((X2) is satisfied). If 𝑏receives an L-notarisation and 𝑣= 𝑏.view, then view 𝑣does not
receive a nullification.
```

**Proof.** (line 564)

```
Proof. Towards a contradiction, suppose 𝑏receives an L-notarisation, 𝑣= 𝑏.view, and view 𝑣
receives a nullification. Let 𝑃be the correct processors that vote for 𝑏, let 𝑃′ = Π \ 𝑃, and note
that |𝑃′| ≤2𝑓. Since view 𝑣receives a nullification, it follows that some processor in 𝑃must send
a nullify(𝑣) message. So, let 𝑡be the first timeslot at which some processor 𝑝𝑖∈𝑃sends such a
message. Since 𝑝𝑖cannot send a nullify(𝑣) message upon timeout (lines 13-14), 𝑝𝑖must send the

nullify(𝑣) message at 𝑡because the conditions of lines 24-27 hold for 𝑝𝑖at 𝑡, i.e., 𝑝𝑖must have
received ≥2𝑓+ 1 messages, each signed by a different processor, and each of the form:
(i) (nullify, 𝑣), or;
(ii) (vote,𝑏′) for some 𝑏′ ≠𝑏with 𝑏′.view = 𝑣.
By Lemma 5.1, no processor in 𝑃sends a message of form (ii). By our choice of 𝑡, no processor in 𝑃
sends a message of form (i) prior to 𝑡. Combined with the fact that |𝑃′| ≤2𝑓, this gives the required
contradiction.
```

### Lemma 5.4 — Consistency

**Statement.** (line 580)

```
Lemma 5.4 (Consistency). The protocol satisfies Consistency.
```

**Proof.** (line 581)

```
Proof. Towards a contradiction, suppose that two inconsistent blocks, 𝑏and 𝑏′ say, both receive
L-notarisations. Without loss of generality suppose 𝑏.view ≤𝑏′.view. Set 𝑏1 := 𝑏and 𝑣1 := 𝑏1.view.
Then there is a least 𝑣2 ≥𝑣1 such that some block 𝑏2 satisfies:
(1) 𝑏2.view = 𝑣2;
(2) 𝑏1 is not an ancestor of 𝑏2, and;
(3) 𝑏2 receives an M-notarisation.
From Lemma 5.2, it follows that 𝑣2 > 𝑣1. According to clause (ii) from the definition of when S
contains a valid proposal for view 𝑣2, correct processors will not vote for 𝑏2 in line 11 until they
receive an M-notarisation for its parent, 𝑏0 say. Correct processors will not vote for 𝑏2 in line 20
until 𝑏2 has already received an M-notarisation, meaning that at least 𝑓+ 1 correct processors
must first vote for 𝑏2 via line 11, and 𝑏0 must receive an M-notarisation. By our choice of 𝑣2, it
follows that 𝑏0.view < 𝑣1. This gives a contradiction, because, by clause (iii) from the definition of
a valid proposal for view 𝑣2, correct processors would not vote for 𝑏2 in line 11 without receiving
a nullification for view 𝑣1. By Lemma 5.3, such a nullification cannot exist. So, block 𝑏2 cannot
receive an M-notarisation (and no correct processor votes for 𝑏2 via either line 11 or 20).
```

## Liveness — §5.2

### Lemma 5.5 — Progression through views

**Statement.** (line 599)

```
Lemma 5.5 (Progression through views). Every correct processor enters every view 𝑣∈N≥1.
```

**Proof.** (line 600)

```
Proof. Towards a contradiction, suppose that some correct processor 𝑝𝑖enters view 𝑣, but never
enters view 𝑣+ 1. Note that correct processors only leave any view 𝑣′ upon receiving either a
nullification for the view, or else an M-notarisation for some view 𝑣′ block. Since correct processors
forward new nullifications and notarisations upon receiving them (lines 2 and 3), the fact that 𝑝𝑖
enters view 𝑣but does not leave it means that:
• All correct processors enter view 𝑣;
• No correct processor leaves view 𝑣.
Each correct processor eventually receives, from at least 𝑛−𝑓processors, either a vote for
some view 𝑣block, or a nullify(𝑣) message. If any correct processor receives an M-notarisation
for a view 𝑣block, then we reach an immediate contradiction. So, suppose otherwise. If 𝑝𝑗is a
correct processor that votes for a view 𝑣block 𝑏, it follows that 𝑝𝑗receives messages from at least
(𝑛−𝑓) −(2𝑓) = 𝑛−3𝑓≥2𝑓+ 1 processors, each of which is either:
(i) A nullify(𝑣) message, or;
(ii) A vote for a view 𝑣block different than 𝑏.
So, the conditions of lines 24-27 are eventually satisfied, meaning that 𝑝𝑗sends a nullify(𝑣) message
(line 28). Any correct processor that does not vote for a view 𝑣block also sends a nullify(𝑣)
message, so all correct processors send nullify(𝑣) messages. All correct processors therefore receive
a nullification for view 𝑣and leave the view (line 17), giving the required contradiction.
```

### Lemma 5.6 — Correct leaders finalise blocks

**Statement.** (line 622)

```
Lemma 5.6 (Correct leaders finalise blocks). If 𝑝𝑖= lead(𝑣) is correct, and if the first correct
processor to enter view 𝑣does so after GST, then 𝑝𝑖disseminates a block and that block receives an
L-notarisation.
```

**Proof.** (line 625)

```
Proof. Suppose 𝑝𝑖= lead(𝑣) is correct and that the first correct processor 𝑝𝑗to enter view 𝑣
does so at timeslot 𝑡≥GST. If 𝑣> 1, processor 𝑝𝑗enters view 𝑣upon receiving either a nullification
for view 𝑣−1, or else an M-notarisation for some view 𝑣−1 block. Since 𝑝𝑗forwards on all new
notarisations and nullifications that it receives (lines 2 and 3), it follows that all correct processors
enter view 𝑣by 𝑡+ Δ (note that this also holds if 𝑣= 1). Processor 𝑝𝑖therefore disseminates a
new block 𝑏by 𝑡+ Δ, which is received by all processors by 𝑡+ 2Δ. Let 𝑏′ be the parent of 𝑏and
suppose 𝑏′.view = 𝑣′. Then 𝑝𝑖receives an M-notarisation for 𝑏′ by 𝑡+ Δ. Since 𝑝𝑖forwards on all
new notarisations that it receives (line 3), all correct processors receive an M-notarisation for 𝑏′
by 𝑡+ 2Δ. Since 𝑝𝑖has entered view 𝑣, it must also have received nullifications for all views in
the open interval (𝑣′, 𝑣) by 𝑡+ Δ, and all correct processors receive these by 𝑡+ 2Δ. All correct
processors therefore vote for 𝑏(by either line 11 or 20)13 before any correct processor sends a
nullify(𝑣) message. The block 𝑏therefore receives an L-notarisation, as claimed.
```

### Lemma 5.7 — Liveness

**Statement.** (line 638)

```
Lemma 5.7 (Liveness). The protocol satisfies Liveness.
```

**Proof.** (line 639)

```
Proof. Suppose correct 𝑝𝑖receives the transaction tr. Let 𝑣be a view with lead(𝑣) = 𝑝𝑖and such
that the first correct processor to enter view 𝑣does so after GST. By Lemma 5.6, 𝑝𝑖will send a block
𝑏to all processors, and 𝑏will receive an L-notarisation. From the definition of the ProposeChild
procedure, it follows that tr will be included in 𝑏′.Tr for some ancestor 𝑏′ of 𝑏, and all correct
processors will add tr to their log upon receiving all ancestors of𝑏(see the final paragraph of Section
2). Correct processors only vote for blocks whose parent has already received an M-notarisation.
All ancestors of 𝑏′ of 𝑏must therefore receive M-notarisations, meaning that at least 𝑓+ 1 correct
processors disseminate each such 𝑏′, and correct processors receive all ancestors of 𝑏.
```

## Optimistic responsiveness — §5.3

### Lemma 5.8 — Correct leader ⇒ finalise a view-v block by t+O(δ)

**Statement.** (line 658)

```
Lemma 5.8. Suppose lead(𝑣) is correct and that the first correct processor to enter view 𝑣does so at
𝑡≥GST. Then all correct processors leave view 𝑣and finalise a view 𝑣block by 𝑡+ 𝑂(𝛿).
```

**Proof.** (line 660)

```
Proof. Proving the claim of the lemma just involves reviewing the proof of Lemma 5.6 and
observing that the leader’s block will actually be finalised by all correct processors within time
𝑂(𝛿) of any correct processor entering the view.
As before, suppose first 𝑝𝑖= lead(𝑣) is correct and that the first correct processor to enter
view 𝑣does so at timeslot 𝑡≥GST. Since correct processors forward on all new notarisations
13The point of line 20 is to ensure this part of the proof goes through. As noted in Section 3, without it, there is the possibility
that correct processors move to the next view upon seeing an M-notarisation, before they are able to vote via line 11, thereby
failing to guarantee an L-notarisation.
14Since the notion of leaders is protocol specific, we prefer to use the more general definition as stated, but the stronger
result also follows directly from the proofs given in this section.

and nullifications that they receive, it follows that all correct processors enter view 𝑣by 𝑡+ 𝛿.
Processor 𝑝𝑖therefore disseminates a new block 𝑏by 𝑡+ 𝛿, which is received by all processors by
𝑡+ 2𝛿. Let 𝑏′ be the parent of 𝑏and suppose 𝑏′.view = 𝑣′. Then, from the definition of the function
SelectParent, it follows that 𝑝𝑖receives an M-notarisation for 𝑏′ by 𝑡+ 𝛿. Since 𝑝𝑖forwards on all
new notarisations that it receives (line 3), all correct processors receive an M-notarisation for 𝑏′ by
𝑡+ 2𝛿. Since 𝑝𝑖has entered view 𝑣, it must also have received nullifications for all views in the open
interval (𝑣′, 𝑣) by 𝑡+ 𝛿, and all correct processors receive these by 𝑡+ 2𝛿. All correct processors
therefore vote for 𝑏(by either line 11 or 20) by 𝑡+ 2𝛿, and before any correct processor sends a
nullify(𝑣) message. All correct processors therefore receive 𝑏together with an L-notarisation (and
an M-notarisation) for 𝑏by 𝑡+ 3𝛿, and also leave view 𝑣by this time. This establishes the claim of
the lemma.
```

### Lemma 5.9 — All correct processors leave view v by t+O(Δ)

**Statement.** (line 685)

```
Lemma 5.9. Suppose the first correct processor to enter view 𝑣does so at 𝑡≥GST. Then, whether or
not lead(𝑣) is correct, all correct processors leave view 𝑣by 𝑡+ 𝑂(Δ).
```

**Proof.** (line 687)

```
Proof. Suppose the first correct processor to enter view 𝑣does so at 𝑡≥GST. Towards a
contradiction, suppose some correct processor does not leave view 𝑣by 𝑡+ 2Δ + 3𝛿. As before, it
follows that all correct processors enter view 𝑣by 𝑡+𝛿. By timeslot 𝑡+𝛿+2Δ, all correct processors
have either voted for some view 𝑣block, or else sent a nullify(𝑣) message. If any correct processor
receives an M-notarisation for a view 𝑣block by 𝑡+ 2Δ + 2𝛿, then it forwards it on to all processors.
This means all correct processors leave the view by 𝑡+ 2Δ + 3𝛿, giving an immediate contradiction.
So, suppose otherwise. If 𝑝𝑗is a correct processor that votes for a view 𝑣block 𝑏, it follows that, by
𝑡+ 2Δ + 2𝛿, 𝑝𝑗receives messages from at least (𝑛−𝑓) −(2𝑓) = 𝑛−3𝑓≥2𝑓+ 1 processors, each of
which is either:
(i) A nullify(𝑣) message, or;
(ii) A vote for a view 𝑣block different than 𝑏.
So, the conditions of lines 24-27 are satisfied at this time, meaning that 𝑝𝑗sends a nullify(𝑣) message
(line 28). Any correct processor that does not vote for a view 𝑣block also sends a nullify(𝑣) message
by this time. So, all correct processors receive a nullification for view 𝑣by 𝑡+ 2Δ + 3𝛿, giving the
required contradiction.
```

### Lemma 5.10 — Minimmit is optimistically responsive

**Statement.** (line 703)

```
Lemma 5.10. Minimmit is optimistically responsive.
```

**Proof.** (line 704)

```
Proof. Suppose tr is first received by a correct processor at 𝑡≥GST. Since we assume correct
processors send new transactions to all other processors upon first receiving them, tr is received by
all correct processors by 𝑡+ 𝛿. Let 𝑣0 be the greatest view that any correct processor is in at 𝑡+ 𝛿,
and let 𝑣1 be the least view > 𝑣0 such that lead(𝑣) is correct. From Lemmas 5.8 and 5.9, it follows
that all correct processors enter view 𝑣1 by time 𝑡+ 𝑂(𝑓𝑎Δ + 𝛿), and that all correct processors
also finalise a view 𝑣1 block, 𝑏say, by 𝑡+ 𝑂(𝑓𝑎Δ + 𝛿). According to the definition of the procedure
ProposeChild(𝑏, 𝑣), tr will be included in an ancestor of 𝑏. Since all ancestors of 𝑏′ of 𝑏must receive
M-notarisations prior to lead(𝑣) proposing 𝑏, at least 𝑓+ 1 correct processors send each such 𝑏′
to all processors, and correct processors receive all ancestors of 𝑏by 𝑡+ 𝑂(𝑓𝑎Δ + 𝛿). All correct
processors therefore finalise tr by time 𝑡+ 𝑂(𝑓𝑎Δ + 𝛿).
```
