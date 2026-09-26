---
slug: davis-width-k-descent-difference-coprime-formula
bibkey: davis2017widthk
doi: 10.48550/arXiv.1701.04788
url: https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/DavisWidthDescentDifferenceCoprime.result
---

# Davis's coprime width-descent difference formula

## Problem

Robert Davis, *Width-k Generalizations of Classical Permutation Statistics*,
JIS 20 (2017), gives the following descent-set line, generating function, and
MacMahon identification together at the top of printed page 2. Printed page
1 ends with the preceding descent-count formula:

> where Des σ = {i ∈ [n − 1] | a_i > a_{i+1}}.
> Given any statistic st, one may form the generating function
> F_n^{st}(q) = Σ_{σ∈S_n} q^{st σ}.
> A famous result due to MacMahon [6] states that F_n^{des}(q) =
> F_n^{exc}(q), and that both are equal to the Eulerian polynomial A_n(q).
> The Eulerian polynomials themselves may be defined via the identity
> Σ_{j≥0} (1 + j)^n q^j = A_n(q)/(1 − q)^{n+1}.

Printed page 2 defines width-k descents:

> For each of the following definitions, we assume n ∈ Z_{>0}, k ∈ [n − 1],
> ∅ ≠ K ⊆ [n − 1], and σ = a_1 a_2 ··· a_n ∈ S_n. We define a width-k
> descent of σ to be an index i ∈ [n − k] for which a_i > a_{i+k}. Thus the
> width-1 descents are the usual descents of a permutation. Let
> Des_k(σ) = {i ∈ [n − k] | a_i > a_{i+k}} denote the set of all width-k
> descents of σ, and set des_k(σ) = |Des_k(σ)|.

Printed page 6 introduces the Laurent polynomial and the named conjecture:

> We now show that interesting behavior occurs when considering the function
> G_{n,k}(q) = Σ_{σ∈S_n} q^{des_k(σ)−des_{n−k}(σ)}.
> According to computational data, the following conjecture holds for all
> n ≤ 9 and 1 ≤ k < n for which gcd(k, n) = 1.
>
> Conjecture 9. If gcd(k, n) = 1, then
> G_{n,k}(q) = n q^{1−k} A_{n−1}(q).

The formal theorem makes the surrounding range explicit: for all natural
`n` and `k`, if `1 <= k`, `k < n`, and `Nat.Coprime k n`, then

```text
G(n,k) = n * q^(1-k) * eulerian(n-1).
```

Here `eulerian(m)` is the descent generating function that the paper
identifies with `A_m` by MacMahon's theorem. The paper's separate
infinite-series definition of the Eulerian polynomials is not formalized.
One-based positions are transported to `Fin n`, and signed exponents live in
the Laurent polynomial ring over the integers.

## Motivation

Issue #9085 preregisters Davis's published Conjecture 9, its full
quantifiers, and the bounded literature status before the proof probe. The
question asks for a uniform identity over every coprime pair, rather than a
finite verification or a coefficientwise approximation.

The orchestrator's exact enumeration through `n <= 8` checked all 34 coprime
pairs and found coefficientwise agreement. Representative readings are
`G(3,1) = 3 + 3q` and
`G(5,2) = 5q^{-1} + 55 + 55q + 5q^2`. The non-coprime pair gives
`G(4,2) = 24`; it lies outside the claim.

## Gap

The primary source is arXiv:1701.04788 and labels the identity Conjecture 9.
The two identified citing papers, arXiv:1912.08551 and arXiv:2402.16251, do
not address Conjecture 9. MathDB `/p/335077` records the same statement with
`Solutions 0`. Searches in the pinned Mathlib source found no Eulerian
polynomial API. These are bounded search results, not an exhaustive claim of
worldwide literature coverage or publication priority.

## Route

The proof has two live private escape witnesses.

W1, `cyclic_reindexing_sum`, uses coprimality to reindex positions along the
single cycle induced by multiplication by `k` modulo `n`. The width-`k` and
width-`(n-k)` counts combine into the cyclic descent count minus `k`, and the
permutation equivalence transports the whole Laurent sum.

W2, `cyclic_descent_distribution`, uses the equivalence
`S_n ~= Fin n x S_(n-1)`: rotate each permutation until its maximum is last,
then restrict to the first `n-1` positions. Cyclic descents become ordinary
descents plus one, so their generating function is
`n * q * eulerian(n-1)`. The necessary hypothesis is `2 <= n`; the proposed
`1 <= n` variant is false. The hypotheses `1 <= k < n` imply this corrected
bound before W2 is applied.

Combining W1 and W2 gives
`q^(-k) * (n * q * eulerian(n-1))`, and Laurent monomial multiplication
normalizes the exponent to `1-k`.

## Falsifier

A natural pair `1 <= k < n` with `Nat.Coprime k n` for which the two Laurent
polynomials differ would refute the theorem. A mismatch between the formal
`widthDescents`, `G`, or `eulerian` definitions and the quoted source
definitions would invalidate the source-to-formal resolution claim even if
the Lean theorem remained true. Non-coprime pairs are not counterexamples.

## Evidence

The formal source is
[`DavisWidthDescentDifferenceCoprime.lean`](../D5/S1/Words/DavisWidthDescentDifferenceCoprime.lean).
The public surface consists of the definitions `widthDescents`, `eulerian`,
`G`, and `claim`, followed by the canonical theorem `result`. The two escape
witnesses are private and lie on the theorem's live proof path.

The authoritative module membership is the
[`frozen state`](../Golden/Frozen/state/D5/S1/Words/DavisWidthDescentDifferenceCoprime.lean.json).
The
[`Freeze event`](../Golden/Frozen/accepted/6e3a430e4c3ac9b02c9cb33619c72235443cbf7ccc213c827f122974560ff812.json)
records the module statement identity
`sha256:9b4ddb20460c155a9916fda8b814e22d203d8a36102721da9ce6ff462adca63a`
and the declaration identity for `result`,
`sha256:7cc4d4742de3a61316cdb69eef32e9881e24ace9ae88545b3aa097f95fd8a80f`.
Its `prerequisite_frozen_node_ids` list is empty; the proof uses only the
pinned Mathlib imports recorded by the module. The Scribe `result` node keeps
`FromRepo` provenance and carries this dossier's typed `Proved` resolution
claim; the four definition nodes retain `FromLiterature` provenance.

## Triage

First tier: an explicitly numbered conjecture in a published paper,
preregistered in issue #9085. Resolution: `proved`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `result` | content | none | open-problem-resolution |

The content proof depends live on `cyclic_reindexing_sum` and
`cyclic_descent_distribution`; neither follows from pinned Mathlib by direct
instantiation, projection, or normalization. The result is a uniform symbolic
identity, not bounded enumeration, checker infrastructure, numeric reduction,
or a certified finite instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The bounded literature checks do not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. Source-to-Lean fidelity,
proof-shape classification, and admission classification are semantic
obligations rather than consequences of the frozen hashes.
