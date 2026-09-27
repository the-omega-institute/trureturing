---
slug: cao-chen-miller-egg-drop-conjecture-one
bibkey: caochenmiller2025eggdrop
doi: 10.48550/arXiv.2511.18330
url: https://arxiv.org/abs/2511.18330
triage: theorem
motivation_gids:
  - D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result
---

# Cao-Chen-Miller Conjecture 1: the multidimensional egg-drop bound

## Problem

Cao, Chen, and Miller, *Egg Drop Problems: They Are All They Are Cracked Up
To Be!*, arXiv:2511.18330v2, printed page 10, Conjecture 1:

> In a d-dimensional setting with sides N_1, N_2, ..., N_d and k eggs, the minimum
> number of drops required in the worst-case scenario under the same strategy satisfies

$$P_d(k) \le \left\lceil (k-d+1)(N_1+\cdots+N_d)^{1/(k-d+1)}\right\rceil,$$

> for k >= d.

The subscripted names and inequality above transcribe the printed notation.
Preregistration issue #8448 writes the positive integer domains explicitly.
The hidden point ranges over the product of the integer intervals
`{1, ..., N_i}`. A drop at `a` returns intact exactly when `a_i < x_i` for
every coordinate; otherwise it breaks one egg. The objective is exact recovery.

The formal `claim` weakens success of the paper's named strategy to existence
of any deterministic adaptive strategy with those outcomes and egg semantics:

```text
forall (d k : Nat) (N : Fin d -> Nat),
  1 <= d -> d <= k -> (forall i, 0 < N i) ->
    exists s : EggStrategy N k (paperBound d k N), Correct s
```

Refuting this weaker existence assertion refutes the named-strategy assertion.

## Motivation

At `d = 4`, `k = 5`, and sides `(5,5,5,5)`, the proposed budget is nine,
but there are 625 possible hidden points and only 512 nine-bit words.
This instance tests the conjecture without assuming any particular strategy.

## Gap

The arXiv identifier and egg-drop counterexample queries returned no resolution.
Crossref identifies a 2026 *Fibonacci Quarterly* publication of the same title,
DOI `10.1080/00150517.2026.2681644`, with zero recorded citations. OpenAlex
work `W4416935832` and its exact cites query returned zero citing works;
the Semantic Scholar DOI citations endpoint returned an empty array.
These bounded index readings do not establish historical priority.

`WorstCaseDepthInformationLowerBound` assumes transcript injectivity. The
missing input for this model is that exact recovery implies injectivity even
when a strategy stops before exhausting its budget.

## Route

Represent hidden coordinate `x_i` by `x_i - 1` in `Fin (N i)` and physical
query coordinates by `Fin (N i + 1)`. The comparison is then
`query_i <= hidden_i`. Strategy nodes consume one drop and, on the broken
branch, one egg. Stop nodes are allowed under unused budget.

Pad each terminal transcript with zeroes to the full drop budget. Structural
induction on the strategy proves that equal padded transcripts reach equal
terminal predictions. Correctness makes the transcript map injective.
At the displayed instance, the real-power ceiling is exactly nine, so
`Fintype.card_le_of_injective` would give `625 <= 512`, a contradiction.

## Falsifier

A correct strategy for all 625 points within nine drops would falsify the
counterexample. In the formal model it would contradict `result : Not claim`.
The source-to-model implication depends on the integer critical-point and
single binary-outcome semantics stated in the paper.

## Evidence

`D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.lean` proves
`result : Not claim`. The proof establishes `paperBound 4 5 (fun _ => 5) = 9`,
transcript injectivity for the alleged correct strategy, and the impossible
cardinality inequality. Its axiom closure is `propext`, `Classical.choice`,
and `Quot.sound`.

## Triage

`theorem`: the universal bound in Conjecture 1 is refuted by the specified
four-dimensional instance. No other statement from the paper is resolved here.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive. The publisher page returned HTTP 403,
and Semantic Scholar's separate metadata endpoint returned HTTP 429; neither
is counted as a completed content check. The target statement is the arXiv v2
text, not an independently checked version-of-record statement. No historical
priority claim follows from the zero citation or search counts.
