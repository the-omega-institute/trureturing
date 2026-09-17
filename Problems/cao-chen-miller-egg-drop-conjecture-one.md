---
slug: cao-chen-miller-egg-drop-conjecture-one
bibkey: caochenmiller2025eggdrop
doi: 10.48550/arXiv.2511.18330
url: https://arxiv.org/abs/2511.18330
triage: theorem
motivation_gids:
  - D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result
---

# Refutation of Cao--Chen--Miller Conjecture 1

## Problem

Cao, Chen, and Miller, *Egg Drop Problems: They Are All They Are Cracked Up
To Be!*, arXiv:2511.18330v2, printed page 10, state:

> Conjecture 1. In a d-dimensional setting with sides N_1, N_2, ..., N_d and
> k eggs, the minimum number of drops required in the worst-case scenario
> under the same strategy satisfies P_d(k) <= ceil((k-d+1) *
> (N_1+N_2+...+N_d)^(1/(k-d+1))), for k >= d.

The formal claim asks for a deterministic adaptive strategy that exactly
recovers every critical point for every positive side function and every
`1 <= d <= k`. This existence statement is weaker than success of the
paper's named strategy, so its refutation also refutes the printed claim.

## Motivation

Every drop returns one broken-or-intact bit. A strategy that always recovers
the hidden point must therefore separate all hidden points by its answer
transcripts. Comparing the hidden-point count with the number of transcripts
can disprove a proposed worst-case budget without constructing an optimal
strategy.

## Gap

Preregistration issue #8448 records the printed statement, its full
quantifiers, and the proposed `d=4`, `k=5`, `(5,5,5,5)` counterexample. The
checked literature surfaces were the source paper and arXiv record, Crossref,
OpenAlex, Semantic Scholar, and the publisher page. The completed checks found
no published proof or refutation. The publisher returned HTTP 403, and one
Semantic Scholar metadata request returned HTTP 429. These searches are
bounded and do not establish priority.

## Route

For `d=4`, `k=5`, and every side length equal to five, the conjectured real
power expression has natural ceiling nine. There are `5^4=625` possible
hidden points. Pad every root-to-leaf answer sequence with zeroes to length
nine. Correctness makes this padded-transcript map injective: equal transcripts
follow equal branches to equal terminal predictions, and each prediction is
the hidden point. The target transcript space has cardinality `2^9=512`, so
the resulting injection would imply `625 <= 512`, a contradiction.

## Falsifier

The refutation would fail if the printed ceiling did not evaluate to nine at
these parameters, if one drop conveyed more than one broken-or-intact bit, if
exact recovery did not force padded transcripts to be injective, or if either
finite-cardinality calculation were incorrect.

## Evidence

- Frozen theorem:
  `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result`.
- The theorem statement ID is
  `sha256:2d76724c598e4e2bd8e0499fd2ec5441ec9f1e46467eaf994dd04c1c4281a726`.
- The axiom closure is std3: `propext`, `Classical.choice`, and `Quot.sound`.
- The Lean proof derives transcript injectivity by induction on the adaptive
  strategy and obtains the final contradiction from
  `Fintype.card_le_of_injective`.

## Triage

`theorem`. The public theorem `result : Not claim` has proof shape `content`.
Its escape witness is the live construction proving that exact recovery makes
the fixed-length padded-transcript map injective. The module admission basis is
`escape-witness`; the resolution marker is attached only to `result`.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive, and no first-publication or priority
claim is made. The correspondence between the natural-language conjecture and
the Lean model is a reviewed statement echo, not a machine-decidable semantic
equivalence. The formal claim deliberately grants any deterministic adaptive
strategy rather than only the paper's named strategy; this strengthens the
refutation rather than weakening it.
