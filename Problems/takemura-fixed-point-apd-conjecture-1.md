---
slug: takemura-fixed-point-apd-conjecture-1
bibkey: takemura2025apd
doi: 10.48550/arXiv.2512.18169
url: https://arxiv.org/abs/2512.18169v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree
---

# Takemura's fixed-point first appearance degree

## Problem

For `n >= 2`, let `fix(sigma)` be the number of fixed points of a
permutation `sigma` of `Fin n`, and define

```text
APD_m(fix) = sum_{sigma in S_n} sign(sigma) * fix(sigma)^m.
```

Takemura's Conjecture 1 in arXiv:2512.18169v1 asks to prove that the least
positive `m` for which this sum is nonzero is `n - 1`:

```lean
theorem resultDegree (n : Nat) (hn : 2 <= n) :
    firstAppearanceDegree n fix = n - 1
```

The source reports numerical verification through `n = 10` and leaves the
statement unproved.

## Motivation

The first appearance degree measures when the alternating projection of a
power of the fixed-point statistic first survives. The result identifies
that degree uniformly for every symmetric group in the stated range.

## Gap

The source explicitly labels the formula Conjecture 1. The bounded
literature check registered in issue #8837 found only arXiv:2512.18169v1
and a later paper by the same author that restates the APD definition but
does not prove this conjecture. The checked Semantic Scholar citation list
was empty. Repository, pinned Mathlib, and external Lean ecosystem searches
found no theorem with the complete first-appearance statement. This is a
bounded search result, not an exhaustive worldwide absence claim.

## Route

Expand `fix(sigma)^m` as a sum over `m`-tuples and exchange the tuple and
permutation sums. For a tuple image `S`, reindex permutations fixing `S`
pointwise by permutations of its complement. Their signs sum to zero when
the complement has at least two elements and to one otherwise. Hence every
APD with `1 <= m <= n - 2` vanishes. The separately frozen value theorem
gives `APD_(n-1)(fix) = n!`, which is nonzero, and the natural-number
infimum laws identify the least positive index as `n - 1`.

## Falsifier

A natural `n >= 2` for which some positive degree below `n - 1` has nonzero
APD, or for which degree `n - 1` has zero APD, would refute the statement.
A computation using unsigned permutations, a subset rather than all of
`S_n`, or a different fixed-point convention addresses a different claim.

## Evidence

The source statement and definitions are recorded in
`Library/ArithSums/takemura2025apd.md`. The frozen theorem is
`D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree`,
with declaration statement ID
`sha256:a5b7cfeeed15480a15ad0807b7a399fad5d83e31848b6cc1788ecf335db7ac2a`.
Its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The module freeze has no prerequisite frozen project nodes; the proof uses
only pinned Mathlib facts and the same module's `resultValue`.

## Triage

First tier: an explicitly numbered conjecture in a 2025 arXiv paper,
preregistered in issue #8837. Resolution: `proved`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `resultDegree` | bind-only | none | open-problem-resolution |

After local helper expansion, the proof consists of pinned-library
instantiation, reindexing, finite-sum normalization, counting, and natural
infimum laws. It therefore has no escape witness. The external conjecture
is admitted under `open-problem-resolution`, not `escape-witness`. The
uniform symbolic theorem is not bounded enumeration, checker
infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies.

## ASSUMED-UNVERIFIED

Google Scholar and MathSciNet were not searched. The literature finding
does not claim exhaustive global novelty, priority, or absence of an
independent proof. The paper's convention `m_1(f) = infinity` when every
APD vanishes is outside the natural-valued definition; the proved case is
nonempty, so that convention does not affect this theorem.
