---
slug: takemura-fixed-point-apd-conjecture-2
bibkey: takemura2025apd
doi: 10.48550/arXiv.2512.18169
url: https://arxiv.org/abs/2512.18169v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue
---

# Takemura's fixed-point first appearance value

## Problem

For `n >= 2`, let `fix(sigma)` be the number of fixed points of a
permutation `sigma` of `Fin n`, and define

```text
APD_m(fix) = sum_{sigma in S_n} sign(sigma) * fix(sigma)^m.
```

Takemura's Conjecture 2 in arXiv:2512.18169v1 asks to prove the value at
degree `n - 1`:

```lean
theorem resultValue (n : Nat) (hn : 2 <= n) :
    apd n fix (n - 1) = (n.factorial : Int)
```

The source reports numerical verification through `n = 10` and leaves the
statement unproved.

## Motivation

The conjecture gives the exact first nonzero alternating power difference,
not only its degree. Its factorial value reflects the count of injections
from an `(n - 1)`-element index type into an `n`-element set.

## Gap

The source explicitly labels the formula Conjecture 2. The bounded
literature check registered in issue #8837 found only arXiv:2512.18169v1
and a later paper by the same author that restates the APD definition but
does not prove this conjecture. The checked Semantic Scholar citation list
was empty. Repository, pinned Mathlib, and external Lean ecosystem searches
found no theorem with the complete APD value statement. This is a bounded
search result, not an exhaustive worldwide absence claim.

## Route

Expand `fix(sigma)^(n-1)` as a sum over `(n - 1)`-tuples and exchange the
tuple and permutation sums. For a tuple image `S`, reindex permutations
fixing `S` pointwise by permutations of its complement. Their signs sum to
zero when the complement has at least two elements and to one otherwise.
At degree `n - 1`, the surviving tuples are exactly the injections from
`Fin (n - 1)` to `Fin n`. Their descending-factorial count simplifies to
`n!`.

## Falsifier

A natural `n >= 2` for which the signed sum over all permutations differs
from `n!` would refute the statement. A computation using unsigned
permutations, a subset rather than all of `S_n`, or a different fixed-point
convention addresses a different claim.

## Evidence

The source statement and definitions are recorded in
`Library/ArithSums/takemura2025apd.md`. The frozen theorem is
`D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue`,
with declaration statement ID
`sha256:53c7bb8dc65bcf39d1fd31f07237f879f761da939051c515e3b00ed67ce72ac6`.
Its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The module freeze has no prerequisite frozen project nodes; the proof uses
only pinned Mathlib facts.

## Triage

First tier: an explicitly numbered conjecture in a 2025 arXiv paper,
preregistered in issue #8837. Resolution: `proved`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `resultValue` | bind-only | none | open-problem-resolution |

After local helper expansion, the proof consists of pinned-library
instantiation, reindexing, finite-sum normalization, injection counting,
and factorial normalization. It therefore has no escape witness. The
external conjecture is admitted under `open-problem-resolution`, not
`escape-witness`. The uniform symbolic theorem is not bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite instance,
so `utility: none` applies.

## ASSUMED-UNVERIFIED

Google Scholar and MathSciNet were not searched. The literature finding
does not claim exhaustive global novelty, priority, or absence of an
independent proof. Bounded numerical checks through `n = 10` do not prove
the universal statement.
