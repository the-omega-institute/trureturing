---
slug: oeis-a077866-least-two-subset-count
bibkey: kimberling2022a077866
doi: null
url: https://oeis.org/A077866
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount
---

# Least-two-element subset count

## Problem

Kimberling's 2022 OEIS A077866 comment asks whether the number `b(N)` of
subsets of `{1,...,N}` with more than one element, whose least two elements
sum to the maximum, satisfies `b(0)=b(1)=b(2)=0` and
`b(n+3)=A077866(n)` for every `n>=0`.

## Motivation

This is a tier-one named external conjecture. Issue #11414 recorded the
literal statement, source and bounded prior-work check before the Lean probe.
The issue is a preregistration locator, not proof evidence.

## Gap

The source's weighted-triangle and parity formulas for A077866 are public.
The checked sources did not provide a proof of the proposed subset
interpretation. The bounded check covered the OEIS entry and related
entries A122196 and A053599, MathDB search results, this repository,
GitHub searches, and pinned Mathlib. It does not establish global novelty.

## Route

For a counted set, write its least two elements as `0<a<b`. Its maximum
must be `a+b<=N`; all remaining members form an arbitrary subset of the
open interval `(b,a+b)`, which has `a-1` elements. The Lean proof establishes
both directions and uniqueness of this decomposition. Hence
`b(N)=sum_{a=1}^N (N-2*a)*2^(a-1)`. Evaluating at odd and even `N`
gives the OEIS formulas. A separate recursive definition with initial
values `1,2,5,8` and the source generating function's recurrence is
proved equal to those formulas at every index.

## Falsifier

A counted subset outside the decomposition, a decomposed set failing the
least-two/max property, or a term where the recursive sequence differs
from the source generating function would break the bridge. Finite
agreement alone would not settle the all-index assertion.

## Evidence

`D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.lean` defines the
literal set predicate, its cardinality, the independent recurrence and
the all-index claim. The current proof uses only standard Lean axioms.
Source fidelity, repository admission, publication and merge remain
separate checks until their respective receipts exist.

## Triage

`theorem`; resolution `proved`; admission basis `open-problem-resolution`;
`proof_shape: content`, with the unique finite-set decomposition as the
new live proof step. The public theorem is the complete original assertion.

## ASSUMED-UNVERIFIED

The literature check is bounded to the named sources and searches above;
no claim of a first proof is made. The equivalence between the OEIS
generating function and the displayed recurrence is ordinary coefficient
extraction and is recorded in the source note; the Lean theorem identifies
the sequence using its initial values and recurrence.
