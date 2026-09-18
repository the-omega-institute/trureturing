---
slug: zhang-character-sum-difference-question-d-refutation
bibkey: zhang2025problems
doi: 10.48550/arXiv.2506.17235
url: https://arxiv.org/abs/2506.17235v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result
---

# Refutation of Zhang's character-sum constant restriction

## Problem

Question (D) of Wenpeng Zhang, *Some interesting number theory problems*,
arXiv:2506.17235v1, asks whether the fixed constant `c` in identity (2) can
only be 0 or 2. Identity (2) compares the Legendre character sums of two
fundamentally different integer-coefficient polynomials. Following the
preceding corollary, the formal statement uses one constant for every odd
prime.

## Motivation

Issue #8626 records the source quotation, full quantifiers, literature-status
scope, and the proposed quadratic counterexample. The result tests the literal
restriction on `c`, including the paper's stated meaning of fundamentally
different polynomials.

## Gap

The bounded source and literature searches found no earlier proof or
refutation of Question (D) in the searched scope. Nica's arXiv:2507.09991
addresses identity (1), not the constant restriction in Question (D). This
dossier makes no claim of exhaustive literature coverage or publication
priority.

## Route

Set `f(X) = X^2` and `g(X) = (X+1)^2`. For every odd prime `p`, all terms in
the first character sum equal 1, so its value is `p-1`. In the second sum, the
term at `x=p-1` is 0 and all earlier terms equal 1, so its value is `p-2`.
The two symbol-valued functions differ at `x=p-1`, and their character-sum
difference is the fixed constant `c=1`.

## Falsifier

A proof that either displayed sum has a different value for some odd prime,
or that the two Legendre-symbol functions agree throughout the summation
domain for some odd prime, would invalidate the counterexample.

## Evidence

- Frozen result: `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result`.
- The result has type `Not claim` and is kernel-checked in the pinned Lean
  toolchain.
- Its axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`; resolution `refuted` for Question (D)'s literal restriction on the
constant. The proof shape is `bind-only`, with no escape witness; admission is
by the preregistered external-open-problem resolution in issue #8626.

## ASSUMED-UNVERIFIED

The bounded literature search is not exhaustive and does not establish
worldwide novelty or priority. Unpublished resolutions remain unverified.
