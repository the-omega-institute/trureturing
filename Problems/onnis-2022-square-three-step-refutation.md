---
slug: onnis-2022-square-three-step-refutation
bibkey: onnis2022happyv1
doi: null
url: https://arxiv.org/abs/2203.03381v1
triage: theorem
motivation_gids:
  - D5/S1/Digit/OnnisSquareThreeStepRefutation
---

# Refutation of Onnis's square convergence prohibition

## Problem

Luca Onnis, *On a variant of the happy numbers and their generalizations*,
arXiv:2203.03381v1, Section 3, "Conjecture 1" (verbatim):

> There are no perfect square that are term of the sequence with length of convergence equal to 3.

Section 1.2 defines `F(n)` to be the square of the product of the nonzero
decimal digits of `n`. A positive integer is a sequence member when some
finite iterate reaches one. With `F^[0](n) = n`, exact convergence length
three means `F^[3](n) = 1` and `F^[k](n) != 1` for every natural `k < 3`.

The closed proposition `claim` is exactly:

```text
∀ n : ℕ, 0 < n → (∃ r : ℕ, n = r ^ 2) →
  SequenceMember n → ¬ FirstHit n 3
```

`SequenceMember n` is `∃ t : ℕ, step^[t] n = 1`, and `FirstHit n t` is
`step^[t] n = 1 ∧ ∀ k : ℕ, k < t → step^[k] n ≠ 1`. The square root is
an arbitrary natural number. There is no smoothness, image, digit-alphabet,
root-bound or exponent-variation condition.

## Motivation

One positive perfect-square member with first hitting time three contradicts
the whole universal prohibition. The distinction between an arbitrary
initial square and the image of a preceding digit-product step matters:
Section 3 itself uses the root 7152 with prime factor 149.

## Gap

The exact versioned source calls the statement a conjecture. The available
bounded arXiv metadata searches found only v1 and no recorded resolution of
this Section 3 statement. The OEIS A351327 comparison concerned the different
at-most-three assertion. OpenAlex and Semantic
Scholar requests returned HTTP 429. Global resolution history and priority
are unverified; this result makes no historical-priority claim.

## Route

Take `n = 55225 = 235^2`. Mathlib's `Nat.digits 10` gives the little-endian
lists `[5,2,2,5,5]`, `[0,0,0,0,5,2]` and `[0,0,1]` for 55225, 250000 and
100. `Nat.digits_ofDigits` supplies these exact decimal representations,
with digit bounds and nonzero final digits. Filtering out every zero and
multiplying gives 500, 10 and 1. Squaring gives the three transitions
`55225 -> 250000 -> 100 -> 1`.

`Function.iterate` and its successor equations give the iterates at indices
one, two and three. The last equality supplies sequence membership. The
three earlier indices are exactly zero, one and two, whose values are
55225, 250000 and 100, all different from one. Positivity and the square
witness 235 discharge the remaining hypotheses of `claim`.

## Falsifier

A proof of the literal `claim` would contradict `result : ¬ claim` at the
explicit positive square 55225. A zero-including digit product, an omitted
index zero, or a restriction to digit-product images would instead change
the original problem and would not establish this result.

## Evidence

The mathematical source is
`D5/S1/Digit/OnnisSquareThreeStepRefutation.lean`; the owning theorem is
`D5.S1.Digit.OnnisSquareThreeStepRefutation.result : ¬ claim`.
All decimal, filter, square, iteration, membership and first-hit calculations
occur in this theorem's proof. The only imported ingredients are pinned
mathlib digit and iteration APIs and kernel-checked arithmetic tactics.
The corresponding Blueprint binds the result to this dossier as `Refuted`.

## Triage

`theorem`. The explicit square refutes the entire Section 3 Conjecture 1.
Section 4's at-most-three assertion, higher-exponent variants, image-restricted
claims, a census and least-counterexample questions are outside this result.

## ASSUMED-UNVERIFIED

The bounded prior literature checks do not establish exhaustive resolution
history or historical novelty. Neither the source's separate Section 4
assertion nor any restricted square-family classification is settled here.
