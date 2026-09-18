---
slug: misawa-nishimura-harmonic-strength-pair-refutation
bibkey: misawa2025spherical
doi: 10.48550/arXiv.2505.06893
url: https://arxiv.org/abs/2505.06893v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result
---

# Misawa--Nishimura harmonic-strength pair refutation

## Problem

Misawa and Nishimura, *Spherical Designs on S¹ of Finite Harmonic Strength*,
arXiv:2505.06893v2, Conjecture 3.3, printed page 6:

> Let p ≠ q be integers with p, q > 1. Then N({p, q}, 2) = 5.

Here N(T, 2) is the minimum size of a finite subset X of the unit circle
whose harmonic strength Hst(X) is exactly T. In the complex-moment form used
by the paper, Hst(X) consists of the natural indices k at which
P_k(X) = sum of x^k over x in X vanishes.

## Motivation

The assertion fixes the same minimum for every pair of distinct indices
greater than one. The pair {2,4} tests that universal quantifier through the
interaction of the second, fourth, and sixth moments of five unit-circle
points.

## Gap

Issue #8616 records the exact statement, its quantified Lean counterpart,
and a bounded literature search. Version 2 of the source retains the
conjecture. The same authors' arXiv:2607.01761 treats infinite harmonic
strength, not this finite pair; the searched Semantic Scholar citation list
contained no resolution. The value of N({2,4},2) is not determined here.

## Route

Suppose N({2,4},2) = 5. The natural-number infimum then belongs to its
nonempty set of attainable sizes, yielding a five-point unit-circle set
with exactly this harmonic strength. Square the five points. Their first
two power sums vanish, and their products with their complex conjugates
equal one. A polynomial combination of these relations makes the third
power sum vanish as well, so the original sixth moment is zero. But
6 is not in {2,4}, contradicting the exact harmonic strength.

## Falsifier

A five-point subset of the unit circle with harmonic strength exactly
{2,4} would refute the obstruction. In particular, such a set would
have vanishing second and fourth moments but a nonvanishing sixth moment,
contradicting the polynomial identity used by the formal theorem.

## Evidence

The frozen theorem
`D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result : Not claim`
uses the formal source definitions of moments, harmonic strength, unit-circle
membership, and minimum size. Its axiom closure is
`[propext, Classical.choice, Quot.sound]`. It establishes only the
counterexample to the universal equality, not a replacement minimum.

## Triage

`theorem`; the outcome is `refuted`. The sole public theorem has
`proof_shape: bind-only` and `admission_basis: open-problem-resolution`
for the preregistered external Conjecture 3.3. Its sixth-moment step is a
polynomial normalization of the five unit relations and vanishing moments,
not a separate escape witness.

## ASSUMED-UNVERIFIED

Google Scholar, MathSciNet, unpublished work, and exhaustive worldwide
priority were not verified. The bounded literature check is not a claim
that no other resolution exists.
