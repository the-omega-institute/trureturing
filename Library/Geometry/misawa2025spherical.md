---
bibkey: misawa2025spherical
authors: Ryutaro Misawa, Yusaku Nishimura
year: 2025
title: Spherical Designs on S¹ of Finite Harmonic Strength
doi: 10.48550/arXiv.2505.06893
url: https://arxiv.org/abs/2505.06893v2
claim: Conjecture 3.3 asserts N({p,q},2) = 5 for all distinct integers p,q greater than one.
strata_touched:
  - D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation
license: citation-only
triage: anchor
---

# Spherical Designs on S¹ of Finite Harmonic Strength

Conjecture 3.3 on printed page 6 states verbatim:

> **Conjecture 3.3.** Let p ≠ q be integers with p, q > 1. Then
> N({p, q}, 2) = 5.

The same page defines
`N(T, 2) := min{|X| | X ⊂ S¹, Hst(X) = T}` for a nonempty finite set
`T ⊂ ℕ`. Printed pages 2--3 identify `S¹` with
`{z ∈ ℂ | |z| = 1}`, define `P_k(X) := Σ_{x∈X} x^k`, and give the
working form `Hst(X) = {k ∈ ℕ | P_k(X) = 0}`. Lemma 3.6 is on printed
pages 7--8; printed page 11 restates the determination of `N({p,q},2)` as
Problem 3.15.

For five unit-modulus points with `P_2 = P_4 = 0`, square the points to obtain
five values `y_i`. Their first two power sums vanish. Conjugation and
`y_i conj(y_i) = 1` then give the polynomial identity forcing the third power
sum to vanish, hence `P_6 = 0`. Therefore a five-point set cannot have harmonic
strength exactly `{2,4}`. This refutes the universal conjecture without
determining `N({2,4},2)`.

The symbolic polynomial certificate has Groebner remainder zero. Independent
numerical readings found all 400 of 400 five-point BFGS runs converging to
`P_2 = P_4 = 0` with `|P_6| <= 2.1e-12`; six-point controls reached values up
to approximately `6`. These are readings, not the proof.

The arXiv record retains Conjecture 3.3 in version 2 dated 30 June 2026. The
same authors' arXiv:2607.01761 does not settle the finite two-element case.
Semantic Scholar reported zero citations. Google Scholar and MathSciNet were
not verified.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2505.06893
- URL: https://arxiv.org/abs/2505.06893v2
- Version and location: arXiv:2505.06893v2, printed pages 2--8 and 11.
