---
slug: han-pedon-metallic-hankel-shift
bibkey: han2025hankel
doi: 10.48550/arXiv.2502.05993
url: https://arxiv.org/abs/2502.05993v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result
---

# Periodicity of the Shift n + 2 Hankel Determinants of q-Metallic Numbers

## Problem

Guo-Niu Han and Emmanuel Pedon, *Hankel continued fractions and Hankel determinants for q-deformed metallic
numbers*, arXiv:2502.05993v2, Section 1, Conjecture E, part 1. Let Φ_n(q) = Σ_i f_i qⁱ be the power series with
constant term 1 satisfying q Φ² + ((1 + qⁿ)(1 − q) − q[n]_q) Φ = 1, where [n]_q = 1 + q + ⋯ + q^{n−1}, and let
Δ_j^{(ℓ)} = det(f_{ℓ+a+b})_{0≤a,b<j}. The conjecture states that for n ≥ 2 the sequence Δ^{(n+2)} satisfies
Δ_{j+2n(n+1)}^{(n+2)} = (−1)ⁿ Δ_j^{(n+2)} for every j and takes only the values −2, −1, 0, 1, 2.

## Motivation

The theorem `D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result` establishes, for every n ≥ 2, the existence
of Φ_n over ℤ and the periodicity and value set of Δ^{(n+2)} for every solution.

## Gap

Pre-registration issue 12749 records the literature screen: the paper proves the analogous statements for the shifts
ℓ ≤ n + 1, and the case n = 1 of the shift n + 2 is due to Ovsienko and Pedon; the later paper arXiv:2604.19898 does
not treat the shift n + 2. This is a bounded negative finding.

## Route

1. The quadratic equation determines Φ_n over ℤ, and concrete quadratic transitions between successive shifted
   series, uniform in n ≥ 2, replace the Hankel continued fraction of the shift n + 1.
2. A division-free determinant lemma computes the next shift from the previous one, including the sizes at which the
   unshifted determinant vanishes.
3. A two-state transfer calculation along one period shows that the top coefficients return with sign (−1)ⁿ and stay
   bounded by 2 in absolute value, which gives the antiperiod 2n(n+1) and the value set.

## Falsifier

The statement would fail if some Δ_j^{(n+2)} had absolute value at least 3, or if the transfer after one period
changed a determinant by a factor other than (−1)ⁿ.

## Evidence

An independent referee implementation computed the coefficients from the quadratic equation and the determinants
exactly for n = 2, …, 9 through j = 2·2n(n+1) + 5.

## Triage

`theorem`; the statement is part 1 of Conjecture E of arXiv:2502.05993v2, quantified over every n ≥ 2 and j ≥ 0.

- Proved (formalized): for n ≥ 2, Δ^{(n+2)} is 2n(n+1)-periodic for even n and antiperiodic for odd n, with values in
  {−2, −1, 0, 1, 2}.
- Computed: for ℓ = n + 3 the determinants grow linearly in j for n = 1, …, 4.
- Open: part 2 of Conjecture E, that Δ^{(ℓ)} is unbounded for every ℓ ≥ n + 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named above, web and GitHub searches and the repository checks.
