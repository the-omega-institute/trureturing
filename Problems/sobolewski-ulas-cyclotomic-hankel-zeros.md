---
slug: sobolewski-ulas-cyclotomic-hankel-zeros
bibkey: sobolewski2026hankel
doi: 10.48550/arXiv.2607.09376
url: https://arxiv.org/abs/2607.09376v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel.result
---

# Zeros of Binary Digit Hankel Determinants at Twice a Root of Unity

## Problem

Bartosz Sobolewski and Maciej Ulas, *Hankel determinants of weighted binary sums of digits*, arXiv:2607.09376v1,
Section 5.1, Conjecture 5.7. For u = Σ_j ε_j 2^j with binary digits ε_j put S(u,t) = Σ_j ε_j t^j and
H(n,t) = det[S(i+j,t)]_{0≤i,j<n}. For d ≥ 2 and ℓ ≥ d + 1 write ℓ = qd + r with q ≥ 1 and 1 ≤ r ≤ d, let
z_{d,ℓ} = 2^r (2^{qd} − 1)/(2^d − 1) − 2 for r < d and z_{d,ℓ} = 2^d (2^{qd} − 1)/(2^d − 1) − 1 for r = d, and let
A_d be the set of positive integers in ⋃_{ℓ≥d+1} ⋃_{s odd} (2^ℓ s − z_{d,ℓ} − 1, 2^ℓ s + z_{d,ℓ} + 1]. The conjecture
states that for every primitive d-th root of unity ζ and every n ≥ 2, H(n, 2ζ) = 0 if and only if n ∈ A_d.

## Motivation

The theorem `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel.result` establishes the equivalence for every
d ≥ 2, every primitive d-th root of unity ζ and every n ≥ 2.

## Gap

Pre-registration issue 12688 records the literature screen: the paper proves the vanishing on A_d (Theorem 5.4) and
states that the nonvanishing outside A_d is the difficulty; the arXiv record has a single version, and web and GitHub
searches found no proof. The case d = 2 is `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel`. This is a bounded
negative finding.

## Route

1. The determinant recursions of the paper (Theorem 4.2 in scalar polynomial form, extended to the degenerate case
   by polynomial identity) relate H and an auxiliary bordered determinant at n to their values at a smaller index,
   with explicit fixed bases depending on the binary phase of n.
2. Vanishing on A_d follows from sparse kernels, as in Theorem 5.4.
3. A valuation at a prime above 2 in the cyclotomic field shows that the two terms of each recursion never cancel
   off A_d, using the vanishing of the auxiliary determinant at singular endpoints.
4. A description of the complement of A_d by forbidden binary runs closes the induction.

## Falsifier

The statement would fail if the two terms of a recursion had equal valuation and cancelled at some n ∉ A_d, or if a
kernel vector failed to exist at some n ∈ A_d.

## Evidence

An independent referee implementation checked the statement by exact cyclotomic arithmetic for d = 2, …, 10 and 12
and every 2 ≤ n ≤ 128, and the phase recursions through n = 256.

## Triage

`theorem`; the statement is Conjecture 5.7 of arXiv:2607.09376v1, quantified over every d ≥ 2, every primitive d-th
root of unity and every n ≥ 2.

- Proved (formalized): H(n, 2ζ) = 0 exactly for n ∈ A_d.
- Open: the values of H(n, 2ζ) outside A_d beyond their nonvanishing, for d ≥ 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, web and GitHub searches and the repository checks.
