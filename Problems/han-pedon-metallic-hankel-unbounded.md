---
slug: han-pedon-metallic-hankel-unbounded
bibkey: han2025hankel
doi: 10.48550/arXiv.2502.05993
url: https://arxiv.org/abs/2502.05993v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result
---

# Unboundedness of the Large-Shift Hankel Determinants of q-Metallic Numbers

## Problem

Guo-Niu Han and Emmanuel Pedon, *Hankel continued fractions and Hankel determinants for q-deformed metallic
numbers*, arXiv:2502.05993v2, Section 1, Conjecture E, part 2. Let Φ_n(q) = Σ_i f_i qⁱ be the power series with
constant term 1 satisfying q Φ² + ((1 + qⁿ)(1 − q) − q[n]_q) Φ = 1, and let Δ_j^{(ℓ)} = det(f_{ℓ+a+b})_{0≤a,b<j}.
The conjecture states that for every n ≥ 1 and every ℓ ≥ n + 3 the sequence (Δ_j^{(ℓ)})_{j≥0} is unbounded. The
printed superscript reads n + 2; the varying shift ℓ is intended, as the quantifier ℓ ≥ n + 3 shows.

## Motivation

The theorem `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result` establishes, for every n ≥ 1, the
existence of Φ_n over ℤ and the unboundedness of Δ^{(ℓ)} for every solution and every ℓ ≥ n + 3.

## Gap

Pre-registration issue 12794 records the literature screen: the paper proves boundedness for ℓ ≤ n + 1, part 1 of
the conjecture (ℓ = n + 2) is `D5/S3/Combinatorics/MetallicHankel/MetallicHankel`, and the later papers of Pedon,
Ovsienko–Pedon and Han that were inspected do not treat part 2. This is a bounded negative finding.

## Route

1. A cofactor identity for the inverse Hankel matrix at the normal indices of the Hankel continued fraction of the
   shift n + 1, valid across runs of vanishing determinants, together with a transfer computation over the dual
   numbers uniform in n (and the three-periodic continued fraction for n = 1), gives
   Δ_{Pk−1}^{(n+3)} = (−1)^k 2k for n = 1 and (−1)^{nk}(4n + 2)k for n ≥ 2, where P = 2n(n + 1).
2. The Desnanot–Jacobi identity and an exponential bound on |f_i| give a bounded-strip lemma: if two rows a < b of
   shifted determinants are bounded, every row between them is bounded.
3. Since the row n + 1 is bounded and the row n + 3 is unbounded, no row ℓ ≥ n + 3 can be bounded.

## Falsifier

The statement would fail if Δ^{(n+3)} were bounded for some n, which the exact subsequence excludes, or if the
bounded-strip propagation failed for some intermediate row.

## Evidence

An independent referee implementation checked the subsequence formula for n = 1, …, 8 and k = 1, 2, 3 (for n = 8 the
values are 34, 68, 102), 1,932 Desnanot–Jacobi identities and 65,550 strip inequalities on computed data.

## Triage

`theorem`; the statement is part 2 of Conjecture E of arXiv:2502.05993v2, quantified over every n ≥ 1 and ℓ ≥ n + 3.

- Proved (formalized): Δ^{(ℓ)} is unbounded for every n ≥ 1 and ℓ ≥ n + 3, with the explicit subsequence
  Δ_{Pk−1}^{(n+3)} growing linearly in k.
- Computed: for n = 1, …, 5 the whole sequence Δ^{(n+3)} follows an affine pattern in each residue class modulo P.
- Open: closed forms for Δ^{(ℓ)} with ℓ ≥ n + 4 and the full affine pattern for ℓ = n + 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named above, web and GitHub searches and the repository checks.
