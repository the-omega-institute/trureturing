---
slug: akyazi-zavadski-2026-romik-conjecture-1-3
bibkey: akyazizavadski2026romik
doi: null
url: https://arxiv.org/html/2611.26570v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary
---

# Romik cylinder boundary conjecture 1.3

## Problem

Akyazi-Zavadski, Berestycki and Chhita, arXiv:2611.26570v1, Conjecture 1.3, equation (1.2).

> For every $k\ge2$, the rational function $R_k$ from Theorem 1.2 satisfies $R_k(k)=R_{k-1}(k)$.

Theorem 1.2 requires $R_m(N)=\mathbb P_{\mathcal C_N}(F_m)$ for every integer $1\le m<N$. Corollary 4.2, (4.4), and the identification (5.25) give the probability by the explicit Pfaffian constructed using Lemma 4.3 and (4.12), (5.1)–(5.3).

## Motivation

The settling declaration is
`D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary`.
It establishes the boundary equality as a consequence of the published open-range identity.

## Gap

Preregistered proof criterion and source scope: https://github.com/the-omega-institute/trureturing/issues/34287.

The paper establishes rationality and regularity at the boundary, and reports symbolic equality for $2\le k\le8$. Its general equality is the target.

## Route

| Published clause | Lean counterpart |
| --- | --- |
| Rational functions $R_m\in\mathbb Q(N)$ | `R : ℕ → RatFunc ℚ` |
| Theorem 1.2 with (4.4) as identified in (5.25) | `hR : ∀ m N : ℕ, 1 ≤ m → m < N → RatFunc.eval (RingHom.id ℚ) (N : ℚ) (R m) = pfaffian (cylinderMatrix m (N : ℚ))` |
| Every integer $k\ge2$ | `(k : ℕ) (hk : 2 ≤ k)` |
| Rational continuation | First two conjuncts identify the two functions with explicit `rationalCylinder` functions |
| Regularity at $N=k$ | Third and fourth conjuncts give membership in `regularAt (k : ℚ)` |
| $R_k(k)=R_{k-1}(k)$ | Fifth and sixth conjuncts give each canonical evaluation as `pfaffian (cylinderMatrix (k - 1) (k : ℚ))` |

The forced final pair lemma uses the original normalized Pfaffian and explicitly extends normalized listings by the final two endpoints, preserving their permutation signs. The cylinder reduction uses the vanishing product at the last white endpoint. Regular specialization follows from the precise bounds on variable denominator indices and the ring homomorphism on the subring of regular rational functions. Uniqueness on the infinite natural tail follows by removing the finite reduced-denominator root sets and applying polynomial equality at infinitely many points.

## Falsifier

A counterexample to (1.2) would require an integer $k\ge2$ for which the source functions satisfy the open-range premise but have unequal regular evaluations. The six conjuncts rule out such a counterexample under the published identity.

## Evidence

- `pfaffian_forced_last_pair` proves the generic commutative-ring forced-pair factorization.
- `cylinder_pfaffian_boundary` proves the all-size unit pair reduction including size one.
- `evaluate_rationalCylinder` proves regularity and canonical evaluation for all natural $m\le k$, including zero.
- `source_rationalCylinder_boundary` proves the six-conjunct result from the exact open-range premise.

## Triage

Proved using the published open-range identity as the hypothesis of the kernel-checked algebraic theorem. Equation (2.8) of the paper identifies the common value with $1/A_k$. The probability correspondence, Kasteleyn identity and alternating-sign-matrix enumeration remain literature inputs outside the formalization.

## ASSUMED-UNVERIFIED

The four public theorem registrations remain unfinished. They need compiled enrolled readouts with exact source occurrence selection and reconstruction, kernel-checked variation and sensitivity, and validated binding evidence. The generic factorization requires the commutative-ring dictionary in its enrolled signature. The cylinder reduction requires the size-dependent matrix operand, and the two evaluation theorems require their rational-function operands and evaluation coordinates. [Escape audit #34324](https://github.com/the-omega-institute/trureturing/issues/34324)
