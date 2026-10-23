---
slug: andrews-el-bachraoui-dprime-eventual-positivity
bibkey: andrews2025positive
doi: 10.48550/arXiv.2507.09276
url: https://arxiv.org/abs/2507.09276v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result
---

# Eventual positivity of the complete D-prime family

## Problem

George E. Andrews and Mohamed El Bachraoui, *Certain positive q-series and inequalities for two-color partitions*,
arXiv:2507.09276v1, Conjecture 5: “If k>m, then sum of D'(k,m,n) q^n is eventually positive.” The source defines
positive to mean that all coefficients are nonnegative. Its parameters k and m are positive integers.

The exact assertion is: for every natural k and m with 1 ≤ m < k, there exists a natural N depending on k and m,
such that D'(k,m,n) ≥ 0 for every natural n ≥ N. Equation (1.3) defines this coefficient by

Σ_n D'(k,m,n) q^n = Σ_{j≥0} q^{m(2j+2)} (q^{2j+4};q²)_∞ (q^{2j+2+2k};q²)_∞ / (q^{2j+3};q²)_∞².

The original `AndrewsElBachraouiDefs.dCoeff` uses precisely these factors and degree n, without a coefficient shift.
For m ≥ 1, omitted summands and product factors have degree above n. The finite truncation therefore retains the
source coefficient exactly.

## Motivation

The assertion includes both coefficient parities, the smallest pair (2,1), the m = 1 family and the m = k−1 family.
A threshold uniform over k and m is not required. Native Conjectures 2, 3 and 4 concern different parameter choices
and sign statements.

## Gap

Preregistration issue [19323](https://github.com/the-omega-institute/trureturing/issues/19323) records the complete
quantifiers, source correspondence and bounded prior comparison. The inspected v1 of Chern and Wang,
arXiv:2601.19845, proves the C-prime(k,1) positivity assertion. Its finite positive expansion does not establish
coefficient domination over the product subtracted in D-prime, or the complete D-prime eventual assertion.
This is a statement about the inspected v1, without a global priority or literature-absence claim.

## Route

1. Two applications of the existing nilpotent q-binomial identity prove the full source transformation modulo
   X^{n+1}. Finite subset expansion gives a fixed rational series R, and finite product cancellation gives a fixed
   Gauss convolution product P. For every n, the original coefficient is [q^n]R − [q^n]P.
2. Arithmetic-progression summation proves the normalized coefficient limit of each finite geometric product.
   Finite monomial shifts and finite sums preserve these limits. For h = k−1, the rational limit is
   r_h = 2^{h−1}/(h ((2h−1)!!)^2). Its numerator subset constant is the integral of (1−x²)^{h−1} on [0,1].
3. The existing parity-compatible triangular-pair injection bounds the first Gauss product by square-root row
   sums. A quarter-circle integral gives the upper bound πn/4 + 5√(2n+1/2)/4 + π/16 + 3/8. An explicit real upper
   sequence is propagated through all required even-step geometric convolutions; its normalized limit is
   p_h = π/(2^{h+1}(h!)²). The argument needs this upper sequence, not an assumed exact Gauss asymptotic.
4. The existing Wallis lower bound proves r_h > p_h for every h ≥ 1. The normalized difference between the rational
   coefficients and the explicit upper sequence has positive limit. It therefore bounds the original coefficient
   positively for every sufficiently large n, including every residue class.

## Falsifier

The target would fail for an admissible fixed pair k,m with arbitrarily large n having dCoeff k m n < 0.
A radial limit, a finite range, a statement on one parity, or an added analytic hypothesis does not settle it.

## Evidence

`D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result` proves the exact all-parameter eventual
nonnegativity statement on `AndrewsElBachraouiDefs.dCoeff`. Its proof uses the source-owning reduction, Gauss and
constant modules, and the original nilpotent q-binomial and Gauss coefficient suppliers. All series identities and
all limits used in the proof are discharged in Lean. No new axiom or assumed asymptotic is introduced.

## Triage

- Proved in Lean: the complete original eventual nonnegativity assertion for every k>m≥1.
- The proof's deciding mechanism is the strict leading gap, independent of m after the finite subset constant is
  evaluated. The finite prefix can contain negative coefficients; the statement asserts no positivity there.
- The threshold is existential and may depend on both parameters. No uniform threshold or explicit optimal
  threshold is claimed.
- Existing special cases and their consumers remain separate declarations. No additional resolution is counted
  from those cases or from the auxiliary coefficient identities.

## ASSUMED-UNVERIFIED

The supplied primary fulltext is arXiv:2507.09276v1, whose metadata gives 12 July 2025 while its displayed document
date is 24 August 2026. This does not establish another version. The prior comparison is limited to the supplied
and inspected fulltexts. Worldwide present openness, priority and absence of other proofs are not asserted.
