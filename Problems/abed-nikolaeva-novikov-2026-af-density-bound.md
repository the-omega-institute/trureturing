---
slug: abed-nikolaeva-novikov-2026-af-density-bound
bibkey: abednikolaevanovikov2026traces
doi: 10.48550/arXiv.2610.34388
url: https://arxiv.org/abs/2610.34388v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.result
---

# Density-independent Alhasan–Fawwaz boundedness

## Problem

Abed, Nikolaeva and Novikov, *How characterisations of traces and central elements fail*,
arXiv:2610.34388v1, Section 11.2(5), ask:

> Is a bounded on M_n(C) independently of rho?

The selected question fixes a positive dimension and varies every strictly positive
density. Section 5.12 defines the quotient set using positive semidefinite A,
Hermitian B and nonzero X=A+iB. Section 3.1 uses the ordinary trace and
modulus |X|=(X*X)^(1/2), without a trace-one requirement.

## Motivation

A dimension-dependent bound controls every positive definite density on the
same matrix algebra, independently of its spectrum and scale.

## Gap

The source's Proposition 5.44(c) supplies the dimension-two bound. Its general
condition-dependent estimates do not give a bound depending only on dimension.
The selected question is the complete fixed-dimension boundedness sentence.

## Route

The matrix estimate `accretive_le_card_abs` proves A <= card(iota)|A+iB|
for every finite index type. It diagonalizes P=|X|, whose eigenvalues s_j
are nonnegative. The square identity gives norm(X e_j)=s_j; Hermitian B
and Cauchy–Schwarz give inner(e_j,A e_j)<=s_j. Expanding sqrt(A)v in
that basis and applying the triangle inequality and finite Cauchy–Schwarz
gives inner(v,A v)<=n inner(v,P v). No eigenvalue is inverted, so singular
nonzero X is included.

For rho positive definite and P positive semidefinite nonzero, factor rho=Y*Y
with Y invertible and P=Q*Q. Cyclicity gives
Tr(rho P)=Tr((YQ)*(YQ))>0. Nonnegativity of trace pairing with the matrix
order estimate bounds every defining quotient by n. A=I and B=0 gives
the value one. Real completeness supplies the stated IsLUB.

## Falsifier

The Lean definition `claim` is exactly

$$
\forall n\ge1\;\exists C\in\mathbb R,\quad C\ge0\quad\text{and}\quad
\forall\rho>0,\quad S_\rho\ne\varnothing,\quad
\operatorname{IsLUB}(S_\rho,\sup S_\rho),\quad \sup S_\rho\le C.
$$

Here S is the source's actual quotient set. The theorem `result : claim`
uses C=n. Nonempty IsLUB prevents the totalized real supremum from certifying
an empty or unbounded set. A failed proof search or a counterexample to a
smaller constant would not refute this claim.

## Evidence

The source is `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.lean`,
with its corresponding Blueprint Scribe and Reg mirror. The proof directly
reuses Mathlib's spectral theorem, matrix order and continuous functional
calculus, `bornProbability` from `D5.S3.Quantum.FiniteDimensional`, and
`RHLinalg.trace_mul_nonneg_of_posSemidef`.

The source-bound audits retain the complete index-type telescope and the full
boundedness claim. They observe respectively the dimension coefficient and
the selected exact quotient-set occurrence. Their residual continuation is
unknown; it asserts no undecidability or inexhaustibility result.

## Triage

Tier 1. The preregistration is [owner #22774](https://github.com/the-omega-institute/trureturing/issues/22774).
The independently approved ordinary argument is its
[complete-proof comment](https://github.com/the-omega-institute/trureturing/issues/22774#issuecomment-6606601813).
Admission basis: `open-problem-resolution`. Reused spectral, functional-calculus,
trace and Cauchy–Schwarz results are not claimed as new mathematics. All
auxiliary declarations have live consumers in the complete boundedness proof.

The proof establishes fixed-dimensional boundedness. Sharpness, a rank
improvement, the entire function a(rho), and the II_1-factor question remain
outside this result. The source's dimension-two and condition-dependent
results remain applicable.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive third-party coverage remain unverified.
The original Alhasan–Fawwaz article, Bikchentaev's cited full text, the relevant
inventory in Bhatia's Matrix Analysis, and complete citing-work enumerations
remain the literature boundaries recorded in owner #22774.
