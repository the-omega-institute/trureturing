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

Abed, Nikolaeva and Novikov, *How characterisations of traces and central elements fail*,
arXiv:2610.34388v1, Section 11.2(5), ask:

> Is a bounded on M_n(C) independently of rho?

The selected question fixes a positive dimension and varies every strictly positive
density. Section 5.12 defines the quotient set using positive semidefinite A,
Hermitian B and nonzero X=A+iB. Section 3.1 uses the ordinary trace and
modulus |X|=(X*X)^(1/2), without a trace-one requirement.

## Result and scope

The Lean definition `claim` is exactly

$$
\forall n\ge1\;\exists C\in\mathbb R,\quad C\ge0\quad\text{and}\quad
\forall\rho>0,\quad S_\rho\ne\varnothing,\quad
\operatorname{IsLUB}(S_\rho,\sup S_\rho),\quad \sup S_\rho\le C.
$$

where S is the source's actual quotient set. The theorem `result : claim`
uses C=n. The genuine nonempty least-upper-bound conclusion prevents the
totalized real supremum from certifying an empty or unbounded set.

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

## Admission and boundaries

The preregistration is [owner #22774](https://github.com/the-omega-institute/trureturing/issues/22774).
The independently approved ordinary argument is its
[complete-proof comment](https://github.com/the-omega-institute/trureturing/issues/22774#issuecomment-6606601813).
Admission basis: `open-problem-resolution`. Reused spectral, functional-calculus,
trace and Cauchy–Schwarz results are not claimed as new mathematics. Every
auxiliary declaration has a live consumer in the complete boundedness proof.

This implementation does not establish sharpness, a rank improvement, the
entire function a(rho), or the II_1-factor question. The source's dimension-two
and condition-dependent results remain applicable. The implementation is
prepared for independent formal review; no frozen membership is asserted here.

Worldwide priority and exhaustive third-party coverage remain unverified.
The original Alhasan–Fawwaz article, Bikchentaev's cited full text, the relevant
inventory in Bhatia's Matrix Analysis, and complete citing-work enumerations
remain the literature boundaries recorded in owner #22774.
