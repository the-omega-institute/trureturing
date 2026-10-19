---
slug: lin-2016-trace-augmentation-g-property
bibkey: lin2016gproperty
doi: 10.13001/1081-3810.3108
url: https://arxiv.org/abs/1609.08231
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi
---

# Lin: the g-property of trace augmentation

## Problem

The original locator is Conjecture 3.1, printed page 124, of the paper
identified by DOI 10.13001/1081-3810.3108. The fixed restatement is
arXiv:1609.08231v1, §3, Example 3.5. Its setup states:

> we assume that [A X; X∗ B], where A, X, B are n × n, is positive semidefinite.

Definition 1.1(iv) states:

> M is said to have g-property if sj (M12 ) ≤ λj (M11 ♯ M22 ), j = 1, . . . , n.

Example 3.5 states:

> [Φ(A) Φ(X); Φ(X∗) Φ(B)] where Φ : X ↦ X+(trX)In , is PPT … Numerical experiments suggest that the matrix [Φ(A) Φ(X); Φ(X∗) Φ(B)] has g-property, which we haven't been able to prove yet.

The concluding §5 refers to:

> Besides the challenging problems described in Example 3.5 and Example 3.6, …

For every natural dimension, all complex matrices A, X, B with positive
semidefinite block matrix W=[A X; X* B], and every decreasing index j,
the target is

$$
s_j(\Phi(X))\le\lambda_j(\Phi(A)\#\Phi(B)),
\qquad \Phi(T)=T+(\operatorname{Tr}T)I.
$$

## Motivation

The target is preregistered in
[issue #19078](https://github.com/the-omega-institute/trureturing/issues/19078).
It asks for each individual singular value, beyond a bound on only the
largest singular value or on a sum. Neither commutation nor full rank is
assumed. The parameter family replaces Φ by
Φ_c(T)=T+c(Tr T)I for real c≥1.

## Gap

Normalize the two positive diagonal traces separately. For trace-one
diagonal blocks set t=|Tr X|. The needed arithmetic estimate retains the
trace defect:

$$
2s_j(X)\le\lambda_j(A+B)+1-t.
$$

The complementary estimate controls the whole matrix difference:

$$
(A-B)^2\le(1-t^2)I.
$$

Both estimates retain the same block matrix and the same t. Their
combination supplies the scalar slack needed to pass from the arithmetic
mean to the geometric mean.

## Route

Gram factorization W=ZZ* with row blocks U,V gives A=UU*, B=VV*, X=UV*.
The Hermitian dilation of X and Loewner eigenvalue monotonicity compare
2s_j(X) with the spectrum of Z*Z. Splitting that Gram matrix into the
sum and difference of U,V bounds the difference part by its trace,
giving the trace-corrected arithmetic estimate. A phase rotation makes
Tr X real without changing the singular values.

For a unit vector, the two outcomes given by its rank-one projection and
the complementary projection bound t by the corresponding classical
overlap. The two-outcome overlap inequality then bounds the squared
quadratic form of A-B. Apply it in an eigenbasis to obtain the matrix
square estimate.

For P,Q positive definite, put H=(P+Q)/2 and K=(P-Q)/2. The harmonic
mean lies below the geometric mean and equals H-KH⁻¹K. If H≥cI and
K²≤dI, inverse order and congruence give P#Q≥H-(d/c)I.
Use P=cI+A, Q=cI+B, d=(1-t²)/4. The scalar perturbation bound
s_j(X+zI)≤s_j(X)+|z| and c≥1 complete the comparison.

Positive diagonal traces permit normalization by block congruence;
homogeneity restores the original matrices. A zero diagonal block forces
X=0. The geometric mean defined here vanishes when either input vanishes,
so the degenerate case is included explicitly.

## Falsifier

A positive semidefinite block matrix and an index violating the displayed
comparison would refute the conjecture. A failure of either normalized
intermediate estimate would invalidate this route without itself refuting
the conjecture.

## Evidence

The exact universal statement and its settlement theorem are
[`conjecture` and `result`](../D5/S3/Quantum/Matrix/LinGProperty/Result.lean),
in Lean namespace `D5.S3.Quantum.Matrix.LinGProperty`.
The theorem `parameter_family` covers every real c≥1.
The live intermediate propositions are `normalized_arithmetic_bound`,
`normalized_difference_square_le`, `arithmetic_sub_le_geometricMean`,
and `singularValuesSorted_add_scalar`. The geometric-mean Riccati
identity identifies the definition with the standard positive definite
matrix geometric mean.

## Triage

### What the settlement shows

**PROVED — settlement.** `D5/S3/Quantum/Matrix/LinGProperty/Result.result`
is the trace-augmentation comparison for every positive semidefinite
complex block matrix and every decreasing index, including zero blocks.

**PROVED — parameter family.**
`D5/S3/Quantum/Matrix/LinGProperty/Result.parameter_family` gives the
same comparison for every real c≥1. Its normalization and zero-block
branches impose no commutation or invertibility condition on A or B.

**PROVED — decisive estimates.**
`D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.normalized_arithmetic_bound`
retains the defect 1−|Tr X|. Together with
`D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_difference_square_le`,
it controls the loss in replacing the arithmetic mean by the geometric
mean, rather than requiring equality of the diagonal blocks.

**OPEN — quantitative margin.** The supplied route proposes the stronger
unnormalized margin (k−|Tr X|)²/(4k), where
k=√(Tr A Tr B)>0. That stronger statement is not part of the Lean
settlement theorem here.

**OPEN — the other map.** Example 3.6 concerns
Ψ(X)=2(Tr X)I−X. This comparison for trace augmentation supplies no
settlement of that separate question.

**OPEN — equality.** The proof supplies sufficient estimates; a complete
characterization of equality and of optimal parameter thresholds below
c=1 is not asserted.

## ASSUMED-UNVERIFIED

The verbatim quotations, source locators and literature reading are supplied
preregistration information, not independently checked against original
papers under the offline constraint. The scope includes Yang–Lu–Chen
(dimension two), Abbas–Ghabries (AX=XA), Fu–Lau–Tam
(c≥(n+3)/2), Rani–Kapil–Singh (Conjecture 1.1), and the Filomat
restatement. No settlement was found within that scope; citation indexes
were not exhaustively checked. This does not certify a literature-wide
priority claim. See the
[Library note](../Library/Eigenstructure/lin2016gproperty.md).
