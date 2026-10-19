---
slug: lin-2016-psi-map-properties
bibkey: lin2016psimap
doi: 10.48550/arXiv.1609.08231
url: https://arxiv.org/abs/1609.08231v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.psi
---

# Lin: both spectral properties of the map Ψ

## Problem

The fixed source is M. Lin, *New properties for certain positive
semidefinite matrices*, arXiv:1609.08231v1, §3, Example 3.6; the journal
version is *Linear Algebra and its Applications* 520 (2017), 32–43.
The setup states:

> we assume that [A X; X∗ B], where A, X, B are n × n, is positive semidefinite.

Definition 1.1(iii) states:

> M is said to have a-property if 2sj (M12 ) ≤ λj (M11 + M22 ), j = 1, . . . , n.

Definition 1.1(iv) states:

> M is said to have g-property if sj (M12 ) ≤ λj (M11 ♯ M22 ), j = 1, . . . , n.

Example 3.6 states:

> If we consider the map Ψ : X ↦ 2(trX)In − X, then using the approach in [14] we can show that the matrix [Ψ(A) Ψ(X); Ψ(X∗) Ψ(B)] is PPT. Though there are strong numerical evidence suggesting that this block matrix also has g-property, yet we have not even been able to show that it has a-property.

The concluding §5 states:

> Besides the challenging problems described in Example 3.5 and Example 3.6, …

For every natural n, complex n-by-n blocks A,X,B with
[A X; X* B] positive semidefinite, and every decreasing index j, prove
both inequalities

$$
2s_j(\Psi(X))\le\lambda_j(\Psi(A)+\Psi(B)),
\qquad
s_j(\Psi(X))\le\lambda_j(\Psi(A)\#\Psi(B)),
\quad \Psi(T)=2(\operatorname{tr}T)I-T.
$$

## Motivation

These are comparisons at each spectral index, with no commutation,
invertibility or rank assumption on the original blocks. The PPT property
alone does not give the matching-index comparisons. The statement uses
the same decreasing singular values, Hermitian eigenvalues and total
geometric mean as the trace-augmentation comparison.

## Gap

With both diagonal traces normalized to one, set t=|tr X| and
R(T)=(tr T)I−T. The decisive additional positive matrix is
[R(A) R(X*); R(X) R(B)]. Its Gram discrepancy is at most 2(1−t)I
after a unit phase makes tr X real. A general discrepancy estimate gives
an arithmetic spectral bound for this reduced block. This estimate must
retain the same t as the diagonal difference-square estimate.

## Route

For basis indices k<l put F_kl=e_k e_l*−e_l e_k*. Entrywise calculation
gives Σ F_kl T F_kl*=(tr T)I−Tᵀ. Apply the corresponding block-diagonal
congruences to the entrywise conjugate of the original positive block.
Their sum is the required positive reduction block.

For any positive block [P Y;Y* Q] whose discrepancy P+Q−Y−Y* is at
most δI, Gram factorization and Loewner eigenvalue monotonicity give
2s_j(Y)≤λ_j(P+Q)+δ/2. Applying this to the reduction block gives
2s_j(tI−X)≤λ_j(2I−A−B)+1−t. Scalar perturbation then gives
s_j(Ψ(X))≤λ_j(H)−(1−t)/2 for H=(Ψ(A)+Ψ(B))/2.

The existing normalized difference-square bound is
(A−B)²≤(1−t²)I. The existing geometric-mean comparison bounds
Ψ(A)#Ψ(B) below by H−(1−t²)I/4. The retained arithmetic deficit
absorbs this correction and gives the normalized g-property.

If either diagonal block is zero, positivity forces X=0. Otherwise a
block congruence normalizes both diagonal traces. Independent positive
homogeneity of the geometric mean restores the g-property for the
original blocks. The matrix arithmetic-geometric mean comparison then
implies the a-property for arbitrary traces; the arithmetic sum itself
is not homogeneous under independent scaling of its two summands.

## Falsifier

A positive semidefinite complex block matrix and an index violating
either displayed inequality would refute the conjunction. A failure of
the reduction-block identity or of the general discrepancy estimate would
invalidate this route without itself refuting the target.

## Evidence

The exact universal conjunction is
[`conjecture`](../D5/S3/Quantum/Matrix/LinPsiMap/Result.lean), and its
settlement theorem is `D5.S3.Quantum.Matrix.LinPsiMap.result` in the same
file. The new intermediate statements are
`reduction_block_posSemidef` and `gram_discrepancy_bound`.
The difference-square, scalar perturbation, phase rotation, block
normalization and geometric-mean estimates are reused from
`D5/S3/Quantum/Matrix/LinGProperty`.

## Triage

### What the settlement shows

**PROVED — both properties.**
`D5/S3/Quantum/Matrix/LinPsiMap/Result.result` states the a-property and
g-property together for every natural dimension, every positive
semidefinite complex block matrix and every decreasing index. Dimension
zero is vacuous, and zero diagonal blocks are included.

**PROVED — the new positivity input.**
`D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.reduction_block_posSemidef`
provides the positive reduction block without a commutation assumption.

**PROVED — the general discrepancy estimate.**
`D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy.gram_discrepancy_bound`
controls each singular value using the corresponding diagonal-sum
eigenvalue and one half of the discrepancy bound.

**OPEN — separate quantitative statement.** The normalized route gives
the margin (1−|tr X|)²/4 in the g-property. No separate public theorem
for that strengthened conclusion is asserted here.

**OPEN — equality classification.** A rank-one trace-one projection with
A=B=X gives equality in both properties. A complete equality
classification is not part of the settlement.

## ASSUMED-UNVERIFIED

The verbatim quotations, source locators and literature reading are
supplied information, not independently checked against original papers
under the offline constraint. Yang–Lu–Chen, *Filomat* 34 (2020), treats
Ψ₁(T)=(2n+1)(tr T)I−T. Alakhrass, arXiv:2305.10461 (2023), gives a
PPT-block geometric-mean estimate with index floor((j+1)/2), weaker than
the matching-index g-property. Rani–Kapil–Singh, *Advances in Operator
Theory* 8 (2023), is also included in the supplied reading. None settles
Example 3.6 within that reading. Citation indexes were not exhaustively
checked, and no literature-wide priority claim is certified. See the
[Library note](../Library/Eigenstructure/lin2016psimap.md).
