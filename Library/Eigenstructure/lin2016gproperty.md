---
bibkey: lin2016gproperty
authors: Minghua Lin
year: 2016
title: "A singular value inequality related to a linear map"
doi: 10.13001/1081-3810.3108
url: https://arxiv.org/abs/1609.08231
claim: "Conjecture 3.1 asks whether trace augmentation gives the g-property for every positive semidefinite two-by-two block matrix."
strata_touched:
  - D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound
  - D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound
  - D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound
  - D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation
license: citation-only
triage: anchor
---

# Trace augmentation and the geometric-mean singular-value inequality

## Locator

The original question is Conjecture 3.1, printed page 124, in
*Electronic Journal of Linear Algebra* 31 (2016), 120–124,
DOI [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108).
The fixed restatement is *New properties for certain positive semidefinite
matrices*, [arXiv:1609.08231v1](https://arxiv.org/abs/1609.08231v1),
§3, Example 3.5; its g-property is Definition 1.1(iv).
The restatement appeared in *Linear Algebra and its Applications* 520
(2017), 32–43.

The supplied text of Definition 1.1(iv) is:

> M is said to have g-property if sj (M12 ) ≤ λj (M11 ♯ M22 ), j = 1, . . . , n.

The supplied text of Example 3.5 is:

> [Φ(A) Φ(X); Φ(X∗) Φ(B)] where Φ : X ↦ X+(trX)In , is PPT … Numerical experiments suggest that the matrix [Φ(A) Φ(X); Φ(X∗) Φ(B)] has g-property, which we haven't been able to prove yet.

The setup states:

> we assume that [A X; X∗ B], where A, X, B are n × n, is positive semidefinite.

## Mathematical scope

For every dimension and every complex positive semidefinite block matrix
$[A\ X;X^*\ B]$, the question is whether

$$
s_j\bigl(X+(\operatorname{Tr}X)I\bigr)
\le\lambda_j\bigl((A+(\operatorname{Tr}A)I)\#
                         (B+(\operatorname{Tr}B)I)\bigr)
$$

holds at every index in decreasing order. On positive definite inputs,
$P\#Q=P^{1/2}(P^{-1/2}QP^{-1/2})^{1/2}P^{1/2}$.
Zero diagonal blocks force the off-diagonal block to vanish.

## Literature-check scope and result

The supplied preregistration records searches of the title and DOI with
conjecture/proof/solved; “g-property” with “X + tr(X) I”; and “Lin's
conjecture” geometric mean singular value, 2024–2026. The named references
checked were Yang–Lu–Chen, *Operators and Matrices* 14 (2020), for dimension
two; Abbas–Ghabries, *Linear and Multilinear Algebra* 70 (2022), for
$AX=XA$; Fu–Lau–Tam, *Mathematical Inequalities & Applications* 23 (2020),
for $\Phi_c$ with $c\ge(n+3)/2$; Rani–Kapil–Singh, *Advances in Operator
Theory* 8 (2023), which restates the problem as Conjecture 1.1; and a
*Filomat* 34 (2020) restatement.

No settlement was found within that scope. Citation indexes were not
exhaustively checked. This is the preregistration's concrete reading,
not an independent exhaustive literature certification.

## Attribution boundary

The quotations, bibliographic metadata and literature-check reading are
supplied source information, **ASSUMED-UNVERIFIED** against original papers
under the offline constraint. The trace-corrected arithmetic bound, the
trace-overlap difference estimate and the quantitative harmonic comparison
are the supplied proof route; no proof of the general conjecture is
attributed to the cited literature. This citation-only note incorporates
no source software.
