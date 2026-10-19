---
bibkey: lin2016psimap
authors: Minghua Lin
year: 2016
title: "New properties for certain positive semidefinite matrices"
doi: 10.48550/arXiv.1609.08231
url: https://arxiv.org/abs/1609.08231v1
claim: "Example 3.6 asks whether the map Ψ(T)=2(tr T)I−T gives the a-property and g-property for every positive semidefinite two-by-two block matrix."
strata_touched:
  - D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock
  - D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy
  - D5/S3/Quantum/Matrix/LinPsiMap/Result
license: citation-only
triage: anchor
---

# The reduction map and Lin's two spectral properties

## Locator

DOI: https://doi.org/10.48550/arXiv.1609.08231

The fixed source is Minghua Lin, *New properties for certain positive
semidefinite matrices*, [arXiv:1609.08231v1](https://arxiv.org/abs/1609.08231v1),
§3, Example 3.6, with the properties defined in Definition 1.1(iii)–(iv).
The journal version is *Linear Algebra and its Applications* 520 (2017),
32–43. The concluding §5 also identifies Example 3.6 as challenging.

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

## Mathematical scope

For every natural dimension n, complex n-by-n matrices A,X,B with
positive semidefinite block matrix [A X; X* B], and every decreasing
spectral index j, the two requested conclusions are

$$
2s_j(\Psi(X))\le\lambda_j(\Psi(A)+\Psi(B)),
\qquad
s_j(\Psi(X))\le\lambda_j(\Psi(A)\#\Psi(B)),
\quad \Psi(T)=2(\operatorname{tr}T)I-T.
$$

The geometric mean is the same total matrix definition used for trace
augmentation. It has the standard inverse-square-root formula on positive
definite inputs and vanishes when either input vanishes. Nonzero positive
diagonal blocks have strictly positive trace, and their images under Ψ
are positive definite. No commutation or rank assumption is imposed.

## Literature-check scope and result

The supplied literature reading covers the paper title and arXiv number
with Example 3.6, g-property, a-property and proof; the formulas
“2(trX)I − X” and “2tr(X)I − X” with singular-value inequalities; and the
reduction map with the matrix geometric mean and block matrices.

Yang–Lu–Chen, *Filomat* 34 (2020), treats the analogous map
Ψ₁(T)=(2n+1)(tr T)I−T, whose coefficient is larger than the coefficient
two here. Alakhrass, arXiv:2305.10461 (2023), obtains for PPT blocks an
index-halved geometric-mean bound: its right-hand index is
floor((j+1)/2), so it does not supply the matching-index g-property.
Rani–Kapil–Singh, *Advances in Operator Theory* 8 (2023), was also included
in the supplied reading. None of these readings supplies a settlement of
Example 3.6. Citation indexes were not exhaustively checked.

## Attribution boundary

The quotations, bibliographic metadata and concrete literature reading
are supplied source information, **ASSUMED-UNVERIFIED** against original
papers under the offline constraint. They do not certify literature-wide
priority. The reduction-block positivity identity, the general
Gram-discrepancy estimate and their application to the reflected spectrum
are the supplied mathematical route; no proof of Example 3.6 is attributed
to the named literature. This citation-only note incorporates no source
software.
