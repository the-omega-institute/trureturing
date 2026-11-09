---
bibkey: zimmermannstoye2024stiefel
authors: Ralf Zimmermann and Jakob Stoye
year: 2024
title: 'High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities'
doi: 10.1137/24M1655755
url: https://arxiv.org/abs/2403.01879v3
claim: 'For n ≥ 4 and (n,p)=(n,n−1), sharp Euclidean Stiefel sectional-curvature bounds are −1/2 ≤ K_e^St(X,Y) ≤ 1/2.'
strata_touched:
  - D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature
license: citation-only
triage: anchor
---

# High curvature means low-rank

Ralf Zimmermann and Jakob Stoye, *SIAM Journal on Matrix Analysis and Applications* 46(1), 748–779 (2025). The Lean statement follows Conjecture 1 on arXiv version 3, PDF page 17, and equation (26).

## Verified locator

DOI: https://doi.org/10.1137/24M1655755

Source: https://arxiv.org/abs/2403.01879v3

## Claim and conventions

The source states verbatim: “For $n\geq 4$ and $(n,p)=(n,n-1)$, sharp bounds on the sectional curvature of the Stiefel manifold under the Euclidean metric are $-\frac12\leq K^{St}_e(X,Y)\leq\frac12$.” The formalization uses the source's block coordinates at the identity base point, the ambient Frobenius metric without a factor $1/2$, and the displayed curvature expression in equation (26). The source's orthogonal base-point identification is recorded as the geometric bridge.

“The Stiefel manifold is $St(n,p) = \{U\in\mathbb R^{n\times p}\mid U^TU=I_p\}$.” (Notational specifics, PDF page 2.)

“The matrices $X,Y$ form a (Riemannian) ONB if and only if $1 = \|A_i\|_F^2 + \|B_i\|_F^2$, $i=1,2$, $0 = \operatorname{tr}(A_1^TA_2) + \operatorname{tr}(B_1^TB_2)$.” (Section 3.3, PDF page 15.) The tangent representation also requires $A_i^T=-A_i$.
