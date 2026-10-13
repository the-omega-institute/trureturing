---
bibkey: takahashietal2023su2sdp
authors: J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh
year: 2023
title: "An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut"
doi: 10.48550/arXiv.2307.15688
url: https://arxiv.org/abs/2307.15688v3
claim: "Appendix C.1 leaves first-level SDP exactness on the weighted-crown interval (n+2)^2/(4(n+1)) < x < (n+2)/3 open."
strata_touched:
  - D5/S3/Quantum/Optimization/WeightedCrownSpectralBound
  - D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate
  - D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2307.15688

Source: https://arxiv.org/abs/2307.15688v3

A Crossref title query and the arXiv metadata expose no separate journal-version DOI; the arXiv DOI is therefore the verified citation identifier.

# SU(2)-symmetric projector SDP for weighted crowns

Section III defines $\mathcal{Proj}(V,w)$ by maximizing
$\langle g|\sum_{jk}w_{jk}h_{jk}|g\rangle$ over Hermitian projections
$h_{ij}=h_{ji}$ and unit vectors $g$, with disjoint commutation and
$h_{ij}h_{jk}+h_{jk}h_{ij}=(h_{ij}+h_{jk}-h_{ik})/2$ for distinct vertices.
The $NPA_\ell$ hierarchy uses positive semidefinite moment matrices indexed
by words of length at most $\ell$, normalized at the identity and subject
to the truncated defining relations. Its real version is
$NPA^{\mathbb R}_\ell$. At level one the paper proves
$NPA_1(\mathcal{Proj}(V,w))=NPA^{\mathbb R}_1(\mathcal{Proj}(V,w))$.

Appendix C.1, printed p. 33, Eq. (C1), defines the weighted crown by

$$H=xh_{ab}+\sum_{j=1}^n(h_{aj}+h_{bj}).$$

It states verbatim:

> Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n ≥ 3.

The same page states verbatim:

> The intermediate region (n + 2)²/4(n + 1) < x < (n + 2)/3 is left as an open problem, although numerics strongly suggest that SDP indeed fails in that region.

Here $L=(n+2)^2/(4(n+1))$ and $U=(n+2)/3$. The source proves exactness for
$x\le L$ and $x\ge n$, and failure for $U<x<n$. Eq. (C2) states that the
true maximum eigenvalue is $n+1$ for $x\le1+n/2$ and $x+n/2$ for
$x\ge1+n/2$.

The formal carrier labels the two hubs by `none` and `some none`, and leaf
$i$ by `some (some i)` in `Option (Option (Fin n))`. Pairs are two-element
finite subsets; the identity moment is indexed by `none`. The real
level-one constraints are symmetry, positive semidefiniteness, identity
normalization, idempotent diagonals and the adjacent-pair anticommutator
relation. The qubit Hamiltonian uses the literal singlet expression
$(1-X_iX_j-Y_iY_j-Z_iZ_j)/4$, with $Y=iXZ$, and the maximum is encoded as
the supremum of nonzero-vector Rayleigh quotients.

The repository-derived certificate on $L<x<U$ has objective
$n+1+(x-L)^2/(32n)$. The operator certificate proves the upper bound
$\lambda_{\max}(H)\le n+1$ on the larger range $x\le1+n/2$. Together these
prove strict level-one inexactness on the open interval. The source's
exact eigenvalue equality is a literature result; the formal settlement
only needs the upper bound. Exact SDP values and endpoint behavior are
separate questions.
