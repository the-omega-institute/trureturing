---
bibkey: singerwu2011vectordiffusion
authors: Amit Singer; Hau-tieng Wu
year: 2011
title: Vector Diffusion Maps and the Connection Laplacian
doi: 10.48550/arXiv.1102.0075
url: https://arxiv.org/abs/1102.0075v1
claim: Section 3 constructs weighted orthogonal transport blocks and their degree matrix, with reverse-edge transpose symmetry, as a graph approximation associated with the connection Laplacian.
strata_touched: []
license: citation-only
triage: anchor
---

# Orthogonal edge transport and connection operators

The arXiv preprint §3, equations (3.1)–(3.3), defines the block matrix
`S(i,j)=w_ij O_ij` and scalar degree blocks `D(i,i)=deg(i)I`, and explains
symmetry from `O_ijᵀ=O_ji` and equal reverse weights. It then uses the
normalized averaging operator. Its manifold approximation involves local
PCA and aligned tangent frames with their own sampling hypotheses.

The FIB boundary geometry volume §19 uses the corresponding unnormalized
quadratic operator with explicitly supplied `SO(3)` transports. Labeled
parallel edges are summed separately. Its common-holonomy fixed-vector
calculation, repeated-walk frame-energy bound and edge-addition examples
are finite-network deductions, not a claim that FIB syntax supplies
aligned tangent frames or satisfies the paper's manifold limit assumptions.
The DOI above identifies the preprint rather than a journal version.
