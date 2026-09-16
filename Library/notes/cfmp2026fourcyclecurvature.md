---
bibkey: cfmp2026fourcyclecurvature
year: 2026
title: Sources for CFMP four-cycle barriers and cover-uniform curvature estimates
license: citation-only
triage: anchor
strata_touched: []
---

# Source map for adjacent low-valence clusters and curvature observations

This is a source map for Sections 16–20 of the existing
`docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md`, not a claim that a new
paper with this title has been published.

## Primary mathematical inputs

Xinrong Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class
of Compact 3-Manifolds with Boundary*, arXiv:2601.15174v2, revised February 5,
2026. https://arxiv.org/html/2601.15174v2

Theorem 1.1 treats general minimum valence nine. Lemma 3.4 gives the adjacent
coordinate monotonicity used on the cosh-length cube; Lemma 2.2 supplies the
actual six-variable formula; Proposition 2.4 states the genuine length-domain
criterion. Section 2.2 records the co-volume gradient. These are existing
inputs, not results newly proved by the four-cycle incidence theorem.
The new restricted class has valence-eight edges and therefore is not covered
by Theorem 1.1 merely on the basis of its minimum valence.

Ke Feng, Huabin Ge and Bobo Hua, *Combinatorial Ricci flows and the
hyperbolization of a class of compact 3-manifolds*, Geometry & Topology 26
(2022), 1349–1384. DOI 10.2140/gt.2022.26.1349.
https://arxiv.org/abs/2009.03731
https://arxiv.org/pdf/2009.03731

Proposition 2.2 and the co-volume discussion supply smooth local convexity
and the positive-definite length Hessian. The existence-dependent flow
convergence result is not used to assume existence of the required metric.
The finite-dimensional spectral and strong-monotonicity consequences in
Section 18 are classical deductions from the actual geometric Hessian.

Feng Luo and Tian Yang, *Volume and rigidity of hyperbolic polyhedral
3-manifolds*, arXiv:1404.5365.
https://arxiv.org/abs/1404.5365
https://arxiv.org/pdf/1404.5365

The co-volume argument following equation (4.2) explicitly gives a positive-
definite Hessian in true hyper-ideal length space. The parsed text and printed
page 15 were inspected, including a successful screenshot of that page.
A screenshot attempt for the Feng–Ge–Hua page failed; no successful visual
inspection of that page is asserted. No unseen figure is a proof input.

## Exact restricted result and its boundary

Each tetrahedron has four degree-eight local edges forming a four-cycle and
two opposite edges of degree at least twelve. Shared global lengths and local
multiplicities are retained. The same box uses critical floor 5/4, critical
cap 2, and high cap 8/5 in cosh-length. Its decisive local cosines are
293/400, 1577/2236, and 37/43, with positive rational squared margins.
Both sides of the box are proved inward before applying the actual co-volume
minimum argument. No zero-curvature solution is assumed.

A fully specified six-tetrahedron manifold has degrees (12,8,8,8) and one
genus-three boundary. Its finite cyclic covers give unbounded examples.
The conditions allow each low edge two adjacent low edges, which the earlier
low-edge matching condition excluded. They do not allow arbitrary low-edge
clusters, all-eight tetrahedra, or unrestricted degrees nine through eleven.
No general minimum-eight or full CFMP resolution is asserted.

## Relation to the repository's observer and diagonal material

The actual `D5/S0/Diagonal/Lawvere/QualitativeEscape.lean` at dev
`c57bf72f087dae3bb5f5cc886c850649d7cb5593` concerns a fixed-point-free twist
and a listing's diagonal escaping its range. It does not prove a curvature
estimate, geometric compactness, or an identity about opposite tetrahedral
edges. Its hypothesis and carrier cannot be omitted when interpreting it.

`FORMAL_OBSERVER_COMPLETION_REFLECTION.md` explicitly distinguishes exact
observability from quantitative conditioning and retains complete mixed
responses. This informs the use of the full Hessian, rather than just its
diagonal entries. The uniformly controlled local Hessians give
`mu D <= -DK <= M D` on the specified common compact true-geometry region.
No numerical eigenvalue sample is treated as a proof of the uniform mu.

Section 19 constructs genuine cone metrics on connected covers for which
mean squared curvature tends to zero while a single moving edge has a fixed
nonzero defect. These metrics are not a single Ricci-flow trajectory. This
is a norm and changing-index-set phenomenon, not an instance of Lawvere's
listing theorem. It is consistent with the unnormalized weighted residual
bound and the cover-uniform contraction of the explicitly specified flow
`dot(l)=D^(-1)K(l)` inside the common region.

## Verification and remaining problem

Exact checks cover the three local substitutions, the three rational sign
margins, and the face-pairing/link/incidence conditions of the displayed
manifold. Sixteen actual global-box corners and one curvature root were
checked numerically; the root residual was about 4.44e-15. The displayed
finite-difference Hessian eigenvalues are diagnostics only. The all-cover
statements follow from the written proofs, not an enumeration of covers.

Bounded primary-source searches did not locate the precise four-cycle
incidence theorem. This is not an exhaustive priority certificate or an
independent referee assessment. The co-volume, compactness and matrix tools
are classical and credited above. The current delivery is ordinary proof:
no Lean elaboration, Scribe compilation, kernel admission, CI result or new
external open-conjecture resolution is claimed.

The general CFMP obligation remains to handle all permitted local low-valence
patterns and their shared variables, or to exclude flat tetrahedra in the
global maximizing angle structure. Small average error on larger objects
cannot replace genuine nondegenerate compactness and an undiluted residual
criterion on a fixed object.
