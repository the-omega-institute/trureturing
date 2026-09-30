# CFMP provenance after Uemura (2026)

## Purpose

This note records a literature update without rewriting the historical
CFMP results.  Soichiro Uemura, *Local combinatorial criteria for geometric
hyper-ideal triangulations via combinatorial Ricci flow*, arXiv:2609.34108v1
(28 September 2026), proves a valence-dependent invariant-box criterion.
The relevant primary statements are Theorem 4.2 (the classical parameter
(C=2)) and Theorem 5.5 / Corollary 5.9 (the parameterized boxes).

Uemura's criterion uses
[
 gamma_n=rac{6}{2+cos(2pi/n)}-1,qquad
 b_n=2 (6le nle9),qquad
 b_n=1+rac{8(1-cos(2pi/n))}{1+cos(2pi/n)} (nge10),
]
and the canonical box ([gamma_{v(e)},b_{v(e)}]).  Only edges of
valence 6--9 require an angle-sum check; valence at least 10 is controlled
by the invariant-box argument.

## Exact scope comparison

The abstract barrier/co-volume mechanism is related to the proof in
CFMP_EIGHT_TRIANGLE_CLUSTERS.md and CFMP_DEGREE10_STAR.md, but the
canonical Uemura box is a different box.  In particular, it must not be
silently substituted for the narrower heterogeneous boxes in those files.

The generic three-edge theorem with degree-eight lows and arbitrary
high degrees at least 12 is not a direct corollary of Uemura Theorem 4.2.
For the homogeneous three-star endpoint with adjacent high valences 12 and
opposite valence 12, its canonical endpoint has
[
 arphi(2,2,2,gamma_{12},b_{12},b_{12})>1/sqrt2,
]
so the corresponding single angle is less than (pi/4).  Thus the
generic theorem's incidence estimate remains an independent certificate.

## The explicit degree-ten witness

The 16-tetrahedron witness in CFMP_DEGREE10_STAR.md has edge degrees
([8,8,8,8,8,8,10,38]).  The exact topology and the heterogeneous
box
[
 [11/8,2]_{d=8},quad [11/10,71/50]_{d=10},quad
 [1009/1000,21/20]_{d=38}
]
remain independent computed certificates.

Its geometric-existence conclusion is, however, also covered by Uemura
Theorem 4.2 after checking the actual occurrence data in Uemura's canonical
box.  For a degree-eight target, the possible adjacent-high/opposite
patterns reduce to
[
 (10,10;38), (10,38;38), (10,38;10), (38,38;38), (38,38;10).
]
Using the exact endpoint formula
[
 arphi(2,b_{n_2},b_{n_3},gamma_m,b_{n_5},b_{n_6}),
]
rational Taylor enclosures from (333/106<pi<355/113) give the following
strict lower-angle bounds (the labels are the five patterns above):
[
 28pi/125,quad31pi/125,quad32pi/125,quad7pi/25,quad29pi/100.
]
The six degree-eight edge stars in the explicit pairing have weighted sums
of these bounds
[
 rac{1037}{500}pi,quadrac{258}{125}pi,quad
 rac{1097}{500}pi,quadrac{213}{100}pi,quad
 rac{1093}{500}pi,quadrac{113}{50}pi,
]
all strictly greater than (2pi).  Theorem 4.2 then controls the degree-ten
and degree-38 edges automatically.  This is a finite corollary check of
Uemura's criterion, not a claim that the heterogeneous box itself appears
in Uemura.

Accordingly, the explicit degree-ten theorem should be cited for its exact
heterogeneous endpoint certificate and explicit topology, while its bare
geometric-existence conclusion should be recorded as independently
re-verified by Uemura's later criterion.  No historical theorem statement is
changed and no priority claim is made against arXiv:2609.34108.

## Primary source

- Uemura, arXiv:2609.34108v1, HTML: https://arxiv.org/html/2609.34108v1
  (Theorem 4.2, Theorem 5.5, Corollary 5.9).
