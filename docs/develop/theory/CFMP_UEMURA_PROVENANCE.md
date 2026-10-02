# CFMP provenance after Uemura (2026)

## Purpose

This note records a literature update without rewriting the historical
CFMP results. Soichiro Uemura, “Local combinatorial criteria for geometric
hyper-ideal triangulations via combinatorial Ricci flow,” arXiv:2609.34108v1
(28 September 2026), proves a valence-dependent invariant-box criterion.
The relevant primary statements are Theorem 4.2 (the classical parameter
C=2) and Theorem 5.5 / Corollary 5.9 (the parameterized boxes).

Uemura's C=2 criterion uses

  gamma_n = 6/(2+cos(2*pi/n)) - 1,
  b_n = 2 for 6 <= n <= 9,
  b_n = 1 + 8*(1-cos(2*pi/n))/(1+cos(2*pi/n)) for n >= 10,

with canonical box [gamma_v, b_v] on an edge of valence v. Only edges of
valence 6--9 require an angle-sum check; valence at least 10 is controlled
by the invariant-box argument.

## Exact scope comparison

The abstract barrier/co-volume mechanism is related to the proof in
CFMP_EIGHT_TRIANGLE_CLUSTERS.md and CFMP_DEGREE10_STAR.md, but the
canonical Uemura box is a different box. It must not be silently substituted
for the narrower heterogeneous boxes in those files.

The generic three-edge theorem with degree-eight lows and arbitrary high
degrees at least 12 is not a direct corollary of Uemura Theorem 4.2. For the
homogeneous three-star endpoint with adjacent high valences 12 and opposite
valence 12, the C=2 canonical endpoint

  phi(2,2,2,gamma_12,b_12,b_12)

is strictly greater than 1/sqrt(2), so the corresponding single angle is
strictly less than pi/4. Thus the generic theorem's incidence estimate
remains an independent certificate.

## The explicit degree-ten witness

The 16-tetrahedron witness in CFMP_DEGREE10_STAR.md has edge degrees
[8,8,8,8,8,8,10,38]. Its exact topology and heterogeneous box

  [11/8, 2] on degree 8,
  [11/10, 71/50] on degree 10,
  [1009/1000, 21/20] on degree 38

remain independent computed certificates.

Its geometric-existence conclusion is also covered by Uemura Theorem 4.2
after checking the actual occurrence data in Uemura's canonical box. For a
degree-eight target, the possible adjacent-high/opposite patterns reduce to

  (10,10;38), (10,38;38), (10,38;10), (38,38;38), (38,38;10).

Using the exact endpoint expression

  phi(2,b_n2,b_n3,gamma_m,b_n5,b_n6),

rational Taylor enclosures from 333/106 < pi < 355/113 give strict
lower-angle bounds (in the order of those five patterns)

  28*pi/125, 31*pi/125, 32*pi/125, 7*pi/25, 29*pi/100.

The six degree-eight edge stars in the explicit pairing have weighted sums
of these bounds

  (1037/500)*pi, (258/125)*pi, (1097/500)*pi,
  (213/100)*pi, (1093/500)*pi, (113/50)*pi,

all strictly greater than 2*pi. Theorem 4.2 then controls the degree-ten
and degree-38 edges automatically. This is a finite corollary check of
Uemura's criterion, not a claim that the heterogeneous box itself appears
in Uemura.

Accordingly, cite the explicit degree-ten theorem for its exact
heterogeneous endpoint certificate and explicit topology, while recording
its bare geometric-existence conclusion as independently re-verified by
Uemura's later criterion. No historical theorem statement is changed and no
priority claim is made against arXiv:2609.34108.

## Primary source

- Uemura, arXiv:2609.34108v1:
  https://arxiv.org/html/2609.34108v1
  (Theorem 4.2, Theorem 5.5, Corollary 5.9).
