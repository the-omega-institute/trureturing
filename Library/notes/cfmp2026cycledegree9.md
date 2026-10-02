---
bibkey: cfmp2026cycledegree9
authors: trureturing contributors
year: 2026
title: Pure three-cycle packets with degree-eight low edges and degree-nine high edges
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/11934
claim: A paper-first strict hyper-ideal realization theorem for role-homogeneous pure three-cycle degree-(8,9) packets, together with finite-index Coxeter-sector non-vacuity.
license: citation-only
triage: anchor
strata_touched: []
---

The theorem and exact rational endpoint audit are in
`docs/develop/theory/CFMP_CYCLE_DEGREE9.md` and
`docs/develop/theory/verify_cycle9_box.py`.

The shared cosh-length box is `[73/50,2]` on low edges and
`[53/40,347/200]` on high edges. Zhao's six-variable cosine monotonicity
reduces all lower/upper faces to four endpoint tuples. Exact squared cosines
are on the strict sides of `1/2` for degree eight and of
`cos(2*pi/9)^2` for degree nine; the latter is bracketed by the cubic
`8q^3-6q+1=0`.

Uemura, arXiv:2609.34108v1, Theorem 3.2 supplies the abstract invariant-box
criterion; the packet-specific endpoint arithmetic below is separate. Zhao's Lemma 3.4 supplies monotonicity. Luo--Yang, arXiv:1404.5365v2,
Section 4.3, Corollary 4.12 and Section 5 formula (5.1), supply the
co-volume differential; the displayed compact-box minimum argument yields
an interior zero-curvature point. The analytic theorem assumes
a valid finite connected orientable ideal triangulation with the packet roles;
the Coxeter-sector construction below proves existence at some finite count,
without an explicit minimal pairing or an N=24 claim. It does not
resolve arbitrary minimum-eight or minimum-six CFMP, and no Lean
formalization is asserted.

Primary references:
- Costantino--Frigerio--Martelli--Petronio, Conjecture 0.8:
  https://arxiv.org/abs/math/0402339
- Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174:
  https://arxiv.org/html/2601.15174v2
- Luo--Yang, *Volume and rigidity of hyperbolic polyhedral 3-manifolds*:
  https://arxiv.org/html/1404.5365v2#S4.SS3
- Uemura, abstract invariant-box criterion, Theorem 3.2:
  https://arxiv.org/html/2609.34108v1


## Non-vacuity provenance

Construction: https://github.com/the-omega-institute/trureturing/pull/12065

A finite non-vacuity witness is now supplied by a six-sector Coxeter quotient, not by an N=24 pairing. Start with the unique symmetric hyper-ideal tetrahedron with low angle pi/4 and high angle 2*pi/9. Its S3 sector is the [4,9,3] doubly-truncated Coxeter orthoscheme Q. The finite K=<c,d> sector group has order 6; KQ is exactly one target tetrahedron: A facets orbit as 1 base hexagon, B facets as 3 side hexagons, U truncations as 3 peripheral triangles, and V truncations as 1 center triangle. In the Coxeter development, <a,b> has 8 sectors around a generic low edge with trivial K stabilizer, while <b,c> has 18 sectors around a high edge and K stabilizer <c> of order 2, giving target degrees 8 and 9. A torsion-free finite-index subgroup of the orientation-preserving parabolic subgroup gives a compact orientable quotient with geodesic boundary; collapsing boundary components yields a topological ideal triangulation. The local exact audit is docs/develop/theory/verify_cycle9_coxeter_local.py; it checks the [4,9,3] relations, maximal finite parabolics, K intersections, and all angle sums over F_17/rational arithmetic.

Primary sources for this non-vacuity addition: Luo--Yang, arXiv:1404.5365v2, Proposition 4.1 and Proposition 4.4; Marshall, J. Austral. Math. Soc. 64 (1998), pp. 58--60 and 69--70; Felikson--Tumarkin, arXiv:math/0604248v3, introduction.
