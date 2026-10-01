---
bibkey: cfmp2026cycledegree9
authors: trureturing contributors
year: 2026
title: Pure three-cycle packets with degree-eight low edges and degree-nine high edges
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/new
claim: A paper-first strict hyper-ideal realization theorem for role-homogeneous pure three-cycle packets with low global degree 8 and high global degree 9, under the stated manifold and incidence hypotheses.
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
Theorems 1.4 and 6.3, supply the shared-edge co-volume derivative and
interior-minimum mechanism; together they produce an interior zero-curvature point. This is conditional on
a valid finite connected orientable ideal triangulation with the packet roles;
no explicit face pairing or non-vacuity witness is claimed. It does not
resolve arbitrary minimum-eight or minimum-six CFMP, and no Lean
formalization is asserted.

Primary references:
- Costantino--Frigerio--Martelli--Petronio, Conjecture 0.8:
  https://arxiv.org/abs/math/0402339
- Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174:
  https://arxiv.org/html/2601.15174v2
- Luo--Yang, *Volume and rigidity of hyperbolic polyhedral 3-manifolds*:
  https://arxiv.org/abs/1404.5365
