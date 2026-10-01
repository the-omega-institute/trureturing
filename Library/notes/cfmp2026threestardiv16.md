---
bibkey: cfmp2026threestardiv16
authors: trureturing contributors
year: 2026
title: Pure three-star role-homogeneous 16-divisibility obstruction
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/11620
claim: In a role-homogeneous orientable pure three-star packet with all low quotient edges degree 8, every center-link component contains a multiple of 16 tetrahedra.
license: citation-only
triage: anchor
strata_touched: []
---

The proof is in docs/develop/theory/CFMP_THREESTAR_DIV16.md.

This is a topological necessary condition, not a geometric realization
theorem. It assumes face pairings preserve the local low/high role, which is
automatic when low edges have degree 8 and high edges have degree at least 10.
If a lowered-threshold construction allows a degree-8 quotient class to occur
in both local roles, the center/peripheral separation need not hold and this
obstruction does not apply.

For high classes of degrees 8 and 14 with counts a,b, the tetrahedron count
N=16k implies 4a+7b=24k. A role-homogeneous inventory with one high-8 class
therefore starts at N=96, b=20.