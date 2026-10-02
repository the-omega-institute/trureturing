---
bibkey: cfmp2026cycledegree9nonnormalindex72
authors: trureturing contributors
year: 2026
title: Nonnormal index-72 PSL2(F71) cover for pure degree-(8,9) cycle packets
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/12065
claim: An explicit torsion-free nonnormal index-72 subgroup of the [4,9,3] orientation Coxeter group yields N=24 in the six-sector degree-(8,9) construction.
license: citation-only
triage: anchor
strata_touched: []
---

Define x=ab, y=bc, z=cd in the [4,9,3] orientation subgroup. The matrices
X=[[2,7],[23,10]], Y=[[0,70],[1,30]], Z=[[47,66],[35,25]] over F71 satisfy all orientation relators projectively in PSL2(F71): X^4=Y^9=Z^3=(XY)^2=(YZ)^2=(XYZ)^2=1. The action on P1(F71) is transitive on 72 points. The images of the three finite orientation parabolics are D8, S3, and C9, and their nonidentity elements act freely on P1(F71); hence the point stabilizer Gamma is torsion-free. It is nonnormal and has index 72. Since K=<c,d> has order 6, the six-sector coarsening has N=2*72/6=24 target tetrahedra.

The deterministic verifier docs/develop/theory/verify_cycle9_psl71.py checks the matrix identities, subgroup orders, transitivity, and cycle structures. This resolves the nonnormal Coxeter-cover route at N=24, while arbitrary non-Coxeter pseudo-simplicial pairings remain outside scope.
