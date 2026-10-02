---
bibkey: cfmp2026cycledegree9finitequotient
authors: trureturing contributors
year: 2026
title: Explicit finite Coxeter quotient for pure three-cycle packets of degree (8,9)
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/12077
claim: The mod-17 Coxeter-sector quotient has orientation image Omega+_4(17) of order 11,985,408 and yields an explicit degree-(8,9) packet triangulation with N=3,995,136 target tetrahedra.
license: citation-only
triage: anchor
strata_touched: []
---

The finite-index step in the degree-(8,9) Coxeter-sector construction can be made effective. For the [4,9,3] sector group W, specialize the canonical reflection representation at 2 cos(pi/4) -> 6, 2 cos(pi/9) -> 3, and 2 cos(pi/3) = 1 modulo 17.

The matrices preserve the plus-type Gram form
[[1,14,0,0],[14,1,7,0],[0,7,1,8],[0,0,8,1]], with determinant 13 = 8^2 modulo 17. Each reflection has determinant -1 and square spinor norm, so the orientation subgroup maps into Omega+_4(17). The deterministic exhaustive checker verify_cycle9_coxeter_order.cpp enumerates the six products R_iR_j and returns exactly ORDER 11985408, equal to |Omega+_4(17)| = 17^2 (17^2-1)^2/2.

The kernel Gamma=ker(rho|W+) is torsion-free: the local checker proves faithful images of all maximal finite special parabolics (orders 16, 12 and 18), and finite-order Coxeter elements are conjugate into finite standard parabolics. With K=<c,d> of order six, the coarsened target-tetrahedron count is N = [W:Gamma]/|K| = 2*11,985,408/6 = 3,995,136.

This is an explicit finite witness and an existence upper bound for the construction. It does not claim minimality and does not obstruct N=24 for other finite-index subgroups or pairings. The prior topological count 24 divides N remains the only stated general lower divisibility condition.
