---
slug: kraus-simanek-2024-polynomial-content-no-maximizer
bibkey: kraussimanek2024polynomialcontent
doi: 10.1007/s10659-024-10087-4
url: https://arxiv.org/abs/2309.16450
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result
---

# Polynomial content has no maximizer on suitable unit-area polygons

## Problem

A. Kraus and B. Simanek, *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*, arXiv:2309.16450v1, Conjecture 2.1, p. 3:

> For each N ∈ ℕ, there is an n ∈ ℕ so that among all n-gons with area 1, ρ_N has no maximizer.

The source characterizes $\rho_N(\Omega)$ as the squared distance from $\bar z$ to complex polynomials of degree at most $N$ in $L^2(\Omega,dA)$. The settlement is **Proved** by `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result`, with preregistration [#16916](https://github.com/the-omega-institute/trureturing/issues/16916).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| For each $N\in\mathbb N$ | `claim` quantifies over all natural degrees, including zero | Covers the source domain and zero. |
| There is a polygon side count | The existential index in `claim` represents index plus three sides | Every polygon has at least three sides; the constructed count is $2\max(3,N+2)$. |
| A simple polygonal Jordan region | `IsSimplePolygon` requires nonadjacent edge disjointness, adjacent-edge intersection exactly at the shared vertex, and consecutive noncollinearity; `IsPolygonRegion` requires a bounded connected open region with frontier equal to Mathlib’s `Polygon.boundary ℝ` of those vertices | The closed path $v_0\to v_1\to\cdots\to v_{n+2}\to v_0$ is the union of `Polygon.edgeSet ℝ`, identified with vector-space segments by `affineSegment_eq_segment` and `finRotate_apply`. |
| Area one | `volume` of the region equals one | Complex planar Lebesgue measure. |
| Polynomial content | `rhoN` is the infimum of the squared integral errors over `Polynomial.degreeLE` | The source's squared-distance expression. |
| Has no maximizer | `claim` negates the existence of an admissible polygon dominating all other admissible polygons | No additional assumption on the competing polygon. |

## Motivation

The source proves the hexagon cases $N=1,2$ in Theorem 2.2. An all-degree result requires a polygon family whose symmetry cancels every polynomial correction of the specified degree while its second moment grows without bound.

## Gap

Boundedness of each individual polygon does not give a uniform upper bound over all unit-area polygons of a fixed side count. The geometric obligations are simplicity, a nonempty connected interior, exact polygonal frontier and unit area; rotational cancellation alone does not establish those obligations.

## Route

For $m=\max(3,N+2)$, put $\theta=\pi/m$ and $r=1/(mR\sin\theta)$. Alternate outer vertices $R e^{2\pi i j/m}$ and inner vertices $r e^{i\theta}e^{2\pi i j/m}$. For sufficiently large positive $R$, the consecutive vertices define a simple $2m$-gon. Its $2m$ fan triangles have total area $mRr\sin\theta=1$.

`PlanarFanPolynomialApproximation.polar_fan_conic_coverage` supplies directional coverage; `adjacent_triangles_spoke_interior` and `finite_cyclic_fan_frontier` identify the interior and frontier. The settling module's private `starRegion_positive_inradius`, `starVertex_isSimplePolygon`, `starRegion_frontier` and `starRegion_unitArea` verify the region. Its private `starRegion_moments` and `rhoN_starRegion` establish rotational cancellation and optimality of the zero polynomial. Its private `starRegion_secondMoment_lower_bound` gives $R^2/(32m)$ as a lower bound, and `starRegion_rhoN_unbounded` gives unboundedness. These are proof constituents of the public `result`, not additional public statements.

## Falsifier

A counterexample to the conjecture would be a degree for which every side count has a maximizing unit-area polygon. The constructed unbounded family for that degree rules it out. The proof additionally checks that the admissible family is nonempty; empty-domain non-attainment is not the mechanism.

## Evidence

The Lean sources are `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.lean` and `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.lean`. Each has a Blueprint Scribe. The reused angle owner is `D5/S3/Geometry/Gluing/CyclicTriangleDisk.positive_circle_angle`.

The four-slot escape audit remains unfinished for all new public theorems and the published angle owner: [#17590](https://github.com/the-omega-institute/trureturing/issues/17590). No `declared_validated` registration is asserted by this dossier.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0e6a55853bd4544e0f5aad2c9e18dbd4f72e1b07/docs/reports/kraus-simanek-2024-polynomial-content-no-maximizer). In that directory, `python3 check.py` exits 0 and reports `ALL_OK`; `check.py` SHA-256 is `d68acfc7e49a03664d0116ea6ffd10ba93cb4a398bb7a87e6de1a73ccceebfc3`. Tested scope: $N=0,1,2,3,4$ with respectively $6,6,8,10,12$ sides, symbolic outer radius, area one, moments through order $N+1$, and divergence of the second moment. For every tested degree, the moment checks evaluate the symbolic moment expressions at $R=3/2,2,7$ with 60 digits and tolerance $10^{-45}$. Area and second-moment expressions are checked symbolically; the numerical moment checks do not certify every radius. The uniform all-degree conclusion comes from Lean, not this finite experiment.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | **Proved, kernel-checked:** private `starRegion_moments`, `rhoN_starRegion`, `starRegion_secondMoment_lower_bound`, `starRegion_rhoN_unbounded`, used by `result` | $m$-fold symmetry with $m>N+1$ kills moments of orders $1,\ldots,N+1$. The zero polynomial minimizes the error, and fixed-area stretching makes the content unbounded. |
| Strength | **Proved, kernel-checked:** private `sideIndex_add_three`, `starRegion_rhoN_unbounded`, `claim_of_star_geometry`, and public `result` | Every $N\ge0$ has unbounded content on unit-area $2\max(3,N+2)$-gons, hence no maximizer. |
| Source's Theorem 2.2 | **Proved in the cited source:** arXiv:2309.16450v1, Theorem 2.2 | Both $N=1,2$ have no maximizer on unit-area hexagons. The delivered symmetry choice has $m=3$ for $N=1$ and $m=4$ for $N=2$; thus its $N=2$ bound uses eight sides. The source's six-side $N=2$ theorem is not claimed as a specialization of this stronger-in-degree construction. |
| Minimal side count | **Open** | The minimal $n(N)$ and boundedness or existence of maximizers for small $n$ relative to $N$ are not settled. The argument supplies a sufficient side count, not sharpness. |
| Experiment | **Computed:** the pinned experiment, command, exit and SHA-256 in Evidence | Only $N=0,\ldots,4$ and the stated moments, areas and second moments are tested. |
| Literature | **Seat-reported literature reading; completeness ASSUMED-UNVERIFIED** | The readable follow-ups listed below do not settle $N\ge3$; three complete bodies remain unread. |

The conjectural all-degree non-attainment is discharged within the preregistered definitions. Results in the source that assume Conjecture 2.1 may use this conclusion when they use those definitions and hypotheses; the source's other statements and the journal-version correspondence are not independently reverified here. The construction extends to every natural degree, but it does not determine the minimal side count or solve the small-side optimization questions.

### Literature status

The [literature-screen comment](https://github.com/the-omega-institute/trureturing/issues/16916#issuecomment-6208623381) is seat-reported. Bogosel arXiv:2609.14785v2, Kraus–Simanek arXiv:2312.12603v2, Gui–Hu–Li–Zhang arXiv:2606.13448v1, and Gimeno i Garcia–Torres-Valverde arXiv:2610.08222v1 are reported readable and do not settle the $N\ge3$ question. The arXiv:2309.16450v1 statement source supplies Conjecture 2.1 and the known $N=1,2$ result.

Kraus's 2024 Baylor dissertation, the J. Elasticity version of record, and the complete Ditommaso–Ponzo article are unread and unassessed for $N\ge3$. Inspected excerpts are not complete readings. This result makes no claim of publication priority.

## ASSUMED-UNVERIFIED

Literature completeness is **ASSUMED-UNVERIFIED**, including the three unread bodies and whether the journal version changes the conjecture. The follow-up literature screen is attributed to its seat, not independently reproduced here. Four-slot escape-registration completion is unfinished under #17590 and is not inferred from Lean proof or CI success.
