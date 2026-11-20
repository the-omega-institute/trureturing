---
bibkey: gangloff2023various
authors: Silvère Gangloff; Pierre Guillon; Piotr Oprocha
year: 2023
title: Various questions around finitely positively expansive dynamical systems
doi: 10.1016/j.topol.2025.109597
url: https://arxiv.org/abs/2310.17241v1
claim: Question 3.1 asks for strict finite positive-expansivity levels on the circle; Theorem 3.8 excludes finitely positively expansive interval systems; the repository also proves the obstruction for every nondegenerate compact metric standard dendroid, within the scope of Question 3.2.
strata_touched:
  - D5/S1/Dynamics/Shadowing/IntervalObstruction
  - D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness
  - D5/S1/Dynamics/Shadowing/DendriteObstruction
  - D5/S1/Dynamics/Shadowing/InvarianceGluedSheets
  - D5/S1/Dynamics/Shadowing/CantorCircleExpansivity
  - D5/S1/Dynamics/Shadowing/BouquetExactExpansivity
  - D5/S1/Dynamics/Shadowing/ExactPendantObstruction
  - D5/S3/Topology/CoveringDimension/GluedCircle
license: citation-only
triage: anchor
---

# Various questions around finitely positively expansive dynamical systems

Question 3.1, Section 3, page 7 of arXiv:2310.17241v1, asks:

> Can we find, for every n ≥ 1, a positively (n + 1)-expansive map of the circle which is not positively n-expansive?

The repository's [full-circle theorem](../../Blueprint/D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.md)
proves that every continuous selfmap of the entire circle with a uniform
finite strict forward Bowen bound is positively expansive. Thus none of the
strict finite hierarchy levels requested in Question 3.1 exists. Its positive
expansivity scale may differ from the finite-bound scale. The theorem adds no
smoothness, invertibility or surjectivity hypothesis. The precise source
correspondence and comparison limits are in the
[circle problem dossier](../../Problems/gangloff-guillon-oprocha-circle-finite-positive-expansivity.md).
This circle proof is repository-derived; attribution of the question does not
attribute that proof to the paper or assert worldwide priority.

Theorem 3.8 states that no interval system is finitely positively expansive.
The repository gives a direct Lean proof for every nondegenerate compact
real interval and an equivalent formulation by arbitrarily large injective
families of all-time close forward orbits. These interval results are consumed
by the circle finite-positive-expansiveness proof; the known interval
obstruction is not claimed as a new discovery.

The direct proof uses exact interval pullbacks, monotone trapping and
coalescing fold histories. It does not assume the source theorem or use
mixing as an additional hypothesis.

The repository's [all-dendroid theorem](../../Blueprint/D5/S1/Dynamics/Shadowing/DendriteObstruction/AllDendroid.md)
proves that every continuous self-map of every nondegenerate compact metric
standard dendroid fails finite positive expansivity. Here the standard
dendroid structure is arcwise connectedness and hereditary unicoherence;
local connectedness, finite branching and uniform arc packing are not
additional assumptions. The map need not be invertible or surjective.
Precisely, for every positive real scale and every natural number m at least
two, there are exactly m distinct points whose joint image under each
iterate has diameter strictly below that scale at every natural time,
including time zero. This is a complete obstruction for the dendroid class;
it does not settle the entire one-dimensional classification in Question 3.2.

The static small-opening theorem supplies the separate opening hypothesis
of the dynamic minimal-invariant-set argument. It gives, inside every
nondegenerate subcontinuum and at every positive scale, a compact connected
subset whose nonempty relative open complement has diameter strictly below
that scale. The static theorem is classical: Krasinkiewicz and Minc,
*Continua and their open subsets with connected complements*, Fundamenta
Mathematicae 102 (1979), 129–136,
[DOI 10.4064/fm-102-2-129-136](https://doi.org/10.4064/fm-102-2-129-136).
Heath and Nall, *Centers of a dendroid*, Fundamenta Mathematicae 189 (2006),
173–183, [DOI 10.4064/fm189-2-6](https://doi.org/10.4064/fm189-2-6),
state the small co-connected-open property on the read page 180.
The Lean package proves and consumes this static input through
ProperExpansion, CoconnectedOpening and TentObstruction; it does not assume
it as an axiom or claim it as a new static theorem.

## Exact expansion order for a gluing construction

Question 3.2 asks which one-dimensional continua admit finitely
positively expansive systems. The theorem
`InvarianceGluedSheets.exact_order_infDist` treats a concrete
construction over a positively expansive base. Take $N\geq 2$ graphs
of integer multiples of distance to a nonempty compact forward-invariant
set $K$. A sufficiently small strict forward Bowen ball lies in a
single fiber of the projection, so its cardinality is at most $N$.
The map is positively expansive exactly when $K$ is the set of points
whose entire forward orbits stay in some open neighborhood of $K$.
Otherwise, for every positive radius there are $N$ distinct points in
one fiber that stay pairwise closer than that radius under every
forward iterate. This gives the exact expansion order of the glued
system.

Remark 3.10 of the arXiv version realizes each exact finite order on a
finite bouquet of circles. At order N at least two on the bouquet of N
circles, the displayed map has image equal to its last circle.

The repository also constructs a topologically exact continuous surjection
of exact positive expansivity order N on the bouquet of N circles for every
N at least two. On each circle the map runs through all N circles in order.
The projection forgetting the circle label semiconjugates the map to
multiplication by N on the circle. Each nonempty open set projects to a
set containing an arc, whose image under sufficiently many iterates
covers the circle. The next application of the traversal covers the
whole bouquet. Distinct points with the same phase close to the common
vertex coalesce in one step and witness all N points in a forward Bowen ball.
[Finite bouquet construction](../../Blueprint/D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.md)

Hisao Kato constructs a surjective positively pseudo-expansive map on every
finite connected graph containing a simple closed curve. His condition (P1)
gives a finite closed cover with a positive separation scale on each member.
A forward Bowen ball at less than half the minimum of those scales meets each
member in at most one point, giving a uniform finite cardinal bound. The
relevant locators are §2, pp. 202–203 and Theorem (4.3), pp. 207–208. The
explicit bouquet traversal above specifies the exact order and proves
topological exactness.
[Kato 1991](https://doi.org/10.4064/fm-137-3-201-210)

## Endpoint obstruction under topological exactness

An embedded closed interval whose image away from one endpoint is open
in the carrier obstructs finite positive expansivity of continuous exact
selfmaps on compact metric spaces. When the fibers are finite, exactness
sends an interior point of each open subarc to the free endpoint, and
both nearby sides cover a common smaller arc. Controlling the finite
prefix before each such fold produces arbitrarily large, eventually
coalescing families at each strict forward Bowen scale. An infinite
fiber supplies such families inside one small ball. This applies to
any finite graph with a leaf.
The argument uses the coalescing-witness mechanism of Remark 3.4 and
Lemma 3.7. Question 3.2 asks about general continuous selfmaps and does
not impose topological exactness.
[Pendant arc obstruction](../../Blueprint/D5/S1/Dynamics/Shadowing/ExactPendantObstruction.md)

For each integer N at least two, the repository constructs a compact connected
metric space of covering dimension one with a continuous surjection of least
positive expansivity order N. It glues N circles along the image of the
ternary Cantor set and applies tripling on each circle. For positive Cantor
points x tending to zero, (1 + x)/3 lies in the open middle third and enters
the Cantor image in one step. These points give fibers that witness failure
of every scale of order N − 1. The closed finite-to-one projection onto the
circle gives the upper covering-dimension bound, and connectedness gives the
lower bound. The result combines surjectivity with exact order on a
one-dimensional continuum. The classification in Question 3.2 remains open.
[Construction and covering dimension](../../Blueprint/D5/S3/Topology/CoveringDimension/GluedCircle.md)

The GGO journal DOI
[10.1016/j.topol.2025.109597](https://doi.org/10.1016/j.topol.2025.109597)
is confirmed bibliographic metadata. The question and theorem locators here
refer to the read arXiv v1. The final GGO article body and the Artigue article
body associated with [DOI 10.1016/j.topol.2026.110006](https://doi.org/10.1016/j.topol.2026.110006)
remain unavailable for comparison. No worldwide originality or priority
claim follows from this repository result.

## Verified locator

- https://arxiv.org/abs/2310.17241v1
- https://doi.org/10.1016/j.topol.2025.109597
- Question 3.1, Section 3, page 7.
- Question 3.2, Section 3, page 7.
- Theorem 3.8, Section 3.1, page 9.
- Remark 3.10, Section 3.2, page 9.
