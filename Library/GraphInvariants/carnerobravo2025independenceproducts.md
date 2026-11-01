---
bibkey: carnerobravo2025independenceproducts
authors: Andrés Carnero Bravo
year: 2025
title: On independence complexes of graph products
doi: null
url: https://arxiv.org/abs/2505.06457v2
claim: "Theorem 21 gives a suspended independence-complex conclusion for induced subgraphs of lexicographic products; Question 22 asks for unsuspended membership in the hereditary class W; Question 32 asks whether the hereditary sphere-wedge statement of Theorem 31 extends to every king-grid width."
strata_touched:
  - D5/S3/Geometry/FiniteGraphVertexSubstitution
  - D5/S3/Geometry/HereditaryLexicographicProduct
  - D5/S3/Geometry/FiniteGraphSubgraphSuspension
  - D5/S3/Geometry/IndependenceComplexTorsionSeed
  - D5/S3/Geometry/SphereBouquetHomology
license: citation-only
triage: anchor
---

# Independence complexes of lexicographic products

Primary: Andrés Carnero Bravo, *On independence complexes of graph products*,
arXiv:2505.06457v2, 11 November 2025.

## Source scope

Section 2 defines the independence complex $I(G)$ and the lexicographic
product $G\circ H$: vertices are pairs, with adjacency either over an edge
of $G$ or within a single fiber over an edge of $H$.
The paragraph immediately preceding Proposition 7 defines:

- $\mathcal P$: $I(G)$ is contractible, homotopy equivalent to a wedge of
  spheres, or homotopy equivalent to a disjoint union of wedges of spheres.
- $\mathcal{SP}$: $I(G)$ is contractible or homotopy equivalent to a wedge
  of spheres.
- $\mathcal W$: every induced subgraph has property $\mathcal P$.
- $\mathcal{SW}$: every induced subgraph has property $\mathcal{SP}$.

Section 4, in the proof of Theorem 19, writes the independence complex of
an induced subgraph of $G\circ H$ as a polyhedral join over an induced
subgraph of $G$, with factors the independence complexes of induced
subgraphs of $H$.

Theorem 21 states that, for $G,H\in\mathcal{SW}$ both of order at least two
and every induced subgraph $F$ of $G\circ H$, the suspension $\Sigma I(F)$
is contractible or homotopy equivalent to a wedge of spheres.
Question 22 asks, under those same hypotheses, whether
$G\circ H\in\mathcal W$. Thus its requested conclusion concerns the
unsuspended complexes of all induced subgraphs; Theorem 21 does not supply
that conclusion.

## Verified locator

- URL: https://arxiv.org/abs/2505.06457v2
- Version v2, Section 2 (the definitions of $I(G)$, $G\circ H$, and
  $\mathcal P$, $\mathcal{SP}$, $\mathcal W$, $\mathcal{SW}$), and the
  paragraph immediately preceding Proposition 7.
- Theorem 21 and Question 22.
- Theorem 31 and Questions 32 and 35.

## Local realization refinement

`FiniteGraphVertexSubstitution.oneVertexReplacementEquiv` is a local
finite-coordinate construction in this setting, not a theorem attributed
to this paper. Its base graph and current fibers are arbitrary finite
types, the fibers may carry different graphs, and only the selected old
fiber is required to be a singleton. A chosen vertex in the new fiber
provides the basepoint. The result is a homotopy equivalence from the
actual new substitution independence realization to the actual quotient
wedge of the old realization and the simplicial link-join realization.
Other fibers may be empty, and the restricted link complex may have no
faces; the pure-right singleton still supplies the join basepoint.

The paper's simplicial-complex convention includes the empty face; the
local coordinate realizations use nonempty faces. In particular, an
ordinary topological join interpretation requires nonempty factor
realizations and is not asserted in the empty-link case. The exact
heterogeneous telescope, coordinate maps and quotient topology are local
proof content. This replacement bridge alone does not supply the hereditary
sphere-wedge conclusion of Question 22.

## Complete local product settlement

`HereditaryLexicographicProduct.result` combines that original induction with
actual occupied-induced transports, compact finite sphere models and the
proved finite marked-wedge and ordinary-join closures. Its hypotheses are
the original two graph-order conditions and unsuspended sourceSW on each
factor; no closure or carrier-identification premise is added.

The native empty independence realization is empty. Accordingly the local
sourceSW convention requires SP on every nonempty induced set, while its
sourceW conclusion covers all induced sets and realizes an empty target by
zero outer coproduct components. The primary text does not separately settle
this vertexless boundary; this convention must remain explicit.

The [problem dossier](../../Problems/carnero-bravo-2025-hereditary-lexicographic-products.md)
records the exact target, proof route and bounded literature standing.
This is a local formal proof, not a theorem attributed to the source author,
a global novelty certificate or official problem acceptance. The attempted
source-readout registration remains unfinished under issue #22742.

## Strong products and arbitrary subgraph suspension

Theorem 31 states that $P_n\boxtimes P_m$ belongs to $\mathcal{SW}$ for
all $n$ and $1\le m\le4$. Question 32 asks whether this extends to every
$m$. The class $\mathcal{SW}$ quantifies over all induced subgraphs; this
is stronger than Question 35, which asks only whether the independence
complex of each full rectangle $P_n\boxtimes P_m$ is a wedge of spheres.
These locators refer to the same version v2 at the verified URL above.

`FiniteGraphSubgraphSuspension` constructs the maximal-independent-set star
gadget for an arbitrary, possibly noninduced subgraph $H$ of a finite graph
$G$. It retains all old edges of $G$ absent from $H$. A hub and independent
apices indexed by the maximal independent sets of $H$ give a literal face
cover whose intersection is $I(G)$. The local and spanning conventions
are identified by adjoining the isolated vertices outside $V(H)$ to each
maximal independent set.

The coordinate neighborhoods use total apex mass, the finite minimum of
hub mass plus old mass outside a maximal independent set, continuous
cutoffs and normalization. Their actual intersection is homotopy equivalent
to the coordinate realization of $I(G)$; the existing open-cover reduced
Mayer--Vietoris theorem and homotopy invariance then give the integral
singular homology shift in degrees $q+1$ and $q$, for $q\geq1$.
This is supporting machinery for Question 32. It does not settle that
question: the seed singular comparison, complete gadget replay, king-grid
rotation and sphere-bouquet torsion obstruction remain further obligations.

The general mechanisms of graph suspension, independence-complex splitting
and star clusters have classical sources, including:

- Michal Adamaszek, *Splittings of independence complexes and the powers of
  cycles*, Journal of Combinatorial Theory, Series A 119 (2012), 1031--1047,
  https://doi.org/10.1016/j.jcta.2012.01.009.
- Jonathan Ariel Barmak, *Star clusters in independence complexes of graphs*,
  Advances in Mathematics 241 (2013), 33--57,
  https://doi.org/10.1016/j.aim.2013.03.016.
- Péter Csorba, *Subdivision yields Alexander duality on independence
  complexes*, Electronic Journal of Combinatorics 16 (2009), Research Paper 11,
  https://doi.org/10.37236/77.

These are references [3], [5] and [11] of Carnero Bravo's v2 paper. The
explicit coordinate neighborhood construction here does not claim that the
general suspension or star-cluster mechanism is new, and these supporting
modules carry no claim of original-problem acceptance or priority.

The unfinished source-readout registrations for the public lemmas in these
four supporting modules are tracked in [issue #25180](https://github.com/the-omega-institute/trureturing/issues/25180).
The three homology-isomorphism endpoints are definitions; they do not exhaust
the public theorem audit targets. The issue is neither a proof nor a validated
registration.

## King-grid question and the finite-chain seed

Theorem 31 states that $P_n\boxtimes P_m\in\mathcal{SW}$ for every $n$
and $1\le m\le4$. Question 32 asks, “Can Theorem 31 be extended to any
$m$?” This is the hereditary statement about all induced subgraphs.
Question 35 instead asks whether the independence complex of the full
$P_n\boxtimes P_m$ is always a wedge of spheres. A counterexample among
induced subgraphs targets Question 32 and need not answer Question 35.

`IndependenceComplexTorsionSeed` constructs an order-two class in the
integer finite ordered chain homology of the independence complex of the
complement of the graph with graph6 encoding `JEhbtj{rve?`. This exact
classical graph6 seed appears in Adamaszek, *Small flag complexes with
torsion* (2012), [arXiv:1208.3892v1](https://arxiv.org/abs/1208.3892v1).
The local explicit Lean proof supplies all 32 increasing edges, all 24
increasing triangles, the cycle, a chain bounding its double and a mod-two
detecting functional. The classical seed and its local formal proof do not
constitute a separate solved original problem or a novelty claim.

The finite-chain class alone supplies no comparison with singular
homology of the coordinate realization. Such a comparison, its transport
through the proposed graph construction and the induced king-grid
embedding, and the sphere-wedge torsion obstruction remain necessary
for a complete Question 32 counterexample.

## Actual singular homology obstruction for sphere sources

`SphereBouquetHomology.compact_sourceSP_smul_eq_zero` states the obstruction
on Mathlib's actual integral singular homology: for a compact topological
space X with `HereditaryLexicographicProduct.sourceSP.{0,v} X`, every positive
degree q, every nonzero integer n and every class z, `n • z = 0` implies
`z = 0`. The original wedge index J ranges over arbitrary `Type v`, the
dimensions are heterogeneous natural numbers including zero, and the original
sphere basepoints are unrestricted. Compactness is used by the existing
`CompactSphereNormalForm.compactWedgeModel`, not replaced by an assumption
that the original family is finite.

The proof constructs actual relatively open vertex stars and their based
contractions, identifies saturated open subwedges by homeomorphisms, reuses
`FiniteConeUnionWedge.wedgeInverseHomotopy` for continuous quotient cylinders,
and applies open Mayer–Vietoris. At q=1 the intersection term is reduced H0;
ordinary H0 of a nonempty contractible intersection does not vanish. Sphere
dimension induction supplies all off-dimensional vanishing degrees, while
`TauCeti.reducedSingularHomologySphereIso` supplies the diagonal. Finite
bouquet append homeomorphisms and `nativeBouquetHomeomorph` connect these
calculations to the existing compact normal form. An empty inner bouquet is
a point; an empty outer model is empty.

These are classical sphere-homology and Mayer–Vietoris arguments; see
[Hatcher, Algebraic Topology](../Geometry/hatcher2002algebraic.md), Chapter 2.
The implementation reuses the existing TauCeti sphere and reduced
Mayer–Vietoris source port, whose source revision and license remain in those
supplier modules. No literature novelty claim is made. The generic ring
statements use Mathlib's regular-scalar meaning of module torsion-freeness;
the nonzero-integer injectivity statement uses the integral-domain endpoint.

This obstruction batch contributes zero original-problem resolution credit
for Question 32. Its intended use takes n=2, but the seed-to-singular homology
comparison, the remaining suspension and graph construction steps, the
induced-coordinate embedding and the final refutation are still required.

The new source modules' readout registration remains unfinished under
[issue #25194](https://github.com/the-omega-institute/trureturing/issues/25194).
The dependent-family interface is available, but an actual homology/quotient
source arena, complete source reconstruction and equivalence bridge, and
whole-family variation, sensitivity and observational-dependence proofs
have not been delivered. No `declared_validated` status is claimed.
