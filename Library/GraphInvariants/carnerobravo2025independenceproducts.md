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
  - D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes
  - D5/S3/Geometry/FiniteSimplicialSingularHomology
  - D5/S3/Geometry/IndependenceComplexTorsionSeedSingular
  - D5/S3/Geometry/SphereBouquetHomology
  - D5/S3/Geometry/FiniteGraphSuspensionMoves
  - D5/S3/Geometry/PrescribedSubdivisionHomology
  - D5/S3/Geometry/KingFiniteReplay
  - D5/S3/Geometry/KingFinalComposition
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
- Theorems 31 and 33 and Questions 32 and 35.

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
This supplies the single-move homology input for the complete Question 32
composition below. Its local suspension theorem alone is not a counterexample.

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

These are references [1], [5] and [11] of Carnero Bravo's v2 paper. The
explicit coordinate neighborhood construction here does not claim that the
general suspension or star-cluster mechanism is new, and these supporting
modules carry no claim of original-problem acceptance or priority.

The geometric predecessor is Brent N. Clark, Charles J. Colbourn and
David S. Johnson, *Unit disk graphs*, Discrete Mathematics 86 (1990),
165--177, https://doi.org/10.1016/0012-365X(90)90358-O, proof of Theorem 5.1,
pp. 172--173. For a planar graph of maximum degree three, that proof
constructs an induced square-grid subdivision with each original edge
replaced by a path of length $3k_e+1$. Its orthogonal embedding input is
Lemma 2.1, p. 168, credited there to Valiant. Theorem 5.1 itself states
NP-completeness of GRID DOMINATING SET; the geometric construction is in
its proof.

The planar independence-complex realization is Skwarski's result, explicitly
credited and alternatively proved in Barmak,
[arXiv:1007.0418v1](https://arxiv.org/abs/1007.0418v1), Theorem 7.3,
pp. 19--20: every finite complex is homotopy equivalent, after iterated
suspension, to the independence complex of a finite planar graph.
Barmak's Theorem 7.5, p. 20, separately gives maximum degree at most three;
its statement does not assert planarity.

To retain planarity in the degree reduction of its proof (p. 21), fix a
plane embedding and choose two cyclically consecutive edges $ww_1,ww_2$
at a vertex $w$ of degree $d>3$. Apply Definition 7.1, p. 19, with the
subgraph having exactly these two edges. Writing $a=v_{\{w\}}$ and
$b=v_{\{w_1,w_2\}}$, the replacement deletes $ww_1,ww_2$ and inserts
the path $w-b-v-a$ and edges $aw_1,aw_2$. Every other old edge, including
a possible ambient $w_1w_2$, is retained. Take a small disk about $w$
meeting only its incident arcs. The selected ports are consecutive, so
their junction $a$ can be split off into their common sector and joined
to $w$ by the subdivided path inside the disk, keeping the other ports
and the drawing outside the disk fixed. This embeds the local tree
without crossings. The degree of $w$ drops to $d-1$, the new degrees
are three at $a$ and two at $b,v$, and all other old degrees are unchanged.
Iteration therefore terminates in a planar graph of maximum degree three;
Proposition 7.2, p. 19, gives one suspension at each step.

Csorba, Theorem 11, p. 6, gives one suspension when an edge is replaced
by a path of length four. Thus the subsequent Clark--Colbourn--Johnson
paths of lengths $3k_e+1$ give $\sum_e k_e$ further suspensions by
successive triple subdivisions, with no need for equal $k_e$.
Finally $T(x,y)=(x+y,x-y)$ is injective and satisfies
$\|T(u)-T(v)\|_\infty=\|u-v\|_1$, since
$\max(|a+b|,|a-b|)=|a|+|b|$. Hence distinct square-lattice points are
neighbors exactly when their images are king-grid neighbors, and a finite
image translates into a finite rectangle. The planar degree reduction
and square-to-king conversion are elementary deductions given here,
not theorem statements quoted from Barmak or Clark--Colbourn--Johnson.

Starting with a finite triangulation of $\mathbb{RP}^2$, these classical
constructions and the two connections produce an induced king-grid graph
whose independence complex is homotopy equivalent to an iterated suspension
of $\mathbb{RP}^2$, hence has positive-degree integral two-torsion. This
qualitative existence consequence supplies no numerical parameters for the
explicit finite implementation below.

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

Theorem 33 has a different scope: if a positive width $m$ has the
hereditary property for every $n$, then the independence complex of the
full graph $P_n\boxtimes P_{m+k}$ has the homotopy type of a wedge of
spheres for $1\leq k\leq4$. Its conclusion does not itself assert the
hereditary property at those larger widths.

`IndependenceComplexTorsionSeed` constructs an order-two class in the
integer finite ordered chain homology of the independence complex of the
complement of the graph with graph6 encoding `JEhbtj{rve?`. The encoding
is taken from the unprinted TeX-source appendix of Adamaszek, *Small flag
complexes with torsion* (2012),
[arXiv:1208.3892v1](https://arxiv.org/abs/1208.3892v1),
[source appendix](https://arxiv.org/src/1208.3892v1).
The four eleven-vertex H1-torsion examples and their minimality were proved
earlier by Mordechai Katzman, *Characteristic-independence of Betti numbers
of graph ideals*, Journal of Combinatorial Theory, Series A 113 (2006),
435--454, https://doi.org/10.1016/j.jcta.2005.04.005; see
[arXiv:math/0408016v2](https://arxiv.org/abs/math/0408016v2), abstract,
p. 1, and Section 5, p. 16. Adamaszek explicitly credits Katzman for
Theorem 1(a),(b) on p. 1. His Section 3, p. 4, records that two of the four
clique complexes are homeomorphic to $\mathbb{RP}^2$ and the other two
collapse to it. The local independence graph is the complement of the
catalogued clique graph; no identification with a numbered Katzman graph
is asserted.
The local explicit Lean proof supplies all 32 increasing edges, all 24
increasing triangles, the cycle, a chain bounding its double and a mod-two
detecting functional. The classical seed and its local formal proof do not
constitute a separate solved original problem or a novelty claim.

`FiniteSimplicialSingularHomology.orderedH1IsoSingular` identifies the
homology of the ordered triangle-to-edge-to-vertex integer short complex
of any finite linearly ordered pre-abstract simplicial complex with
Mathlib singular H1 of its actual finite-coordinate realization. The
coefficient object is `ModuleCat.of ℤ ℤ`. Its positive-coordinate open
stars have contractible face intersections; the ordered Cech and small
singular chain augmentations give the comparison without an assumed
good-cover or homology-isomorphism premise. Empty realizations and
ghost vertices remain within the statement.

`IndependenceComplexTorsionSeedSingular.seedH1IsoSingular` applies that
comparison to the original 11/32/24 finite integer boundary model. Three
basis bijections and both differential squares identify its actual short
complex with the ordered one. The transported `singularSeedClass` is
nonzero and killed by two in singular H1 of the original coordinate
realization, with the same integer coefficient object. No abstract
comparison is assumed.

The finite replay and prescribed-subdivision transport below carry this
class into the selected king-grid graph. The singular seed itself does not
settle Question 32. The comparison audit is unfinished under
issue #25205; the original finite-chain seed audit remains unfinished
under issue #25149.

## Prescribed king-grid routing interface

`CarneroBravoKingRoutes` specifies the actual 141 natural-labelled vertices,
178 original edges and 178 integer polylines with 1,283 corners. The prescribed
subdivision inserts `3*k(e)` distinct fresh vertices on each edge, with
`sum k(e) = 31286`, giving 93,999 vertices and 94,036 edges. Its
induced embedding has target `P_9337` strong `P_9061`. The literal transform
`T(x,y) = (x+y+25,x-y+1705)` has inclusive one-based bounds; the map into
`Fin 9337` times `Fin 9061` subtracts one from both coordinates.

`PrescribedSubdivision`, `IntegerPolyline` and `LatticeRouting` provide
Lean-verified tagged paths, corner-expansion semantics, occupancy-checker
soundness and strong-product conversion. The computational tags retain the
actual edge numbers and natural positions; their injection and exact graph
correspondence with the dependent fresh vertices are proved. The concrete
kernel-checked occupancy reduction proves coordinate injection and both
directions of adjacency for the literal routes. `inducedEmbedding` maps into
the stated finite strong product, and `inducedIso` identifies the routed graph
with the induced graph on its range. `endpoint_inventory`,
`endpoint_pair_injective` and `baseGraph_iff_endpoints` identify the route
endpoints with all original edges. `sum_subdivisions`, `actual_vertex_count`,
`actual_edge_count`, `selected_vertex_count` and `selected_edge_count` give
the exact multiplicity and graph counts. The evaluator proposes occupancy
trees and proof blocks; Lean's kernel checks the exact fill equations and
every block. No native-evaluation axiom or assumed certificate correctness
is used.

The exact seed encoding is from Adamaszek's catalogue; the earlier
eleven-vertex four-example and minimality result is due to Katzman.
The supplied graph-move route uses the Barmak/Lozin approach, with the Lozin
homotopy effect proved by Biyikoglu--Civan,
[arXiv:1302.3064v1](https://arxiv.org/abs/1302.3064v1), Lemma 3.3 and
Proposition 3.4, p. 7. The explicit coordinate construction is local proof
content, not a theorem attributed to Carnero Bravo or an originality claim.
The forty-move replay, prescribed-subdivision suspension transport and
sphere-wedge obstruction are combined in `KingFinalComposition` below. This
routing interface alone does not settle Question 32 and makes no claim about Question
35 or an additional solved original problem.
The source-readout registrations remain unfinished under
[issue #25256](https://github.com/the-omega-institute/trureturing/issues/25256).

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

This obstruction batch alone contributes zero original-problem resolution
credit for Question 32. The complete composition below applies it with n=2
to the transported seed class in the actual selected induced graph.

The new source modules' readout registration remains unfinished under
[issue #25194](https://github.com/the-omega-institute/trureturing/issues/25194).
The dependent-family interface is available, but an actual homology/quotient
source arena, complete source reconstruction and equivalence bridge, and
whole-family variation, sensitivity and observational-dependence proofs
have not been delivered. No `declared_validated` status is claimed.


## Induced king-grid counterexample to Question 32

`KingFiniteReplay.fortyMoves` starts at the actual complement of the graph
encoded by `JEhbtj{rve?` in Adamaszek's catalogue. Its literal finite vertex
and edge lists verify ten triple subdivisions, five matching suspensions and
twenty-five Lozin replacements. The endpoint has 141 vertices and 178 edges.
The local edge and star subgraphs are arbitrary subgraphs: extra ambient
edges in moves 11, 13, 15, 19 and 39 are retained. The suspension mechanisms
are classical, with attribution to Barmak, Proposition 7.2, and
Biyikoglu–Civan, Proposition 3.4, in the corresponding move sources.

`PrescribedSubdivisionHomology` treats an arbitrary finite endpoint inventory
with injective unordered endpoint pairs. Partial paths retain an original
edge at multiplicity zero. Increasing one multiplicity identifies the graph
with one literal triple subdivision of its terminal edge. A proved label
bijection accounts for all old and fresh vertices, and recursion on the sum
of multiplicities composes the single-move homology shifts. Thus every
positive degree q shifts by the prescribed sum; no graph or homology
correctness premise is supplied by the caller.

`KingFinalComposition` identifies the finite replay endpoint with the actual
routing base graph by its natural labels and complete edge inventory. The
forty moves and the 31286 prescribed triple subdivisions transport the
original nonzero integral singular H1 seed class into ordinary integral
singular H31327 of the independence realization of the selected induced
graph. `selectedSingularClass_nonzero_killed_by_two` proves that the class is
nonzero and twice it is zero. This is homology of the actual finite-coordinate
realization, with coefficient object `ModuleCat.of ℤ ℤ`.

The selected realization is compact. Applying
`SphereBouquetHomology.compact_sourceSP_smul_eq_zero` contradicts this class,
so `selected_not_sourceSP` excludes the original contractible-or-sphere-wedge
alternatives. Arbitrary sphere index families, natural dimensions including
S0, arbitrary sphere basepoints and the ordinary quotient wedge topology
remain in scope. The argument does not assume a finite original sphere
family or replace the realization with a homology record.

`question32_counterexample` supplies the nonempty selected set, its 93999
vertices and 94036 edges, and its failure of sourceSP inside the strong
product of paths on 9337 and 9061 vertices. `rectangle_not_sourceSW` and
`result : ¬ claim` refute the universal positive-order hereditary extension
of Theorem 31 asked in Question 32. The sourceSW convention excludes empty
induced sets, while the paper does not specify the vertexless convention;
this counterexample is nonempty. No conclusion about the full-rectangle
Question 35 follows.

The literal construction is identified by SHA-256
`ff9876310835eca475074719e41da20ea0d5056d76b996c3ea7d5b63fcaa0980`.
The original-statement evidence pins arXiv v2 and distinguishes Questions
32 and 35. The qualitative existence of an induced king-grid torsion
obstruction follows from the cited classical constructions and the explicit
connections above. This is distinct from a paper explicitly announcing a
solution under Carnero Bravo's Question 32 numbering. No priority, uniqueness
or exhaustive open-status claim is made. Lean verification
of this construction does not itself constitute independent fidelity review,
required CI, publication acceptance or a priority certificate.

The 377 public theorem audit targets, including the universe-polymorphic
`KingFinalComposition.result`, remain unfinished under
[issue #25577](https://github.com/the-omega-institute/trureturing/issues/25577).
The typed dependent-family attempt for `KingFiniteReplay.rowBits_spec` has a
compiled equivalence bridge, rejected whole-family intervention, sensitivity
and actual observational dependence. Its native binding is
`declared_unresolved` at `source.state_binder`, with no certificate. The
remaining targets lack completed per-target registrations. No
`declared_validated` registration is claimed. Earlier supporting audit
issues above remain separate.
