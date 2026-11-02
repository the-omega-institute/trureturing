/- GID: D5/S3/Geometry/KingFinalComposition
   generality: I
   mirror-B: none(waiver:source-only-stage)
   mirror-E: none(waiver:source-only-stage)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: kind=scientific-composition; consumer=Question32 King-grid counterexample
   digest: The actual selected king-grid graph has an integral singular class
     of order two in degree 31327, via canonical prescribed-path induction
     and the retained seed class; arbitrary-family sourceSP is contradicted.
-/

import D5.S3.Geometry.FiniteGraphSuspensionMoves
import D5.S3.Geometry.PrescribedSubdivisionHomology
import D5.S3.Geometry.KingFiniteReplay
import D5.S3.Geometry.IndependenceComplexTorsionSeedSingular
import D5.S3.Geometry.SphereBouquetHomology
import D5.S3.Combinatorics.Graph.Products.CarneroBravoKingRoutes

/-!
UNCOMPILED SOURCE-ONLY CONTINUATION for Carnero Bravo, arXiv:2505.06457v2,
Question 32. Reused project source is licensed under Apache-2.0, as in the
canonical repository LICENSE. Supplier files retain their original GID and
source text. The source pins (which do not assert future merged delivery) are:
* star and coordinate modules: ca35a11485807c5009f6f3afdef81f72f3f48cef;
* singular comparison and its two required support updates:
  d40ed0116eaff5bc2f6afe06f7728b2062e49ed6;
* routing modules: 4024e536502e407db7cd86352cbe5e18baa04d73;
* remaining project imports, including SphereBouquetHomology:
  31fa401a7c17858fa323ddd0886ed580e0c57347 (the freshdev BASE, with no star
  modules; its sphere source is identical to the d40 pin).
The seven move/replay files are retained source-only scientific inputs from
king-suspension-moves-source and king-finite-replay-source. Their original
source-stage comments describe their upstream status, not current acceptance.
Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679
are the intended immutable language/library baseline.
This file imports those exact suppliers and the source-only replay. It contains no `sorry`, `admit`, custom axiom, native
proof escape, build result, or original-problem completion claim.

The finite replay endpoint is identified with the routing base graph by its
literal labels and actual adjacency. The preserved source supplier
`PrescribedSubdivisionHomology` proves the simultaneous subdivision shift
by a well-founded recursion on the total multiplicity: each partial graph
has the canonical Original + Sigma internal carrier, and each step is an
explicit graph isomorphism from a literal triple subdivision. No 31286-deep
carrier or graph/homology correctness premise is introduced.

The final composition uses the actual singular seed class, a reflexive
homeomorphism identifying its actual realization with Ispace G0, the natural
positive-degree reduced/ordinary comparison, forty moves, the prescribed
31286 subdivisions, and the actual selected induced graph isomorphism.
Compactness and the original arbitrary-family sourceSP theorem then give
the contradiction. Every declaration here and every uncompiled imported
source supplier still requires the owner's canonical kernel/CI checks.
-/


noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open CategoryTheory
open scoped BigOperators

namespace D5.S3.Geometry.KingFinalComposition

open D5.S3.Geometry.FiniteGraphSuspensionMoves
open D5.S3.Geometry.KingFiniteReplay
open D5.S3.Geometry.FiniteCoordinateTruncation (Ispace)
open D5.S3.Geometry.IndependenceComplexTorsionSeedSingular
open D5.S3.Combinatorics.Graph.Products
open D5.S3.Combinatorics.Graph.Products.CarneroBravoKingRoutes

/-! ## The retained actual seed torsion class -/

/-- The singular supplier's class is the class transported from the retained
integer seed cycle into the actual finite independence-complex realization.
This is the exact nonzero class killed by two; no abstract torsion premise is
introduced here. -/
theorem seedSingularTorsion :
    singularSeedClass ≠ 0 ∧ (2 : ℕ) • singularSeedClass = 0 :=
  IndependenceComplexTorsionSeedSingular.singularSeedClass_nonzero_killed_by_two

/-! ## The actual 141-vertex endpoint is the routing base graph -/

/-- The old Nat label is the same label used by the finite replay endpoint.
The two subtype carriers are different types, so this is an actual equivalence,
not a definitional identification of graphs. -/
def replayToRouteVertex : ConcreteSubcubicVertex ≃ Original :=
  Equiv.ofBijective
    (fun x => ⟨x.val, by
      have hx : x.val ∈ concreteSubcubicVertices := x.property
      have h : ∀ n ∈ concreteSubcubicVertices, n ∈ oldLabels := by decide
      exact h x.val hx⟩)
    ⟨by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h),
      by
      intro y
      have hy : y.val ∈ concreteSubcubicVertices := by
        have h : ∀ n ∈ oldLabels, n ∈ concreteSubcubicVertices := by decide
        exact h y.val y.property
      exact ⟨⟨y.val, hy⟩, Subtype.ext rfl⟩⟩

/-- The literal endpoint adjacency tables agree. Every edge is checked in the
actual finite list data; no size-only identification is used. -/
theorem replayToRouteAdjacency : ∀ x y : ConcreteSubcubicVertex,
    baseGraph.Adj (replayToRouteVertex x) (replayToRouteVertex y) ↔
      concreteSubcubicGraph.Adj x y := by
  decide

/-- Actual graph isomorphism from the 141-vertex replay endpoint to the
`PrescribedSubdivision` base graph used by the routing core. -/
def replayToRouteBaseIso : concreteSubcubicGraph ≃g baseGraph where
  toEquiv := replayToRouteVertex
  map_rel_iff' := by
    intro x y
    exact replayToRouteAdjacency x y

/-- The concrete forty-move shift transported to the route base graph.
This is the real composition of `fortyMoves` with the actual endpoint graph
isomorphism; it contains no subdivision hypothesis. -/
def routeBaseReducedHomologyIso (q : ℕ) (hq : 1 ≤ q) :
    Reduced baseGraph (q + 40) ≅ Reduced IndependenceComplexTorsionSeed.G0 q :=
  (graphReducedIso replayToRouteBaseIso (q + 40)).symm ≪≫
    KingFiniteReplay.reducedHomologyIso q hq

/-! ## A genuine repeated-triple path expansion -/

/-- The nested carrier after `k` literal triple subdivisions of one edge.
Keeping the nested sums avoids allocating or unrolling 31286 global labels.
This local recursion is retained for reuse; the simultaneous bridge below
uses canonical partial graphs and never flattens these nested carriers. -/
def pathCarrier (X : Type) : ℕ → Type
  | 0 => X
  | n + 1 => pathCarrier X n ⊕ Fin 3

/-- The recursively defined carrier has the actual finite instances required
by MoveChain; typeclass search does not invent these through a variable n. -/
instance pathCarrierFintype {X : Type} [Fintype X] :
    (n : ℕ) → Fintype (pathCarrier X n)
  | 0 => inferInstanceAs (Fintype X)
  | n + 1 => by
      letI := pathCarrierFintype (X := X) n
      exact inferInstanceAs (Fintype (pathCarrier X n ⊕ Fin 3))

instance pathCarrierDecidableEq {X : Type} [DecidableEq X] :
    (n : ℕ) → DecidableEq (pathCarrier X n)
  | 0 => inferInstanceAs (DecidableEq X)
  | n + 1 => by
      letI := pathCarrierDecidableEq (X := X) n
      exact inferInstanceAs (DecidableEq (pathCarrier X n ⊕ Fin 3))

/-- The old vertices are lifted through each successive fresh triple. -/
def pathOldLift {X : Type} : (n : ℕ) → X → pathCarrier X n
  | 0 => id
  | n + 1 => Sum.inl ∘ pathOldLift n

/-- The right endpoint is lifted through the nested carrier. -/
def pathRightLift {X : Type} {a b : X} : (n : ℕ) → pathCarrier X n
  | 0 => b
  | n + 1 => Sum.inl (pathRightLift (a := a) (b := b) n)

/-- After at least one step, the new last vertex is the rightmost fresh
vertex of the latest triple. -/
def pathLast {X : Type} {a b : X} : (n : ℕ) → pathCarrier X n
  | 0 => a
  | n + 1 => Sum.inr (2 : Fin 3)

/-- Actual graph obtained after `n` successive triple subdivisions of the edge
whose endpoints are `pathLast n` and `pathRightLift n`. -/
def pathGraph {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b : X} (h : G.Adj a b) :
    (n : ℕ) → SimpleGraph (pathCarrier X n)
  | 0 => G
  | n + 1 =>
      tripleSubdivision (pathGraph G h n) (pathLast (a := a) (b := b) n)
        (pathRightLift (a := a) (b := b) n)

/-- The selected edge remains present after each preceding subdivision. This
is the exact edge condition consumed by the next `MoveChain.triple`. -/
def pathEdgeProof {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b : X} (h : G.Adj a b) :
    (n : ℕ) → (pathGraph G h n).Adj
      (pathLast (a := a) (b := b) n)
      (pathRightLift (a := a) (b := b) n)
  | 0 => h
  | n + 1 => by
      change (tripleSubdivision (pathGraph G h n)
        (pathLast (a := a) (b := b) n)
        (pathRightLift (a := a) (b := b) n)).Adj
        (Sum.inr (2 : Fin 3)) (Sum.inl (pathRightLift (a := a) (b := b) n))
      change ((2 : Fin 3) = 0 ∧
        pathRightLift (a := a) (b := b) n = pathLast (a := a) (b := b) n) ∨
        ((2 : Fin 3) = 2 ∧
          pathRightLift (a := a) (b := b) n = pathRightLift (a := a) (b := b) n)
      exact Or.inr ⟨rfl, rfl⟩

/-- The complete concrete chain for one path. The recursion is on the actual
number of triple subdivisions and does not assume a homology shift. -/
def pathMoveChain {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b : X} (h : G.Adj a b) :
    (n : ℕ) → MoveChain G (pathGraph G h n) n
  | 0 => MoveChain.refl G
  | n + 1 => by
      let prior := pathMoveChain G h n
      have hstep := pathEdgeProof G h n
      simpa [pathGraph] using
        (MoveChain.triple prior
          (pathLast (a := a) (b := b) n)
          (pathRightLift (a := a) (b := b) n)
          hstep (Equiv.refl _))

/-- Actual reduced singular-homology transport for one prescribed path. -/
def pathReducedHomologyIso {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b : X} (h : G.Adj a b)
    (n q : ℕ) (hq : 1 ≤ q) :
    Reduced (pathGraph G h n) (q + n) ≅ Reduced G q :=
  (pathMoveChain G h n).reducedHomologyIso q hq

/-- A preceding triple subdivision preserves an unrelated old adjacency.
The disequality is stated on the unordered endpoint pairs, so ambient cross
edges are retained exactly as required by the local-subgraph suppliers. -/
theorem tripleSubdivision_old_adj_of_pair_ne
    {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b x y : X}
    (hxy : G.Adj x y)
    (hne : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
    (tripleSubdivision G a b).Adj (Sum.inl x) (Sum.inl y) := by
  exact ⟨hxy, hne⟩

/-- Iterating the preceding lemma gives the old-edge preservation needed when
processing a second route edge. This is the reusable combinatorial half of
the simultaneous-subdivision construction. -/
theorem pathGraph_old_adj_of_pair_ne
    {X : Type} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {a b x y : X}
    (hxy : G.Adj x y)
    (hne : ∀ n, ¬ ((pathOldLift n x = pathLast (a := a) (b := b) n ∧
      pathOldLift n y = pathRightLift (a := a) (b := b) n) ∨
      (pathOldLift n x = pathRightLift (a := a) (b := b) n ∧
       pathOldLift n y = pathLast (a := a) (b := b) n)))
    (h : G.Adj a b) (n : ℕ) :
    (pathGraph G h n).Adj (pathOldLift n x) (pathOldLift n y) := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
      exact tripleSubdivision_old_adj_of_pair_ne _ ih (hne n)

/-! ## The simultaneous prescribed subdivision and the actual selected graph -/

/-- The route's final graph is the actual selected induced finite graph, via
the reviewed induced graph isomorphism. -/
def selectedToRoutedReducedIso (q : ℕ) :
    Reduced (rectangle.induce selected) q ≅ Reduced RoutedGraph q :=
  (graphReducedIso inducedIso q).symm

/-- The actual route counts, supplied by the unchanged routing data. -/
theorem route_counts :
    Fintype.card Original = 141 ∧
    Fintype.card Edge = 178 ∧
    (∑ e : Edge, subdivision.k e) = 31286 ∧
    Fintype.card Vertex = 93999 ∧
    RoutedGraph.edgeFinset.card = 94036 := by
  exact ⟨original_card, edge_card, sum_subdivisions, actual_vertex_count,
    actual_edge_count⟩

/-- Pair injectivity on the actual Original subtype follows from the
routing supplier's injectivity on the underlying Nat labels. -/
theorem routeEndpointPairInjective :
    Function.Injective (fun e : Edge =>
      s(subdivision.left e, subdivision.right e)) := by
  intro e f h
  apply endpoint_pair_injective
  change s((route e).left, (route e).right) =
    s((route f).left, (route f).right)
  simpa only [Sym2.map_mk] using congrArg
    (Sym2.map (fun x : Original => x.val)) h

/-- The formerly unpaid simultaneous bridge, now consumed from the actual
canonical partial-graph induction. The supplier proves `Partial.labels`,
`Partial.stepIso`, `Partial.tip_adjacent`, `Partial.zeroIso` and
`Partial.positiveIso`; its recursion decreases sum n by one and applies the
actual single-triple homology theorem at each step. Its only additional
hypothesis is the proved combinatorial endpoint-pair injectivity above. -/
def prescribedSubdivisionReducedHomologyIso (q : ℕ) (hq : 1 ≤ q) :
    Reduced RoutedGraph (q + ∑ e : Edge, subdivision.k e) ≅
      Reduced baseGraph q :=
  PrescribedSubdivisionHomology.reducedHomologyIsoOfAdjacency
    subdivision baseGraph baseGraph_iff_endpoints routeEndpointPairInjective q hq

/-- Actual forty-plus-31286 transport, with every graph identification
present. The resulting shift of seed degree one is exactly degree 31327. -/
def selectedReducedHomologyIso (q : ℕ) (hq : 1 ≤ q) :
    Reduced (rectangle.induce selected) (q + 31326) ≅
      Reduced IndependenceComplexTorsionSeed.G0 q := by
  have hdegree : q + 31326 =
      (q + 40) + ∑ e : Edge, subdivision.k e := by
    rw [sum_subdivisions]
    omega
  rw [hdegree]
  exact selectedToRoutedReducedIso _ ≪≫
    prescribedSubdivisionReducedHomologyIso (q + 40) (by omega) ≪≫
    routeBaseReducedHomologyIso q hq

/-! ## Actual seed realization, ordinary homology, and the torsion class -/

/-- This is equality of the actual realizations: seedComplex was defined as
independenceComplex G0, and Ispace is its finite-coordinate realization.
No triangulation comparison or assumed carrier identification is needed. -/
def seedRealizationHomeomorph :
    ↥(FiniteConeCollapse.realization IndependenceComplexTorsionSeedSingular.K) ≃ₜ
      Ispace IndependenceComplexTorsionSeed.G0 := by
  change Ispace IndependenceComplexTorsionSeed.G0 ≃ₜ
    Ispace IndependenceComplexTorsionSeed.G0
  exact Homeomorph.refl _

/-- The actual reduced seed H1 is identified with the ordinary singular H1
containing singularSeedClass, using the real positive-degree comparison and
real realization homeomorphism. -/
def seedReducedIsoSingular :
    Reduced IndependenceComplexTorsionSeed.G0 1 ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of ↥(FiniteConeCollapse.realization
            IndependenceComplexTorsionSeedSingular.K)) :=
  (TauCeti.reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) 0).app
      (TopCat.of (Ispace IndependenceComplexTorsionSeed.G0)) ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo
          (X := TopCat.of (Ispace IndependenceComplexTorsionSeed.G0))
          (Y := TopCat.of ↥(FiniteConeCollapse.realization
            IndependenceComplexTorsionSeedSingular.K))
          seedRealizationHomeomorph.symm)

/-- Ordinary integral singular homology of the ACTUAL selected induced graph,
in the exact final degree, is isomorphic to the actual ordinary seed H1. -/
def selectedSingularHomologyIso :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 31327).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Ispace (rectangle.induce selected))) ≅
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of ↥(FiniteConeCollapse.realization
          IndependenceComplexTorsionSeedSingular.K)) :=
  ((TauCeti.reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) 31326).app
    (TopCat.of (Ispace (rectangle.induce selected)))).symm ≪≫
      selectedReducedHomologyIso 1 (by decide) ≪≫ seedReducedIsoSingular

/-- The retained actual seed cycle class transported to the actual induced
king-grid independence realization, rather than a certificate torsion field. -/
def selectedSingularClass :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 31327).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Ispace (rectangle.induce selected))) :=
  selectedSingularHomologyIso.inv singularSeedClass

/-- The exact selected graph has nonzero integral singular 2-torsion. -/
theorem selectedSingularClass_nonzero_killed_by_two :
    selectedSingularClass ≠ 0 ∧ (2 : ℕ) • selectedSingularClass = 0 := by
  constructor
  · intro hzero
    have h := congrArg selectedSingularHomologyIso.hom hzero
    apply seedSingularTorsion.1
    simpa only [selectedSingularClass, ModuleCat.hom_inv_apply, map_zero] using h
  · change (2 : ℕ) • selectedSingularHomologyIso.inv singularSeedClass = 0
    rw [← map_nsmul, seedSingularTorsion.2, map_zero]

/-! ## The original arbitrary-family sourceSP contradiction -/

universe v

/-- The selected induced graph does not have the source's original SP
property. Sphere dimensions, index family and basepoints are unrestricted,
exactly as in the pinned sourceSP definition; in particular S0 is allowed. -/
theorem selected_not_sourceSP :
    ¬ HereditaryLexicographicProduct.sourceSP.{0, v}
      (Ispace (rectangle.induce selected)) := by
  intro h
  letI : CompactSpace (Ispace (rectangle.induce selected)) :=
    FiniteSimplicialJoin.realizationCompactSpace
      (FiniteGraphVertexSubstitution.independenceComplex
        (rectangle.induce selected)).toPreAbstractSimplicialComplex
  have hz : (2 : ℤ) • selectedSingularClass = 0 := by
    simpa only [two_smul] using selectedSingularClass_nonzero_killed_by_two.2
  exact selectedSingularClass_nonzero_killed_by_two.1
    (SphereBouquetHomology.compact_sourceSP_smul_eq_zero h 31327 (by decide)
      2 (by decide) selectedSingularClass hz)

/-- The concrete selected set is nonempty independently of homology. -/
theorem selected_nonempty : selected.Nonempty := by
  let e : Edge := ⟨0, by decide⟩
  let x : Vertex := .inl (subdivision.left e)
  exact ⟨inducedEmbedding x, ⟨x, rfl⟩⟩

/-- Negative answer to the exact hereditary Question 32, represented by the
unchanged rectangle P9337 strong P9061 and its actual selected induced graph.
This source declaration is not a kernel/CI acceptance or priority claim. -/
theorem rectangle_not_sourceSW :
    ¬ HereditaryLexicographicProduct.sourceSW.{0, v} rectangle := by
  intro h
  exact selected_not_sourceSP (h selected selected_nonempty)

/-- The explicit original obstruction with the published selected set and
its exact graph cardinalities. None of these are hypotheses of the result. -/
theorem question32_counterexample :
    selected.Nonempty ∧
      Fintype.card selected = 93999 ∧
      (rectangle.induce selected).edgeFinset.card = 94036 ∧
      ¬ HereditaryLexicographicProduct.sourceSP.{0, v}
        (Ispace (rectangle.induce selected)) := by
  exact ⟨selected_nonempty, selected_vertex_count,
    selected_edge_count, selected_not_sourceSP⟩

end D5.S3.Geometry.KingFinalComposition
