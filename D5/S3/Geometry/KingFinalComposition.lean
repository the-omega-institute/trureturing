/- GID: D5/S3/Geometry/KingFinalComposition
   generality: I
   mirror-B: D5/B/S3/Geometry/KingFinalComposition
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/KingFinalComposition.utilityClaim; result=D5/S3/Geometry/KingFinalComposition.utilityRefutation; claim=D5/S3/Geometry/KingFinalComposition.utilityClaim
   digest: The selected induced king-grid graph has nonzero integral singular 2-torsion in degree 31327 and refutes arbitrary-family sourceSP. -/

import D5.S3.Geometry.FiniteGraphSuspensionMoves
import D5.S3.Geometry.PrescribedSubdivisionHomology
import D5.S3.Geometry.KingFiniteReplay
import D5.S3.Geometry.IndependenceComplexTorsionSeedSingular
import D5.S3.Geometry.SphereBouquetHomology
import D5.S3.Combinatorics.Graph.Products.CarneroBravoKingRoutes

/-!
# Integral torsion in an induced king-grid graph

The literal forty-move endpoint is identified with the routing base graph
by natural labels and actual adjacency. Simultaneous prescribed subdivision
shifts reduced integral singular homology by 31286 further degrees. The
actual induced graph isomorphism places the resulting graph inside the
strong product of paths on 9337 and 9061 vertices.

The original nonzero seed class killed by two transports to ordinary
integral singular degree 31327 of the actual selected independence
realization. Compactness and the sphere-bouquet torsion obstruction retain
arbitrary indexing families, dimensions including zero, arbitrary basepoints
and ordinary quotient topology. The selected set is nonempty. Thus its
obstruction addresses hereditary Question 32 independently of the paper's
unspecified vertexless convention; it does not address full-rectangle
Question 35. Reused project content is licensed under Apache-2.0.
-/


noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

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

set_option maxHeartbeats 8000000 in
/-- The literal endpoint adjacency tables agree. Every edge is checked in the
actual finite list data; no size-only identification is used. -/
theorem replayToRouteAdjacency : ∀ x y : ConcreteSubcubicVertex,
    baseGraph.Adj (replayToRouteVertex x) (replayToRouteVertex y) ↔
      concreteSubcubicGraph.Adj x y := by
  have inventory :
      (concreteSubcubicEdges.map (fun z => s(z.1, z.2))).toFinset = constructionEdges := by
    decide
  intro x y
  change s(x.val, y.val) ∈ constructionEdges ↔
    x ≠ y ∧ ((x.val, y.val) ∈ concreteSubcubicEdges ∨
      (y.val, x.val) ∈ concreteSubcubicEdges)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      subst y
      exact construction_no_diagonals _ h (by simp)
    · rw [← inventory, List.mem_toFinset, List.mem_map] at h
      obtain ⟨⟨a, b⟩, hab, heq⟩ := h
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · change a = x.val at ha
        change b = y.val at hb
        exact Or.inl (by simpa only [ha, hb] using hab)
      · change a = y.val at ha
        change b = x.val at hb
        exact Or.inr (by simpa only [ha, hb] using hab)
  · rintro ⟨_, h | h⟩
    · rw [← inventory, List.mem_toFinset, List.mem_map]
      exact ⟨(x.val, y.val), h, rfl⟩
    · rw [← inventory, List.mem_toFinset, List.mem_map]
      exact ⟨(y.val, x.val), h, Sym2.eq_swap⟩

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

/-! ## The simultaneous prescribed subdivision and the actual selected graph -/

/-- The route's final graph is the actual selected induced finite graph, via
the reviewed induced graph isomorphism. -/
def selectedToRoutedReducedIso (q : ℕ) :
    Reduced (rectangle.induce selected) q ≅ Reduced RoutedGraph q :=
  (graphReducedIso inducedIso q).symm

/-- Pair injectivity on the actual Original subtype follows from the
routing supplier's injectivity on the underlying Nat labels. -/
theorem routeEndpointPairInjective :
    Function.Injective (fun e : Edge =>
      s(subdivision.left e, subdivision.right e)) := by
  intro e f h
  apply endpoint_pair_injective
  change s((route e).left, (route e).right) =
    s((route f).left, (route f).right)
  simpa only [Sym2.map_mk, subdivision] using congrArg
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
    simpa only [two_zsmul, two_nsmul] using selectedSingularClass_nonzero_killed_by_two.2
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

/-- The positive-order hereditary extension asked in Question 32.
The sourceSW convention quantifies over nonempty induced sets. -/
def claim : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m →
    HereditaryLexicographicProduct.sourceSW.{0, v}
      (LatticeRouting.strongProduct (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph m))

/-- The nonempty selected graph refutes the hereditary extension. -/
theorem result : ¬ claim.{v} := by
  intro h
  exact rectangle_not_sourceSW (h 9337 9061 (by decide) (by decide))

/-- Closed utility enrollment of the universe-zero instance of `claim`.
This administrative declaration does not replace the arbitrary-universe
claim or supply the mathematical scope of the counterexample. -/
def utilityClaim : Prop := claim.{0}

/-- The closed refutation required by the utility interface, enrolled from
the existing arbitrary-universe `result`. This is administrative support,
not an additional mathematical result. -/
theorem utilityRefutation : ¬ utilityClaim := result.{0}

end D5.S3.Geometry.KingFinalComposition
