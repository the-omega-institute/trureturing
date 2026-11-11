/- GID: D5/S3/Geometry/FinitePathIndependence
   generality: G
   mirror-B: D5/B/S3/Geometry/FinitePathIndependence
   mirror-E: none(waiver:native-path-classification)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Exact modulo-three homotopy classification of native path independence realizations. -/
import D5.S3.Geometry.FiniteForestIndependence

/-!
# Native path independence realizations

The original `Fin n` labels give an explicit residual path after deleting the
closed neighborhood of the penultimate vertex. Three-vertex reduction, the
empty augmented join, and induction give the exact sphere dimensions.

This is the classical classification of Ehrenborg--Hetyei, The topology of the
independence complex, Proposition 6.2(ii) and Corollary 6.3,
DOI 10.1016/j.ejc.2005.04.010. The native empty realization is separate.
-/

noncomputable section
open Set Topology ContinuousMap

namespace D5.S3.Geometry.FinitePathIndependence

open FiniteCoordinateTruncation FiniteGraphVertexSubstitution
open FiniteSimplicialJoin FiniteForestIndependence FiniteComponentClosure
open private disjointGraph from D5.S3.Geometry.FiniteGraphVertexSubstitution
open private empty_faces join_contractible disjoint_complex edge_complex
  from D5.S3.Geometry.FiniteForestIndependence
open private joinCongr from D5.S3.Geometry.FiniteComponentClosure.Transport

private abbrev pathSpace (n : ℕ) := Ispace (SimpleGraph.pathGraph n)
private abbrev pathComplex (n : ℕ) :=
  (independenceComplex (SimpleGraph.pathGraph n)).toPreAbstractSimplicialComplex
local notation "X" => pathSpace
local notation "K" => pathComplex

private def endLeaf (n : ℕ) : Fin (n + 3) := ⟨n + 2, by omega⟩
private def neighbor (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩

private theorem end_adj (n : ℕ) :
    (SimpleGraph.pathGraph (n + 3)).Adj (endLeaf n) (neighbor n) := by
  exact SimpleGraph.pathGraph_adj.mpr (Or.inr rfl)

private theorem end_leaf (n : ℕ) (w : Fin (n + 3))
    (h : (SimpleGraph.pathGraph (n + 3)).Adj (endLeaf n) w) : w = neighbor n := by
  apply Fin.ext
  have := w.isLt
  simp only [SimpleGraph.pathGraph_adj, endLeaf] at h
  dsimp [neighbor]
  omega

private theorem residual_iff (n : ℕ) (i : Fin (n + 3)) :
    i ∈ residualSet (SimpleGraph.pathGraph (n + 3)) (neighbor n) ↔ i.val < n := by
  simp only [residualSet, Set.mem_ofPred_eq, SimpleGraph.pathGraph_adj,
    ne_eq, Fin.ext_iff, neighbor]
  have := i.isLt
  omega

/-- The residual bijection preserves the original natural-number labels. -/
private def residualEquiv (n : ℕ) :
    residualSet (SimpleGraph.pathGraph (n + 3)) (neighbor n) ≃ Fin n where
  toFun i := ⟨i.val.val, (residual_iff n i.val).mp i.property⟩
  invFun j := ⟨⟨j.val, by omega⟩, (residual_iff n _).mpr j.isLt⟩
  left_inv _ := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv _ := by apply Fin.ext; rfl

private def residualIso (n : ℕ) :
    (SimpleGraph.pathGraph (n + 3)).induce
      (residualSet (SimpleGraph.pathGraph (n + 3)) (neighbor n)) ≃g
        SimpleGraph.pathGraph n where
  toEquiv := residualEquiv n
  map_rel_iff' := by
    intro a b
    change (SimpleGraph.pathGraph n).Adj (residualEquiv n a) (residualEquiv n b) ↔
      (SimpleGraph.pathGraph (n + 3)).Adj a.val b.val
    simp only [SimpleGraph.pathGraph_adj]
    rfl

/-- Transport both tagged blocks of the augmented join, including n = 0. -/
private def residualJoinHomeomorph (n : ℕ) :
    Space (simplicialJoin
      (independenceComplex ((SimpleGraph.pathGraph (n + 3)).induce
        (residualSet (SimpleGraph.pathGraph (n + 3)) (neighbor n)))).toPreAbstractSimplicialComplex
      twoPoints) ≃ₜ Space (simplicialJoin (K n) twoPoints) := by
  classical
  let G := (SimpleGraph.pathGraph (n + 3)).induce
    (residualSet (SimpleGraph.pathGraph (n + 3)) (neighbor n))
  let e : disjointGraph G (⊤ : SimpleGraph Bool) ≃g
      disjointGraph (SimpleGraph.pathGraph n) (⊤ : SimpleGraph Bool) := {
    toEquiv := Equiv.sumCongr (residualEquiv n) (Equiv.refl Bool)
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · exact (residualIso n).map_adj_iff
      · rfl
      · rfl
      · rfl }
  let hG := (disjoint_complex G (⊤ : SimpleGraph Bool)).trans
    (congrArg (simplicialJoin _) edge_complex)
  let hP := (disjoint_complex (SimpleGraph.pathGraph n) (⊤ : SimpleGraph Bool)).trans
    (congrArg (simplicialJoin _) edge_complex)
  exact ((Homeomorph.setCongr (congrArg FiniteConeCollapse.realization hG)).symm.trans
    (graphIsoHomeomorph e)).trans
      (Homeomorph.setCongr (congrArg FiniteConeCollapse.realization hP))

private def threeStep (n : ℕ) : X (n + 3) ≃ₕ Space (simplicialJoin (K n) twoPoints) :=
  (leafEquiv _ (endLeaf n) (neighbor n) (end_adj n) (end_leaf n)).trans
    (residualJoinHomeomorph n).toHomotopyEquiv

private theorem zero_empty : IsEmpty (X 0) := by
  refine ⟨fun x => ?_⟩
  have h := (probability _ x).2
  simp at h

private theorem one_contractible : ContractibleSpace (X 1) := by
  apply isolated_contractible _ (0 : Fin 1)
  intro w
  have : w = (0 : Fin 1) := Subsingleton.elim _ _
  subst w
  simp

private def twoSphere : X 2 ≃ₕ EuclideanSphereJoin.StdSphere 0 := by
  classical
  let G := SimpleGraph.pathGraph 2
  have ha : G.Adj (1 : Fin 2) (0 : Fin 2) := by
    simp [G, SimpleGraph.pathGraph_adj]
  have hl (w : Fin 2) (hw : G.Adj (1 : Fin 2) w) : w = 0 := by
    apply Fin.ext
    simp only [G, SimpleGraph.pathGraph_adj] at hw
    have := w.isLt
    omega
  letI : IsEmpty (residualSet G (0 : Fin 2)) := ⟨by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [residualSet, G, SimpleGraph.pathGraph_adj] at hi⟩
  exact (leafEquiv G 1 0 ha hl).trans
    (((emptyLeftJoinHomeomorph _ twoPoints (empty_faces (G.induce _))).symm.trans
      twoPointSphereHomeomorph).toHomotopyEquiv)

private def threeSphere : X 3 ≃ₕ EuclideanSphereJoin.StdSphere 0 :=
  (threeStep 0).trans (((emptyLeftJoinHomeomorph (K 0) twoPoints
    (empty_faces (SimpleGraph.pathGraph 0))).symm.trans
      twoPointSphereHomeomorph).toHomotopyEquiv)

private def ordinaryStep (n : ℕ) (hn : Nonempty (X n)) :
    X (n + 3) ≃ₕ OrdinaryJoin (X n) (Space twoPoints) :=
  (threeStep n).trans (FiniteSimplicialJoin.joinHomeomorph (K n) twoPoints hn
    ⟨twoPointSphereHomeomorph.symm (EuclideanSphereJoin.coordinatePoint 0)⟩).symm.toHomotopyEquiv

private def sphereStep {n k : ℕ} (e : X n ≃ₕ EuclideanSphereJoin.StdSphere k) :
    X (n + 3) ≃ₕ EuclideanSphereJoin.StdSphere (k + 1) := by
  let hn : Nonempty (X n) := ⟨e.invFun (EuclideanSphereJoin.coordinatePoint k)⟩
  exact (ordinaryStep n hn).trans
    ((joinCongr e twoPointSphereHomeomorph.toHomotopyEquiv).trans
      (by simpa using (EuclideanSphereJoin.sphereJoinHomeomorph k 0).toHomotopyEquiv))

private theorem contractibleStep {n : ℕ} (h : ContractibleSpace (X n)) :
    ContractibleSpace (X (n + 3)) := by
  let := h
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (X n)
  let := join_contractible (W := X n)
    (twoPointSphereHomeomorph.symm (EuclideanSphereJoin.coordinatePoint 0))
  exact (ordinaryStep n ⟨e.invFun ()⟩).contractibleSpace

/-- The complete native path classification, with exact dimensions and all small cases. -/
theorem classification :
    IsEmpty (Ispace (SimpleGraph.pathGraph 0)) ∧
    (∀ k : ℕ, Nonempty (Ispace (SimpleGraph.pathGraph (3 * (k + 1))) ≃ₕ
      EuclideanSphereJoin.StdSphere k)) ∧
    (∀ k : ℕ, ContractibleSpace (Ispace (SimpleGraph.pathGraph (3 * k + 1)))) ∧
    (∀ k : ℕ, Nonempty (Ispace (SimpleGraph.pathGraph (3 * k + 2)) ≃ₕ
      EuclideanSphereJoin.StdSphere k)) := by
  have all (k : ℕ) :
      Nonempty (X (3 * (k + 1)) ≃ₕ EuclideanSphereJoin.StdSphere k) ∧
      ContractibleSpace (X (3 * k + 1)) ∧
      Nonempty (X (3 * k + 2) ≃ₕ EuclideanSphereJoin.StdSphere k) := by
    induction k with
    | zero => exact ⟨⟨threeSphere⟩, one_contractible, ⟨twoSphere⟩⟩
    | succ k ih =>
      obtain ⟨⟨a⟩, b, ⟨c⟩⟩ := ih
      refine ⟨⟨?a⟩, ?b, ⟨?c⟩⟩
      case a => convert sphereStep a using 1 <;> congr 2 <;> omega
      case b => convert contractibleStep b using 1 <;> congr 2 <;> omega
      case c => convert sphereStep c using 1 <;> congr 2 <;> omega
  exact ⟨zero_empty, fun k => (all k).1, fun k => (all k).2.1, fun k => (all k).2.2⟩

end D5.S3.Geometry.FinitePathIndependence
