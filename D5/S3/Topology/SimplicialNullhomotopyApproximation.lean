/- GID: D5/S3/Topology/SimplicialNullhomotopyApproximation
   generality: I
   mirror-B: D5/B/S3/Topology/SimplicialNullhomotopyApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nullhomotopies give contiguity after subdividing the source. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.GeometricGraphTermination
import D5.S3.Topology.StableCategory.LebesgueStarAssignment

/-!
# Fixed-target simplicial approximation of a nullhomotopy

At every sufficiently fine ordinary subdivision, every selector supported in
the original carriers gives a map contiguous, through a finite chain, to a
constant in the fixed target.

The relative cone factor for Question 6.3 of arXiv:2609.39615 separately
requires a mixed cylinder with the original triangulation at the bottom
and its ordinary subdivision at the top. Its face prisms must triangulate
compatibly, and its top must glue to the contiguity prisms and the terminal
cone while the bottom retains the original simplicial map.
-/

namespace D5.S3.Topology.SimplicialNullhomotopyApproximation

open D5.S3.Geometry
open FiniteConeCollapse (faceSimplex realization_mem_iff)
open FiniteSimplicialJoin (Space)
open FiniteVertexCylinder (vertexPoint)
open BarycentricBaseRigidity (Contiguous faceImage)
open BarycentricGraphDistance (Face Vertex)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem)
open GeometricGraphTermination
  (cylinder_star_radius contiguous_labels_of_small_faces realizedVertexMap)
open StableCategory.LebesgueStarAssignment
  (DepthVertices depthComplex iteratedRealization iteratedRealization_coordinates
    vertexCoordinates vertexCoordinates_succ)
open Relation (ReflTransGen)
open scoped BigOperators ContinuousMap unitInterval

open private contiguous_of_original_support exists_vertex_in_star
  linearMap_mem_faceImage mem_faceImage_iff from D5.S3.Topology.GeometricGraphTermination
open private depthFintype depthDecEq iterated_vertex_mesh_of_card_le from
  D5.S3.Topology.StableCategory.LebesgueStarAssignment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable {A : PreAbstractSimplicialComplex X} {K : PreAbstractSimplicialComplex Y}

/-- Every coordinate outside the iterated original support of a simplex
vanishes at each of its vertices. The induction holds for any finite family
of depth vertices. -/
private theorem vertexCoordinates_eq_zero_of_not_mem_originalSupport (n : ℕ) :
    ∀ {s : Finset (DepthVertices A n)} {a : DepthVertices A n}, a ∈ s →
      ∀ {x : X}, x ∉ originalSupport A n s → vertexCoordinates A n a x = 0 := by
  induction n with
  | zero =>
    intro s a ha x hx
    change x ∉ s at hx
    change Pi.single (M := fun _ : X => ℝ) a 1 x = 0
    apply Pi.single_eq_of_ne
    intro hxa
    subst x
    exact hx ha
  | succ n ih =>
    intro s
    change Finset (Face (depthComplex A n)) at s
    intro a
    change Face (depthComplex A n) at a
    intro ha x hx
    have hne := ((depthComplex A n).isRelLowerSet_faces a.property).1
    rw [vertexCoordinates_succ, Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        (a.val.sum_centroidWeights_eq_one_of_nonempty ℝ hne)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro v hv
    let : DecidableEq (DepthVertices A n) := Classical.decEq _
    change x ∉ originalSupport A n (s.biUnion Subtype.val) at hx
    have hvUnion : v ∈ s.biUnion Subtype.val :=
      Finset.subset_biUnion_of_mem Subtype.val ha hv
    rw [ih hvUnion hx, mul_zero]

/-- A nullhomotopy of the affine realization into a fixed finite target
gives a common subdivision threshold and a common final vertex for all
original-support selectors. -/
theorem realized_simplicial_map_contracts
    (fallback : Vertex K) (f : Vertex A → Vertex K)
    (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K)
    (q : Space K)
    (H : (realizedVertexMap fallback f hf).Homotopy (ContinuousMap.const (Space A) q)) :
    ∃ (base : Vertex K) (d : ℕ), ∀ m, d ≤ m →
      ∀ select : Vertex (depthComplex A m) → Vertex A,
        (∀ x, (select x).val ∈ originalSupport A m {x.val}) →
        ReflTransGen Contiguous (f ∘ select) (fun _ => base) := by
  obtain ⟨base, hq⟩ := exists_vertex_in_star q
  let contraction := FiniteVertexOpenStar.contraction K base.val base.property
  let extension : (ContinuousMap.const (Space A) q).Homotopy
      (ContinuousMap.const (Space A) (vertexPoint K base.val base.property)) :=
    { toFun := fun z => (contraction (z.1, ⟨q, hq⟩)).val
      continuous_toFun := continuous_subtype_val.comp (contraction.continuous.comp
        (continuous_fst.prodMk continuous_const))
      map_zero_left := fun _ => congrArg Subtype.val (contraction.toHomotopy.apply_zero ⟨q, hq⟩)
      map_one_left := fun _ => congrArg Subtype.val (contraction.toHomotopy.apply_one ⟨q, hq⟩) }
  let extended := H.trans extension
  obtain ⟨δ, hδ, label, hlabel⟩ := cylinder_star_radius extended.toContinuousMap
  let D := Fintype.card X + 1
  have hD : 0 < D := Nat.succ_pos _
  have dimension (s : Finset X) (_ : s ∈ A) : s.card ≤ D :=
    (Finset.card_le_univ s).trans (Nat.le_succ _)
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hD)
  have hfactor_nonneg : 0 ≤ 1 - 1 / (D : ℝ) :=
    sub_nonneg.mpr ((div_le_one hDpos).2 hDone)
  have hfactor_lt_one : 1 - 1 / (D : ℝ) < 1 := sub_lt_self _ (one_div_pos.mpr hDpos)
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hδ hfactor_lt_one
  refine ⟨base, d, ?_⟩
  intro m hm select hselect
  have hpow : (1 - 1 / (D : ℝ)) ^ m < δ :=
    (pow_le_pow_of_le_one hfactor_nonneg hfactor_lt_one.le hm).trans_lt hd
  let : Fintype (DepthVertices A m) := depthFintype A m
  let : DecidableEq (DepthVertices A m) := depthDecEq A m
  let position (x : Vertex (depthComplex A m)) : Space A :=
    iteratedRealization A m (vertexPoint (depthComplex A m) x.val x.property)
  have hcoord (x : Vertex (depthComplex A m)) :
      (position x).val = vertexCoordinates A m x.val :=
    iteratedRealization_coordinates A m (vertexPoint (depthComplex A m) x.val x.property)
  have hsmall (s : Finset (DepthVertices A m)) (hs : s ∈ depthComplex A m)
      (x y : Vertex (depthComplex A m)) (hx : x.val ∈ s) (hy : y.val ∈ s) :
      dist (position x) (position y) < δ := by
    change dist (position x).val (position y).val < δ
    rw [hcoord x, hcoord y]
    exact (iterated_vertex_mesh_of_card_le A hD dimension m s hs x.val hx y.val hy).trans_lt hpow
  let bottom (x : Vertex (depthComplex A m)) :=
    faceImage f (originalSupport_mem m x.property)
  have hbottom (x : Vertex (depthComplex A m)) (y : Y)
      (hy : 0 < (extended.toContinuousMap (0, position x)).val y) : y ∈ bottom x := by
    have hp : (position x).val ∈ faceSimplex (originalSupport A m {x.val}) := by
      obtain ⟨_, _, hcoords⟩ := (realization_mem_iff A _).mp (position x).property
      refine ⟨hcoords.1, hcoords.2.1, ?_⟩
      intro w hw
      rw [hcoord x]
      exact vertexCoordinates_eq_zero_of_not_mem_originalSupport m
        (Finset.mem_singleton_self x.val) hw
    have himage : ((realizedVertexMap fallback f hf) (position x)).val ∈
        faceSimplex (bottom x) :=
      linearMap_mem_faceImage fallback f (originalSupport_mem m x.property) hp
    change 0 < (extended (0, position x)).val y at hy
    rw [extended.apply_zero] at hy
    by_contra hn
    exact (ne_of_gt hy) (himage.2.2 y hn)
  obtain ⟨N, row, hfirst, hlast, hstep⟩ :=
    contiguous_labels_of_small_faces extended.toContinuousMap hδ label hlabel position hsmall
      bottom hbottom base extended.apply_one
  have hinit : Contiguous (f ∘ select) (row 0) := by
    apply contiguous_of_original_support hf _ hfirst
    intro x
    exact (mem_faceImage_iff f _).mpr ⟨select x, hselect x, rfl⟩
  have hchain (j : ℕ) (hj : j ≤ N) : ReflTransGen Contiguous (row 0) (row j) := by
    induction j with
    | zero => exact .refl
    | succ j ih =>
      exact (ih (by omega)).tail (hstep j (by omega))
  exact (ReflTransGen.single hinit).trans (hlast ▸ hchain N le_rfl)

end

end D5.S3.Topology.SimplicialNullhomotopyApproximation
