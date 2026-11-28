/- GID: D5/S3/Topology/StableCategory/OrderComplexNullhomotopy
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/OrderComplexNullhomotopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realization nullhomotopies give fences after maximum projections. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.BarycentricRealization
import D5.S3.Topology.SimplicialNullhomotopyApproximation
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
import Mathlib.Order.Preorder.Finite

/-!
# Maximum projections and nullhomotopy fences for order complexes

The vertices at depth `r + 1` are the nonempty faces at depth `r`. Taking
maxima successively gives an order map on that face poset. At depth `r`,
the same construction gives an original-support selector for fixed-target
simplicial approximation. Passing the resulting contiguity chain to faces
adds one round of subdivision and gives a fence beginning at the exact
composite with the maximum projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.OrderComplexNullhomotopy

open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open BarycentricBaseRigidity (faceImage sd)
open BarycentricGraphDistance (Face Vertex)
open GeometricGraphTermination (realizedVertexMap)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem)
open Relation (EqvGen)
open SimplicialNullhomotopyApproximation (realized_simplicial_map_contracts)
open StableCategory.LebesgueStarAssignment (DepthVertices depthComplex)
open StableCategory.OrdinaryContiguityLift (Simplicial face_map_fence)
open StableCategory.TerminalCarrierIteration (originalSupport_mono)
open scoped ContinuousMap

open private chainComplex map_fence from D5.S3.Topology.SubdivisionCategoricalCover
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private faceMap constant_face_image from
  D5.S3.Topology.StableCategory.OrdinaryContiguityLift

noncomputable section

variable {X Y : Type} [PartialOrder X] [PartialOrder Y]

/-- The simplicial complex of nonempty finite chains in a poset. -/
abbrev orderComplex (X : Type) [PartialOrder X] := chainComplex X

private theorem orderComplex_has_maximum (s : Face (orderComplex X)) :
    ∃ a ∈ s.val, ∀ b ∈ s.val, b ≤ a := by
  classical
  obtain ⟨a, ha⟩ := s.val.exists_maximal s.property.1
  refine ⟨a, ha.1, fun b hb => ?_⟩
  by_cases h : b = a
  · exact h.le
  · rcases s.property.2 hb ha.1 h with hba | hab
    · exact hba
    · exact ha.2 hb hab

/-- The maximum of a nonempty chain is monotone under inclusion. -/
def chainMaximum : Face (orderComplex X) →o X where
  toFun s := (orderComplex_has_maximum s).choose
  monotone' s t h := (orderComplex_has_maximum t).choose_spec.2 _
    (h (orderComplex_has_maximum s).choose_spec.1)

theorem chainMaximum_spec (s : Face (orderComplex X)) :
    chainMaximum s ∈ s.val ∧ ∀ a ∈ s.val, a ≤ chainMaximum s :=
  (orderComplex_has_maximum s).choose_spec

private theorem chainMaximum_eq_of_greatest (s : Face (orderComplex X)) {a : X}
    (ha : a ∈ s.val) (hle : ∀ b ∈ s.val, b ≤ a) : chainMaximum s = a :=
  le_antisymm (hle _ (chainMaximum_spec s).1) ((chainMaximum_spec s).2 _ ha)

private theorem subdivision_has_maximum {V : Type} {K : PreAbstractSimplicialComplex V}
    (s : Face (sd K)) : ∃ a ∈ s.val, ∀ b ∈ s.val, b ≤ a := by
  classical
  obtain ⟨a, ha, hcard⟩ :=
    Finset.exists_max_image s.val (fun f : Face K => f.val.card) s.property.1
  refine ⟨a, ha, fun b hb => ?_⟩
  by_cases he : b = a
  · exact he.le
  rcases s.property.2.1 hb ha he with h | h
  · exact h.le
  · exact (not_lt_of_ge (hcard b hb) (Finset.card_lt_card h)).elim

/-- The greatest face in a nonempty flag of faces. -/
def subdivisionMaximum {V : Type} (K : PreAbstractSimplicialComplex V) :
    Face (sd K) →o Face K where
  toFun s := (subdivision_has_maximum s).choose
  monotone' s t h := (subdivision_has_maximum t).choose_spec.2 _
    (h (subdivision_has_maximum s).choose_spec.1)

theorem subdivisionMaximum_spec {V : Type} {K : PreAbstractSimplicialComplex V}
    (s : Face (sd K)) :
    subdivisionMaximum K s ∈ s.val ∧ ∀ a ∈ s.val, a ≤ subdivisionMaximum K s :=
  (subdivision_has_maximum s).choose_spec

/-- The `(r + 1)`-fold maximum projection on the face poset at depth `r`. -/
def maximumProjection (X : Type) [PartialOrder X] :
    (r : ℕ) → Face (depthComplex (orderComplex X) r) →o X
  | 0 => chainMaximum (X := X)
  | r + 1 => (maximumProjection X r).comp (subdivisionMaximum (depthComplex (orderComplex X) r))

/-- The `r`-fold maximum projection on the vertex labels at depth `r`. -/
def vertexProjection (X : Type) [PartialOrder X] :
    (r : ℕ) → DepthVertices (orderComplex X) r → X
  | 0 => id
  | r + 1 => maximumProjection X r

private theorem maximumProjection_attained (r : ℕ) (s : Face (depthComplex (orderComplex X) r)) :
    ∃ a ∈ s.val, vertexProjection X r a = maximumProjection X r s ∧
      ∀ b ∈ s.val, vertexProjection X r b ≤ maximumProjection X r s := by
  cases r with
  | zero =>
    exact ⟨chainMaximum (X := X) s, (chainMaximum_spec (X := X) s).1, rfl,
      (chainMaximum_spec (X := X) s).2⟩
  | succ r =>
    let a := subdivisionMaximum (depthComplex (orderComplex X) r) s
    refine ⟨a, (subdivisionMaximum_spec s).1, rfl, ?_⟩
    intro b hb
    exact (maximumProjection X r).monotone ((subdivisionMaximum_spec s).2 b hb)

theorem maximumProjection_mem_originalSupport (r : ℕ)
    (s : Face (depthComplex (orderComplex X) r)) :
    maximumProjection X r s ∈ originalSupport (orderComplex X) r s.val := by
  induction r with
  | zero => exact (chainMaximum_spec (X := X) s).1
  | succ r ih =>
    let K := depthComplex (orderComplex X) r
    let a : Face K := subdivisionMaximum K s
    let : DecidableEq (DepthVertices (orderComplex X) r) := Classical.decEq _
    change maximumProjection X r a ∈
      originalSupport (orderComplex X) r (s.val.biUnion Subtype.val)
    have hsub : a.val ⊆ s.val.biUnion Subtype.val :=
      Finset.subset_biUnion_of_mem Subtype.val (subdivisionMaximum_spec s).1
    exact originalSupport_mono (orderComplex X) r hsub (ih a)

/-- Every element of a poset is a vertex of its order complex. -/
def orderVertex (x : X) : Vertex (orderComplex X) :=
  ⟨x, Finset.singleton_nonempty x, by
    simpa only [Finset.coe_singleton] using (IsChain.singleton (r := (· ≤ ·)) (a := x))⟩

/-- The iterated maximum as a vertex selector for ordinary subdivision. -/
def maximumSelector (r : ℕ) (x : Vertex (depthComplex (orderComplex X) r)) :
    Vertex (orderComplex X) :=
  orderVertex (vertexProjection X r x.val)

theorem maximumSelector_supported (r : ℕ) (x : Vertex (depthComplex (orderComplex X) r)) :
    (maximumSelector r x).val ∈ originalSupport (orderComplex X) r {x.val} := by
  cases r with
  | zero => exact Finset.mem_singleton_self x.val
  | succ r =>
    let : DecidableEq (DepthVertices (orderComplex X) r) := Classical.decEq _
    change maximumProjection X r x.val ∈
      originalSupport (orderComplex X) r (({x.val} : Finset _).biUnion Subtype.val)
    rw [Finset.singleton_biUnion]
    exact maximumProjection_mem_originalSupport r x.val

theorem maximumSelector_simplicial (r : ℕ) : Simplicial (maximumSelector (X := X) r) := by
  intro s hs
  have hsub : faceImage (maximumSelector r) hs ⊆ originalSupport (orderComplex X) r s := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff _ hs a).mp ha
    exact originalSupport_mono (orderComplex X) r (Finset.singleton_subset_iff.mpr hx)
      (maximumSelector_supported r x)
  have hne : (faceImage (maximumSelector r) hs).Nonempty :=
    by
      classical
      unfold faceImage
      exact ((depthComplex (orderComplex X) r).isRelLowerSet_faces hs).1.attach.image _
  exact ((orderComplex X).isRelLowerSet_faces (originalSupport_mem r hs)).2 hsub hne

/-- The simplicial vertex map induced by an order homomorphism. -/
def orderHomVertices (f : X →o Y) (x : Vertex (orderComplex X)) : Vertex (orderComplex Y) :=
  orderVertex (f x.val)

theorem orderHomVertices_simplicial (f : X →o Y) : Simplicial (orderHomVertices f) := by
  intro s hs
  refine ⟨?_, ?_⟩
  · classical
    unfold faceImage
    exact hs.1.attach.image _
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff (orderHomVertices f) hs a).mp ha
    obtain ⟨y, hy, rfl⟩ := (mem_faceImage_iff (orderHomVertices f) hs b).mp hb
    have hxy : x.val ≠ y.val := fun h => hab (congrArg (fun z : X => f z) h)
    exact (hs.2 hx hy hxy).imp (fun h => f.monotone h) (fun h => f.monotone h)

/-- Taking the target maximum of the image of a face applies `f` to the
iterated maximum of that face. -/
theorem chainMaximum_comp_faceMap (f : X →o Y) (r : ℕ)
    (hf : Simplicial (orderHomVertices f ∘ maximumSelector r)) :
    chainMaximum.comp (faceMap _ hf) = f.comp (maximumProjection X r) := by
  ext s
  change chainMaximum (faceMap _ hf s) = f (maximumProjection X r s)
  obtain ⟨a, ha, he, hle⟩ := maximumProjection_attained r s
  apply chainMaximum_eq_of_greatest
  · let x : Vertex (depthComplex (orderComplex X) r) :=
      ⟨a, ((depthComplex (orderComplex X) r).isRelLowerSet_faces s.property).2
        (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _)⟩
    exact (mem_faceImage_iff _ s.property _).mpr
      ⟨x, ha, congrArg (fun z : X => f z) he⟩
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff _ s.property b).mp hb
    exact f.monotone (hle x.val hx)

private theorem chainMaximum_comp_const_faceMap {V : Type} {K : PreAbstractSimplicialComplex V}
    (b : Vertex (orderComplex Y)) (hb : Simplicial (fun _ : Vertex K => b)) :
    chainMaximum.comp (faceMap _ hb) = OrderHom.const (Face K) b.val := by
  ext s
  change chainMaximum (faceMap _ hb s) = b.val
  have hface : (faceMap _ hb s).val = {b.val} := constant_face_image b s.property
  apply chainMaximum_eq_of_greatest
  · rw [hface]
    exact Finset.mem_singleton_self _
  · intro y hy
    rw [hface] at hy
    exact (Finset.mem_singleton.mp hy).le

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The affine realization of the map of order complexes. -/
def realizedOrderHom (fallback : Y) (f : X →o Y) :
    C(Space (orderComplex X), Space (orderComplex Y)) :=
  realizedVertexMap (orderVertex fallback) (orderHomVertices f) (orderHomVertices_simplicial f)

/-- If the realization of `f` is nullhomotopic, then at every sufficiently
large depth `r` the order maps from the face poset at depth `r` to `Y`
have a finite fence from `f` composed with the `(r + 1)`-fold maximum
projection to a constant. -/
theorem order_map_fence_of_nullhomotopy (fallback : Y) (f : X →o Y) (q : Space (orderComplex Y))
    (H : (realizedOrderHom fallback f).Homotopy (ContinuousMap.const (Space (orderComplex X)) q)) :
    ∃ (base : Y) (d : ℕ), ∀ r, d ≤ r →
      EqvGen (· ≤ ·) (f.comp (maximumProjection X r))
        (OrderHom.const (Face (depthComplex (orderComplex X) r)) base) := by
  obtain ⟨b, d, h⟩ := realized_simplicial_map_contracts (orderVertex fallback)
    (orderHomVertices f) (orderHomVertices_simplicial f) q H
  refine ⟨b.val, d, fun r hr => ?_⟩
  let K := depthComplex (orderComplex X) r
  have hf : Simplicial (orderHomVertices f ∘ maximumSelector r) :=
    (orderHomVertices_simplicial f).comp (maximumSelector_simplicial r)
  have hb : Simplicial (fun _ : Vertex K => b) := by
    intro s hs
    rw [constant_face_image b hs]
    exact b.property
  have hfence := face_map_fence hf hb (h r hr (maximumSelector r) (maximumSelector_supported r))
  have hmax : EqvGen (· ≤ ·) (chainMaximum.comp (faceMap _ hf))
      (chainMaximum.comp (faceMap _ hb)) :=
    map_fence (fun g : Face K →o Face (orderComplex Y) => chainMaximum.comp g)
      (fun _ _ hfg => .rel _ _ (OrderHom.comp_mono le_rfl hfg)) hfence
  rw [chainMaximum_comp_faceMap f r hf, chainMaximum_comp_const_faceMap b hb] at hmax
  exact hmax

end

end D5.S3.Topology.OrderComplexNullhomotopy
