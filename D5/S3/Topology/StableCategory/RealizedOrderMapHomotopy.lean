/- GID: D5/S3/Topology/StableCategory/RealizedOrderMapHomotopy
   generality: I
   mirror-B: none(waiver:consumed-by-weak-category-one-reduction)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite order-map fences realize to homotopies. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrderComplexNullhomotopy
import D5.S3.Topology.DescendingClosureContiguity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.RealizedOrderMapHomotopy

open D5.S3.Geometry.FiniteConeCollapse (faceSimplex realization realization_mem_iff)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open BarycentricBaseRigidity (Contiguous faceImage)
open BarycentricGraphDistance (Vertex)
open GeometricGraphTermination (realizedVertexMap)
open OrderComplexNullhomotopy
  (orderComplex orderVertex orderHomVertices orderHomVertices_simplicial realizedOrderHom)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open StableCategory.OrdinaryContiguityLift (Simplicial)
open Relation (EqvGen)
open scoped ContinuousMap unitInterval

open private extendVertexMap linearMap_mem_faceImage mem_faceImage_iff contiguous_of_face_carriers from
  D5.S3.Topology.GeometricGraphTermination
open private convex_faceSimplex faceSimplex_mono from D5.S3.Geometry.FiniteConeCollapse

noncomputable section

variable {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private def contiguousRealizationHomotopy
    {A : PreAbstractSimplicialComplex X} {K : PreAbstractSimplicialComplex Y}
    (fallback : Vertex K) (f g : Vertex A → Vertex K)
    (hf : Simplicial f) (hg : Simplicial g) (h : Contiguous f g) :
    (realizedVertexMap fallback f hf).Homotopy (realizedVertexMap fallback g hg) := by
  let F := realizedVertexMap fallback f hf
  let G := realizedVertexMap fallback g hg
  let segment (z : I × Space A) : Y → ℝ :=
    (1 - (z.1 : ℝ)) • (F z.2).val + (z.1 : ℝ) • (G z.2).val
  have hsegment (z : I × Space A) : segment z ∈ realization K := by
    obtain ⟨s, hs, hp⟩ := (realization_mem_iff A _).mp z.2.property
    let t : Finset Y := by
      letI : DecidableEq Y := Classical.decEq Y
      exact faceImage f hs ∪ faceImage g hs
    have ht := h s hs
    change t ∈ K at ht
    refine (realization_mem_iff K _).mpr ⟨t, ht, ?_⟩
    have hF : (F z.2).val ∈ faceSimplex t :=
      faceSimplex_mono (show faceImage f hs ⊆ t from
        @Finset.subset_union_left Y (Classical.decEq Y) _ _)
        (linearMap_mem_faceImage fallback f hs hp)
    have hG : (G z.2).val ∈ faceSimplex t :=
      faceSimplex_mono (show faceImage g hs ⊆ t from
        @Finset.subset_union_right Y (Classical.decEq Y) _ _)
        (linearMap_mem_faceImage fallback g hs hp)
    exact convex_faceSimplex t hF hG
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))
  have ht : Continuous (fun z : I × Space A => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hF : Continuous (fun z : I × Space A => (F z.2).val) :=
    continuous_subtype_val.comp (F.continuous.comp continuous_snd)
  have hG : Continuous (fun z : I × Space A => (G z.2).val) :=
    continuous_subtype_val.comp (G.continuous.comp continuous_snd)
  exact
    { toFun := fun z => ⟨segment z, hsegment z⟩
      continuous_toFun := (((continuous_const.sub ht).smul hF).add (ht.smul hG)).subtype_mk _
      map_zero_left := fun p => Subtype.ext (show segment (0, p) = (F p).val by simp [segment])
      map_one_left := fun p => Subtype.ext (show segment (1, p) = (G p).val by simp [segment]) }

variable [PartialOrder X] [PartialOrder Y]

private theorem contiguous_of_common_chain {f g : X →o Y}
    (h : ∀ s : Set X, IsChain (· ≤ ·) s → IsChain (· ≤ ·) (f '' s ∪ g '' s)) :
    Contiguous (orderHomVertices f) (orderHomVertices g) := by
  classical
  apply contiguous_of_face_carriers
  intro s hs
  let t := s.image f ∪ s.image g
  have hset : (t : Set Y) = f '' (s : Set X) ∪ g '' (s : Set X) := by
    simp [t, Finset.coe_union, Finset.coe_image]
  refine ⟨t, ⟨(Finset.image_nonempty.mpr hs.1).mono Finset.subset_union_left, ?_⟩, ?_⟩
  · rw [hset]
    exact h s hs.2
  · intro x hx
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)⟩

/-- A finite fence of order maps gives a homotopy of their affine realizations. -/
theorem homotopic_of_fence (fallback : Y) {f g : X →o Y}
    (h : EqvGen (· ≤ ·) f g) :
    (realizedOrderHom fallback f).Homotopic (realizedOrderHom fallback g) := by
  classical
  induction h with
  | rel f g hfg =>
    let rank (x : X) := (Finset.univ.filter (· ≤ x)).card
    have hstrict : StrictMono rank := by
      intro x y hxy
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2.trans hxy.le⟩
      · intro he
        have hy : y ∈ Finset.univ.filter (· ≤ y) := by simp
        rw [← he] at hy
        exact (not_le_of_gt hxy) (Finset.mem_filter.mp hy).2
    have hbound (x : X) : rank x ≤ Fintype.card X := Finset.card_le_univ _
    obtain ⟨F, h0, hlast, _, _, hstep⟩ :=
      exists_relative_contiguity_of_le rank hstrict g f
        (OrderHom.le_def.mp hfg) (Fintype.card X) hbound
    have path (n : ℕ) :
        (realizedOrderHom fallback (F 0)).Homotopic (realizedOrderHom fallback (F n)) := by
      induction n with
      | zero => exact .refl _
      | succ n ih =>
        have hc := contiguous_of_common_chain (hstep n)
        let H := contiguousRealizationHomotopy (orderVertex fallback)
          (orderHomVertices (F n)) (orderHomVertices (F (n + 1)))
          (orderHomVertices_simplicial _) (orderHomVertices_simplicial _) hc
        exact ih.trans ⟨H⟩
    simpa only [h0, hlast] using (path (Fintype.card X + 1)).symm
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem realizedOrderHom_val (fallback : Y) (f : X →o Y) (p : Space (orderComplex X)) :
    (realizedOrderHom fallback f p).val = FunOnFinite.linearMap ℝ ℝ f p.val := by
  change FunOnFinite.linearMap ℝ ℝ
    (extendVertexMap (orderVertex fallback) (orderHomVertices f)) p.val = _
  have hf : extendVertexMap (orderVertex fallback) (orderHomVertices f) = f := by
    funext x
    unfold extendVertexMap
    exact dite_eq_left (show ({x} : Finset X) ∈ orderComplex X from (orderVertex x).property)
  rw [hf]

theorem realizedOrderHom_id (fallback : X) :
    realizedOrderHom fallback (OrderHom.id : X →o X) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rw [realizedOrderHom_val]
  exact congrArg (fun L : (X → ℝ) →ₗ[ℝ] (X → ℝ) => L p.val)
    (FunOnFinite.linearMap_id ℝ ℝ X)

variable [Fintype Z] [DecidableEq Z] [PartialOrder Z]

theorem realizedOrderHom_comp (fallbackY : Y) (fallbackZ : Z) (f : X →o Y) (g : Y →o Z) :
    realizedOrderHom fallbackZ (g.comp f) =
      (realizedOrderHom fallbackZ g).comp (realizedOrderHom fallbackY f) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rw [realizedOrderHom_val]
  change FunOnFinite.linearMap ℝ ℝ (g ∘ f) p.val =
    (realizedOrderHom fallbackZ g (realizedOrderHom fallbackY f p)).val
  rw [realizedOrderHom_val, realizedOrderHom_val, FunOnFinite.linearMap_comp]
  rfl

end

end D5.S3.Topology.RealizedOrderMapHomotopy
