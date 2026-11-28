import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.WeaklyContractibleFactor

/-! Nullhomotopy is preserved by passage to the face-poset inclusion. -/

noncomputable section

open ContinuousMap Set
open scoped ContinuousMap Classical
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Geometry.MappedRealization (homeomorphMap)
open D5.S3.Topology.BarycentricGraphDistance (Face)
open D5.S3.Topology.BarycentricNeighborhoodIteration (subdivision subdivision_full)
open D5.S3.Topology.BarycentricRealization (subcomplex_nullhomotopic_iff)
open D5.S3.Topology.OrderComplexNullhomotopy (orderComplex realizedOrderHom)

namespace D5.S3.Topology.FaceInclusionNullhomotopy

open private mem_map_orderComplex_iff from D5.S3.Topology.StableCategory.OrderComplexCylinderUnion
open private orderComplex_face_eq_sd from D5.S3.Topology.StableCategory.MaximumProjectionRealization
open private realizedOrderHom_val from D5.S3.Topology.StableCategory.RealizedOrderMapHomotopy

variable {V : Type} [Fintype V] [DecidableEq V]
variable {A K : PreAbstractSimplicialComplex V}

private def faceEmbedding (h : A ≤ K) : Face A ↪o Face K :=
  OrderEmbedding.ofMapLEIff (fun a => (⟨a.val, h a.property⟩ : Face K)) (fun _ _ => Iff.rfl)

private theorem map_orderComplex_faceEmbedding (h : A ≤ K) :
    (orderComplex (Face A)).map (faceEmbedding h) = subdivision K A := by
  apply SetLike.ext
  intro s
  rw [mem_map_orderComplex_iff, orderComplex_face_eq_sd]
  constructor
  · rintro ⟨hs, hrange⟩
    refine ⟨hs.1, hs.2.1, fun f hf => ?_⟩
    obtain ⟨a, ha⟩ := hrange hf
    exact (congrArg Subtype.val ha) ▸ a.property
  · intro hs
    refine ⟨⟨hs.1, hs.2.1, fun f _ => f.property⟩, fun f hf => ?_⟩
    exact ⟨⟨f.val, hs.2.2 f hf⟩, Subtype.ext rfl⟩

/-- The face-poset inclusion has nullhomotopic realization whenever the original
subcomplex inclusion does. The local factors can therefore be taken before any
further subdivision of the ambient poset. -/
theorem face_inclusion_nullhomotopic (h : A ≤ K) (p : Face K)
    (H : (realizationInclusion h).Nullhomotopic) :
    (realizedOrderHom p (faceEmbedding h).toOrderHom).Nullhomotopic := by
  let k : C(D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace K A, Space A) :=
    ⟨fun x => ⟨x.val.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have H' : (ContinuousMap.subtypeVal
      (D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace K A)).Nullhomotopic :=
    H.comp_left k
  have H'' := (subcomplex_nullhomotopic_iff K A).mpr H'
  let e := homeomorphMap (orderComplex (Face A)) (faceEmbedding h).toEmbedding
  let e' := Homeomorph.setCongr (congrArg D5.S3.Geometry.FiniteConeCollapse.realization
    (map_orderComplex_faceEmbedding h))
  let hSub : subdivision K A ≤ D5.S3.Topology.BarycentricBaseRigidity.sd K :=
    (subdivision_full K A).1
  let s : C(Space (orderComplex (Face A)),
      D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace
        (D5.S3.Topology.BarycentricBaseRigidity.sd K) (subdivision K A)) :=
    ⟨fun x => ⟨realizationInclusion hSub
      (e' (e x)), (e' (e x)).property⟩,
      ((realizationInclusion hSub).continuous.comp
        (e'.continuous.comp e.continuous)).subtype_mk _⟩
  let t := Homeomorph.setCongr (congrArg D5.S3.Geometry.FiniteConeCollapse.realization
    (orderComplex_face_eq_sd K).symm)
  let tMap : C(Space (D5.S3.Topology.BarycentricBaseRigidity.sd K),
      Space (orderComplex (Face K))) := ⟨t, t.continuous⟩
  have transported := (H''.comp_left s).comp_right tMap
  have eq : tMap.comp ((ContinuousMap.subtypeVal _).comp s) =
      realizedOrderHom p (faceEmbedding h).toOrderHom := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change FunOnFinite.linearMap ℝ ℝ (faceEmbedding h) x.val = _
    rw [realizedOrderHom_val]
    rfl
  exact eq ▸ transported

end D5.S3.Topology.FaceInclusionNullhomotopy
