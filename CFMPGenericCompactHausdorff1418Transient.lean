import CFMPGenericClosedRelation1415Transient
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedPoint)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceClosedRelation1415Candidate
open Topology Set
open private slice_closed slice_quotient_restriction from CFMPRawFaceCapSlice1053Transient

-- Temporary applications of compact projection and normal separation.
theorem closed_quotient_map {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hR : IsClosed {ab : X × X | r ab.1 ab.2}) :
    IsClosedMap (@Quotient.mk' X r) := by
  intro C hC
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have he : (@Quotient.mk' X r) ⁻¹' ((@Quotient.mk' X r) '' C) =
      Prod.fst '' ({ab : X × X | r ab.1 ab.2} ∩ Prod.snd ⁻¹' C) := by
    ext x
    constructor
    · rintro ⟨z,hz,heq⟩
      exact ⟨(x,z),⟨Quotient.exact heq.symm,hz⟩,rfl⟩
    · rintro ⟨⟨x',z⟩,⟨hr,hz⟩,heq⟩
      dsimp at heq
      subst x'
      exact ⟨z,hz,Quotient.sound (r.symm hr)⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ (hR.inter (hC.preimage continuous_snd))

theorem compact_closed_quotient_t2 {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (r : Setoid X)
    (hR : IsClosed {ab : X × X | r ab.1 ab.2}) : T2Space (Quotient r) := by
  let q : X → Quotient r := @Quotient.mk' X r
  have hc : IsClosedMap q := closed_quotient_map r hR
  refine ⟨?_⟩
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  have hx : IsClosed {z : X | r z x} :=
    hR.preimage (continuous_id.prodMk continuous_const)
  have hy : IsClosed {z : X | r z y} :=
    hR.preimage (continuous_id.prodMk continuous_const)
  have hd : Disjoint {z : X | r z x} {z : X | r z y} := by
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hxy (Quotient.sound (r.trans (r.symm hzx) hzy))
  obtain ⟨U,V,hU,hV,hxU,hyV,hUV⟩ := normal_separation hx hy hd
  refine ⟨(q '' Uᶜ)ᶜ,(q '' Vᶜ)ᶜ,(hc _ hU.isClosed_compl).isOpen_compl,
    (hc _ hV.isClosed_compl).isOpen_compl,?_,?_,?_⟩
  · rintro ⟨z,hz,he⟩
    exact hz (hxU (Quotient.exact he))
  · rintro ⟨z,hz,he⟩
    exact hz (hyV (Quotient.exact he))
  · apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨w,rfl⟩ := Quotient.mk'_surjective z
    have hwU : w ∈ U := by
      by_contra h
      exact hzU ⟨w,h,rfl⟩
    have hwV : w ∈ V := by
      by_contra h
      exact hzV ⟨w,h,rfl⟩
    exact Set.disjoint_left.mp hUV hwU hwV

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

omit [DiscreteTopology T] in
theorem original_truncated_compact : CompactSpace (TruncatedPoint T) := by
  let S : Set (Fin 4 → ℝ) := {a |
    (∀ i, 0 ≤ a i ∧ a i ≤ 3/4) ∧ (∑ i, a i) = 1}
  have hB : IsClosed {a : Fin 4 → ℝ | ∀ i, 0 ≤ a i ∧ a i ≤ 3/4} := by
    have he : {a : Fin 4 → ℝ | ∀ i, 0 ≤ a i ∧ a i ≤ 3/4} =
        ⋂ i : Fin 4, {a : Fin 4 → ℝ | 0 ≤ a i ∧ a i ≤ 3/4} := by ext a; simp
    rw [he]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  have hS : IsClosed S := hB.inter (isClosed_eq (by fun_prop) continuous_const)
  have hK : IsCompact S :=
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 4 => (0 : ℝ))
      (fun _ : Fin 4 => (3/4 : ℝ)))).of_isClosed_subset hS (by
        intro a ha
        exact ⟨fun i => (ha.1 i).1,fun i => (ha.1 i).2⟩)
  letI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hK
  exact inferInstanceAs (CompactSpace (T × ↥S))

theorem original_truncated_quotient_t2 (P : RawFacePairing T) :
    T2Space (TruncatedQuotient P) := by
  letI : CompactSpace (TruncatedPoint T) := original_truncated_compact
  exact compact_closed_quotient_t2 _ (original_truncated_relation_closed P)

omit [DiscreteTopology T] in
theorem original_truncated_quotient_compact (P : RawFacePairing T) :
    CompactSpace (TruncatedQuotient P) := by
  letI : CompactSpace (TruncatedPoint T) := original_truncated_compact
  infer_instance

theorem original_corner_quotient_t2 (P : RawFacePairing T) (ν : Vertex P) :
    T2Space (Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))) := by
  letI : T2Space (TruncatedQuotient P) := original_truncated_quotient_t2 P
  exact (actualSliceQuotientHomeomorph P ν).symm.t2Space

theorem original_cap_t2 (P : RawFacePairing T) (ν : Vertex P) :
    T2Space ↥(quotientSlice P ν) := by
  letI : T2Space (TruncatedQuotient P) := original_truncated_quotient_t2 P
  infer_instance

theorem original_cap_compact (P : RawFacePairing T) (ν : Vertex P) :
    CompactSpace ↥(quotientSlice P ν) := by
  letI : CompactSpace (TruncatedQuotient P) := original_truncated_quotient_compact P
  have hc : IsClosed (quotientSlice P ν) :=
    isQuotientMap_quotient_mk'.isClosed_preimage.mp (by
      rw [(slice_quotient_restriction P ν).1]
      exact slice_closed P ν)
  exact isCompact_iff_compactSpace.mp hc.isCompact

end D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.closed_quotient_map,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.compact_closed_quotient_t2,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_truncated_compact,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_truncated_quotient_t2,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_truncated_quotient_compact,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_corner_quotient_t2,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_cap_t2,
      ``D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate.original_cap_compact] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1418 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1418 disallowed {ax}"
    Lean.logInfo m!"CFMP1418 CHECKED {name} axioms={axioms}"
