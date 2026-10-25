import CFMPGenericEndpoint1147Transient
import Mathlib.Topology.Homeomorph.Quotient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open private sigma_face sigma_inverse paired_twice from CFMPRawFaceCapSlice1053Transient
open private saturated_restriction from CFMPGenericEndpoint1147Transient
variable {T : Type*}

-- Uncompiled temporary candidate, with the original carrier and generators.
def Neighborhood (P : RawFacePairing T) {ν : Vertex P} (d : Dart T) :
    Set (Point P ν) :=
  {x | ∃ k : Fin 4, 1 / 2 < x.val.2 k ∧ DartRelated P d (x.val.1,k)}

private theorem move_inverse (P : RawFacePairing T) (f : Fin 4) (x : Raw T) :
    move P (P.facePair (x.1.1,f)).2 (move P f x) = x := by
  change (((P.facePair (P.facePair (x.1.1,f))).1,
      sigma P (P.facePair (x.1.1,f)) (sigma P (x.1.1,f) x.1.2)),
    fun i => x.2 ((sigma P (x.1.1,f)).symm
      ((sigma P (P.facePair (x.1.1,f))).symm i))) = x
  rw [paired_twice, sigma_inverse]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

theorem step_symmetric (P : RawFacePairing T) {ν : Vertex P}
    {x y : Point P ν} (h : Step P x y) : Step P y x := by
  obtain ⟨f,hfj,hzero,hy⟩ := h
  let s := sigma P (x.val.1.1,f)
  let g := (P.facePair (x.val.1.1,f)).2
  have hg : g = s f := (sigma_face P (x.val.1.1,f)).symm
  refine ⟨g,?_,?_,?_⟩
  · rw [hy]
    change g ≠ s x.val.1.2
    rw [hg]
    exact s.injective.ne hfj
  · rw [hy]
    change x.val.2 (s.symm g) = 0
    rw [hg, Equiv.symm_apply_apply]
    exact hzero
  · rw [hy]
    exact (move_inverse P f x.val).symm

theorem step_neighborhood (P : RawFacePairing T) {ν : Vertex P}
    (d : Dart T) {x y : Point P ν} (h : Step P x y)
    (hx : x ∈ Neighborhood P d) : y ∈ Neighborhood P d := by
  obtain ⟨f,hfj,hzero,hy⟩ := h
  obtain ⟨k,hk,hd⟩ := hx
  let s := sigma P (x.val.1.1,f)
  have hfk : f ≠ k := by
    intro hfk
    subst k
    linarith
  refine ⟨s k,?_,?_⟩
  · rw [hy]
    change 1 / 2 < x.val.2 (s.symm (s k))
    simpa only [Equiv.symm_apply_apply] using hk
  · have he : DartStep P (x.val.1,k) (y.val.1,s k) := by
      refine ⟨f,hfj,hfk,?_⟩
      rw [hy]
      rfl
    exact hd.trans _ _ _ (Relation.EqvGen.rel _ _ he)

theorem strict_neighborhood_saturated (P : RawFacePairing T) {ν : Vertex P}
    (d : Dart T) {x y : Point P ν} (h : Related P x y) :
    x ∈ Neighborhood P d ↔ y ∈ Neighborhood P d := by
  induction h with
  | rel x y h => exact ⟨step_neighborhood P d h,
      step_neighborhood P d (step_symmetric P h)⟩
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem strict_chain_reflection (P : RawFacePairing T) {ν : Vertex P}
    (d : Dart T) (x y : ↥(Neighborhood P (ν := ν) d)) :
    Related P x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Neighborhood P (ν := ν) d) =>
        Step P a.val b.val) x y :=
  saturated_restriction (Step P) (Neighborhood P d)
    (fun h => strict_neighborhood_saturated P d h) x y

section Topology
variable [TopologicalSpace T] [DiscreteTopology T]

abbrev PointQuotient (P : RawFacePairing T) (ν : Vertex P) :=
  Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))

def quotientNeighborhood (P : RawFacePairing T) {ν : Vertex P} (d : Dart T) :
    Set (PointQuotient P ν) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) '' Neighborhood P d

theorem neighborhood_open (P : RawFacePairing T) {ν : Vertex P} (d : Dart T) :
    IsOpen (Neighborhood P (ν := ν) d) := by
  have he : Neighborhood P (ν := ν) d = ⋃ k : Fin 4,
      {y : Point P ν | 1 / 2 < y.val.2 k} ∩
        {y | DartRelated P d (y.val.1,k)} := by
    ext y
    simp only [Neighborhood,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [he]
  apply isOpen_iUnion
  intro k
  apply IsOpen.inter
  · exact isOpen_lt continuous_const
      ((continuous_apply k).comp (continuous_snd.comp continuous_subtype_val))
  · exact (isOpen_discrete {a : T × Fin 4 | DartRelated P d (a,k)}).preimage
      (continuous_fst.comp continuous_subtype_val)

theorem actual_open_quotient_neighborhood (P : RawFacePairing T) {ν : Vertex P}
    (d : Dart T) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
        quotientNeighborhood P d = Neighborhood P d) ∧
    IsOpen (quotientNeighborhood P (ν := ν) d) ∧
    Topology.IsQuotientMap ((quotientNeighborhood P (ν := ν) d).restrictPreimage
      (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν))))) := by
  have hs : (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
      quotientNeighborhood P d = Neighborhood P d := by
    ext y
    constructor
    · rintro ⟨z,hz,he⟩
      exact (strict_neighborhood_saturated P d (Quotient.exact he)).mp hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  have ho : IsOpen (quotientNeighborhood P (ν := ν) d) := by
    apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
    rw [hs]
    exact neighborhood_open P d
  exact ⟨hs,ho,isQuotientMap_quotient_mk'.restrictPreimage_isOpen ho⟩
end Topology
end D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.step_symmetric,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.step_neighborhood,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.strict_neighborhood_saturated,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.strict_chain_reflection,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.neighborhood_open,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.actual_open_quotient_neighborhood] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1191 endpoint fan target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1191 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1191 CHECKED {name} axioms={axioms}"
