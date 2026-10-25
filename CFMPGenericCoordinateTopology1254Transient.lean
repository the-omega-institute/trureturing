import CFMPGenericNeighborhoodCoordinates1244Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing Occurrence incomingFace outgoingFace)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
open D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate
open D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (Sector)
open private dominant_unique from D5.S3.Geometry.Gluing.ActualLinkAffineFan
variable {T : Type*}

theorem inverse_component_fiber (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T)
    (y : ↥(Neighborhood P (ν := label P d0.val.1) d0.val)) (i : Component P d0) :
    ((coordinateEquiv P r d0).symm y).1 = i ↔
      y.val.val.1 = i.val.val.1 ∧ 1/2 < y.val.val.2 i.val.val.2 := by
  obtain ⟨⟨j,p⟩,rfl⟩ := (actual_component_strict_coordinates P r d0).2 y
  change ((coordinateEquiv P r d0).symm (coordinateEquiv P r d0 (j,p))).1 = i ↔ _
  rw [Equiv.symm_apply_apply]
  change j = i ↔ j.val.val.1 = i.val.val.1 ∧ 1/2 < beta r j.val p.val i.val.val.2
  constructor
  · rintro rfl
    exact ⟨rfl,(beta_actual_simplex r j.val p).2.2⟩
  · rintro ⟨hc,ht⟩
    have hb := beta_actual_simplex r j.val p
    have hk : j.val.val.2 = i.val.val.2 :=
      dominant_unique _ hb.1 hb.2.1 hb.2.2 ht
    exact Subtype.ext (Subtype.ext (Prod.ext hc hk))

section Topology
variable [TopologicalSpace T] [DiscreteTopology T]

local instance componentTopology (P : RawFacePairing T) (d0 : OrderedEnd T) :
    TopologicalSpace (Component P d0) :=
  inferInstanceAs (TopologicalSpace {d : OrderedEnd T //
    D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.DartRelated P d0.val d.val})

local instance componentDiscrete (P : RawFacePairing T) (d0 : OrderedEnd T) :
    DiscreteTopology (Component P d0) :=
  inferInstanceAs (DiscreteTopology {d : OrderedEnd T //
    D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.DartRelated P d0.val d.val})

theorem continuous_phi (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T) : Continuous (Phi P r d0) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (rawPhi P r d0)
  apply continuous_prod_of_discrete_left.mpr
  intro i
  have hb : Continuous (fun p : Sector => beta r i.val p.val) := by
    apply continuous_pi
    intro l
    unfold beta D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta
    split_ifs <;> fun_prop
  exact (continuous_const : Continuous (fun _ : Sector => i.val.val.1)).prodMk hb

theorem continuous_inverse_component (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T) : Continuous (fun y => ((coordinateEquiv P r d0).symm y).1) := by
  apply continuous_discrete_rng.mpr
  intro i
  have he : (fun y => ((coordinateEquiv P r d0).symm y).1) ⁻¹' {i} =
      {y | y.val.val.1 = i.val.val.1} ∩ {y | 1/2 < y.val.val.2 i.val.val.2} := by
    ext y
    exact inverse_component_fiber P r d0 y i
  rw [he]
  apply IsOpen.inter
  · exact (isOpen_discrete {i.val.val.1}).preimage
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
  · exact isOpen_lt continuous_const ((continuous_apply _).comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))

def coordinateHomeomorph (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T) :
    (Component P d0 × Sector) ≃ₜ
      ↥(Neighborhood P (ν := label P d0.val.1) d0.val) where
  toEquiv := coordinateEquiv P r d0
  continuous_toFun := continuous_phi P r d0
  continuous_invFun := by
    have hi := continuous_inverse_component P r d0
    have heval : Continuous (fun z : (Fin 4 → ℝ) × Fin 4 => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr (fun k => continuous_apply k)
    have ha : Continuous (fun y : ↥(Neighborhood P (ν := label P d0.val.1) d0.val) =>
        2*y.val.val.2 (incomingFace r (occ ((coordinateEquiv P r d0).symm y).1.val.val))) := by
      apply continuous_const.mul
      exact heval.comp ((continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_of_discreteTopology : Continuous
            (fun i : Component P d0 => incomingFace r (occ i.val.val))).comp hi))
    have hb : Continuous (fun y : ↥(Neighborhood P (ν := label P d0.val.1) d0.val) =>
        2*y.val.val.2 (outgoingFace r (occ ((coordinateEquiv P r d0).symm y).1.val.val))) := by
      apply continuous_const.mul
      exact heval.comp ((continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_of_discreteTopology : Continuous
            (fun i : Component P d0 => outgoingFace r (occ i.val.val))).comp hi))
    apply hi.prodMk
    apply continuous_induced_rng.mpr
    convert ha.prodMk hb using 1
    funext y
    change ((coordinateEquiv P r d0).symm y).2.val =
      (2*y.val.val.2 (incomingFace r (occ ((coordinateEquiv P r d0).symm y).1.val.val)),
       2*y.val.val.2 (outgoingFace r (occ ((coordinateEquiv P r d0).symm y).1.val.val)))
    obtain ⟨⟨i,p⟩,rfl⟩ := (actual_component_strict_coordinates P r d0).2 y
    have he : (coordinateEquiv P r d0).symm (Phi P r d0 (i,p)) = (i,p) :=
      (coordinateEquiv P r d0).symm_apply_apply (i,p)
    simp only [he]
    have hv := beta_actual_values r i.val p.val
    apply Prod.ext
    · change p.val.1 = 2*beta r i.val p.val _
      rw [hv.2.2.1]
      ring
    · change p.val.2 = 2*beta r i.val p.val _
      rw [hv.2.2.2]
      ring
end Topology
end D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.inverse_component_fiber,
      ``D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.continuous_phi,
      ``D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.continuous_inverse_component,
      ``D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.coordinateHomeomorph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1254 target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1254 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1254 CHECKED {name} axioms={axioms}"
