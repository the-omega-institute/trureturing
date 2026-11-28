import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
open LeanInformationAudit
open Matrix
open scoped Matrix

namespace Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D

set_option autoImplicit false

noncomputable section

private abbrev SpatialMatrix := Matrix (Fin 3) (Fin 3) ℝ

abbrev energySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def energyActual : Realization energySignature :=
  realize energySignature
    (fun _ hp hc => Matrix.trace (gwStrainZ hp hc * gwStrainZ hp hc)) (fun e => nomatch e)

def energyErased : Realization energySignature :=
  realize energySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev energyArena : Arena where
  signature := energySignature
  Law R := ∀ hp hc : ℝ, R.readout () hp hc = 2 * (hp ^ 2 + hc ^ 2)

private theorem energy_erased_fails : ¬ energyArena.Law energyErased := by
  intro h
  have he := h 0 1
  change (0 : ℝ) = 2 * (0 ^ 2 + 1 ^ 2) at he
  norm_num at he

def energyFamily : Registration energyArena (type_of% (@gw_strain_hilbert_schmidt_energy)) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨gw_strain_hilbert_schmidt_energy, energyErased, energy_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    energyArena.Law energyActual energyErased energy_erased_fails
  dependence := by
    intro _
    refine ⟨0, 0, 1, ?_⟩
    change Matrix.trace (gwStrainZ 0 0 * gwStrainZ 0 0) ≠
      Matrix.trace (gwStrainZ 0 1 * gwStrainZ 0 1)
    rw [gw_strain_hilbert_schmidt_energy, gw_strain_hilbert_schmidt_energy]
    norm_num

def energyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gw_strain_hilbert_schmidt_energy) (Realization energySignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.gw_strain_hilbert_schmidt_energy.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.energyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena⟩
  objectArena := .source ⟨energyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena ⟨energyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature
    (fun _ hp hc => Matrix.trace (gwStrainZ hp hc * gwStrainZ hp hc)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev strainSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => SpatialMatrix)

def strainActual : Realization strainSignature :=
  realize strainSignature (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e)

def strainErased : Realization strainSignature :=
  realize strainSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem strain_cross_entry (hp hc : ℝ) : gwStrainZ hp hc 0 1 = hc :=
  (tt_z_coordinates (gwStrainZ hp hc) rfl).2.symm

private theorem strain_dependence :
    ∀ i : strainSignature.Role, ∃ (p : strainSignature.Params)
      (x y : strainSignature.State p), strainActual.readout i p x ≠ strainActual.readout i p y := by
  intro _
  refine ⟨0, 0, 1, ?_⟩
  intro he
  change gwStrainZ 0 0 = gwStrainZ 0 1 at he
  have hf := congrArg (fun A : SpatialMatrix => A 0 1) he
  norm_num [strain_cross_entry] at hf

private theorem strain_cross_nonzero : gwStrainZ 0 1 ≠ 0 := by
  intro he
  have hf := congrArg (fun A : SpatialMatrix => A 0 1) he
  norm_num [strain_cross_entry] at hf

abbrev classificationArena : Arena where
  signature := strainSignature
  Law R := ∀ h : SpatialMatrix,
    (hᵀ = h ∧ h.mulVec ![0, 0, 1] = 0 ∧ Matrix.trace h = 0) ↔
      ∃ hp hc : ℝ, h = R.readout () hp hc

private theorem classification_erased_fails : ¬ classificationArena.Law strainErased := by
  intro hlaw
  have hTT := (tt_z_classification (gwStrainZ 0 1)).mpr ⟨0, 1, rfl⟩
  obtain ⟨_, _, h⟩ := (hlaw (gwStrainZ 0 1)).mp hTT
  exact strain_cross_nonzero h

def classificationFamily : Registration classificationArena (type_of% (@tt_z_classification)) where
  actual := strainActual
  bridge := Iff.rfl
  variation := ⟨tt_z_classification, strainErased, classification_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    classificationArena.Law strainActual strainErased classification_erased_fails
  dependence := strain_dependence

def classificationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tt_z_classification) (Realization strainSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.tt_z_classification.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.classificationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classificationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize strainSignature
    (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev polarizationArena : Arena where
  signature := strainSignature
  Law R := ∀ (h : SpatialMatrix) {hp hc : ℝ},
    h = R.readout () hp hc → hp = h 0 0 ∧ hc = h 0 1

private theorem polarization_erased_fails : ¬ polarizationArena.Law strainErased := by
  intro hlaw
  have he := (hlaw (hp := 0) (hc := 1) 0 rfl).2
  norm_num at he

def polarizationFamily : Registration polarizationArena (type_of% (@tt_z_coordinates)) where
  actual := strainActual
  bridge := Iff.rfl
  variation := ⟨tt_z_coordinates, strainErased, polarization_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    polarizationArena.Law strainActual strainErased polarization_erased_fails
  dependence := strain_dependence

def polarizationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tt_z_coordinates) (Realization strainSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.tt_z_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.polarizationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨polarizationArena⟩
  objectArena := .source ⟨polarizationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source polarizationArena ⟨polarizationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize strainSignature
    (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev helicityArena : Arena where
  signature := strainSignature
  Law R := ∀ φ hp hc : ℝ, rotZ3 φ * R.readout () hp hc * (rotZ3 φ)ᵀ =
    gwStrainZ (hp * Real.cos (2 * φ) - hc * Real.sin (2 * φ))
      (hp * Real.sin (2 * φ) + hc * Real.cos (2 * φ))

private theorem helicity_erased_fails : ¬ helicityArena.Law strainErased := by
  intro hlaw
  have he : rotZ3 0 * (0 : SpatialMatrix) * (rotZ3 0)ᵀ =
      gwStrainZ (0 * Real.cos (2 * 0) - 1 * Real.sin (2 * 0))
        (0 * Real.sin (2 * 0) + 1 * Real.cos (2 * 0)) := hlaw 0 0 1
  exact strain_cross_nonzero (by simpa using he.symm)

def helicityFamily : Registration helicityArena (type_of% (@gw_strain_helicity_two)) where
  actual := strainActual
  bridge := Iff.rfl
  variation := ⟨gw_strain_helicity_two, strainErased, helicity_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    helicityArena.Law strainActual strainErased helicity_erased_fails
  dependence := strain_dependence

def helicityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gw_strain_helicity_two) (Realization strainSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.gw_strain_helicity_two.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.helicityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨helicityArena⟩
  objectArena := .source ⟨helicityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source helicityArena ⟨helicityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize strainSignature
    (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev piRotationArena : Arena where
  signature := strainSignature
  Law R := ∀ hp hc : ℝ, rotZ3 Real.pi * R.readout () hp hc * (rotZ3 Real.pi)ᵀ =
    gwStrainZ hp hc

private theorem piRotation_erased_fails : ¬ piRotationArena.Law strainErased := by
  intro hlaw
  have he : rotZ3 Real.pi * (0 : SpatialMatrix) * (rotZ3 Real.pi)ᵀ =
      gwStrainZ 0 1 := hlaw 0 1
  exact strain_cross_nonzero (by simpa using he.symm)

def piRotationFamily : Registration piRotationArena (type_of% (@gw_strain_pi_invariant)) where
  actual := strainActual
  bridge := Iff.rfl
  variation := ⟨gw_strain_pi_invariant, strainErased, piRotation_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    piRotationArena.Law strainActual strainErased piRotation_erased_fails
  dependence := strain_dependence

def piRotationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gw_strain_pi_invariant) (Realization strainSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.gw_strain_pi_invariant.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.piRotationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨piRotationArena⟩
  objectArena := .source ⟨piRotationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source piRotationArena ⟨piRotationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize strainSignature
    (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev halfPiRotationArena : Arena where
  signature := strainSignature
  Law R := ∀ hp hc : ℝ, rotZ3 (Real.pi / 2) * R.readout () hp hc * (rotZ3 (Real.pi / 2))ᵀ =
    -gwStrainZ hp hc

private theorem halfPiRotation_erased_fails : ¬ halfPiRotationArena.Law strainErased := by
  intro hlaw
  have he : rotZ3 (Real.pi / 2) * (0 : SpatialMatrix) * (rotZ3 (Real.pi / 2))ᵀ =
      -gwStrainZ 0 1 := hlaw 0 1
  have hz : -gwStrainZ 0 1 = 0 := by simpa using he.symm
  exact strain_cross_nonzero (neg_eq_zero.mp hz)

def halfPiRotationFamily : Registration halfPiRotationArena (type_of% (@gw_strain_half_pi_neg)) where
  actual := strainActual
  bridge := Iff.rfl
  variation := ⟨gw_strain_half_pi_neg, strainErased, halfPiRotation_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    halfPiRotationArena.Law strainActual strainErased halfPiRotation_erased_fails
  dependence := strain_dependence

def halfPiRotationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gw_strain_half_pi_neg) (Realization strainSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.gw_strain_half_pi_neg.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.halfPiRotationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨halfPiRotationArena⟩
  objectArena := .source ⟨halfPiRotationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source halfPiRotationArena ⟨halfPiRotationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize strainSignature
    (fun _ hp hc => gwStrainZ hp hc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
