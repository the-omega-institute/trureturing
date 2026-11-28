import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation

/-! The derivative functional in the nonzero excess-variation clause is
observed on real functions, with the evaluation point as parameter. -/

noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation

namespace Reg.D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ t f => deriv f t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℝ) (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi),
    (∀ i, ‖sphericalVertices t i‖ = 1) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → HasDerivAt (fun s => sphericalAngle s i j k) 1 t) ∧
    HasDerivAt sphericalExcess 3 t ∧
    (∑ i : Fin 3, deriv (fun s => sphericalAngle s i (i + 1) (i + 2)) t) =
      deriv sphericalExcess t ∧ R.readout () t sphericalExcess ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : Real.pi / 2 ∈ Set.Ioo (Real.pi / 3) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact (h (Real.pi / 2) ht).2.2.2.2 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℝ => 0), id, ?_⟩
  change deriv (fun _ : ℝ => 0) 0 ≠ deriv id 0
  simp

def source : Registration arena (type_of% (@equilateral_spherical_angle_variation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equilateral_spherical_angle_variation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@equilateral_spherical_angle_variation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation.unit
  realizationName := `Reg.D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t f => deriv f t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation
