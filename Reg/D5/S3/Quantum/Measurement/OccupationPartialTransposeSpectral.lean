import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the maximal-root quadratic bound. -/

namespace Reg.D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral

open _root_.D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real comparison at the lower endpoint of the gain bound. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ lower upper => lower < upper) (fun e => nomatch e)

/-- Retain all five real parameters of the quadratic estimate. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a b c x y : ℝ),
    r.readout () () (a * x ^ 2 + 2 * b * x * y + c * y ^ 2)
      (topRoot a b c * (x ^ 2 + y ^ 2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0 0 0 0
  change (0 : ℝ) * 0 ^ 2 + 2 * 0 * 0 * 0 + 0 * 0 ^ 2 <
    topRoot 0 0 0 * (0 ^ 2 + 0 ^ 2) at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun upper : ℝ => 0 ≤ upper) = (fun upper : ℝ => 1 ≤ upper) at h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration : Registration arena (type_of% @topRoot_quadratic_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨topRoot_quadratic_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@topRoot_quadratic_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
