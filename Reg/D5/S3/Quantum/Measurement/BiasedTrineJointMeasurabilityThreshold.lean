import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the exact biased-trine compatibility threshold. -/

namespace Reg.D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold

open _root_.D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real comparison at the lower endpoint of the threshold inequality. -/
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

/-- Retain the full source domain and the joint-measurability biconditional. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ b η : ℝ, -1 ≤ b → b ≤ 1 → 0 ≤ η → η ≤ 1 →
    |b| ≤ 1 - η →
      (TriplewiseJointlyMeasurable b η ↔ r.readout () () η (trineThreshold b))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : trineThreshold 0 = (2 / 3 : ℝ) := by norm_num [trineThreshold]
  have hj : TriplewiseJointlyMeasurable 0 (2 / 3) :=
    (result 0 (2 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).mpr (by rw [ht])
  have hbad := (h 0 (2 / 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mp hj
  change (2 / 3 : ℝ) < trineThreshold 0 at hbad
  rw [ht] at hbad
  exact (lt_irrefl _) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun upper : ℝ => 0 ≤ upper) = (fun upper : ℝ => 1 ≤ upper) at h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.source_registration
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
    owner := `D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
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
end Reg.D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
