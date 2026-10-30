import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.RegularParentChart
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.CubicGain.RegularParentChart

open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.RegularParentChart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => OriginalWorld) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ => OriginalParent) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ × ℝ),
    9005/10000 ≤ x.1*x.2 → x.1*x.2 ≤ 9006/10000 →
    12758/100000 ≤ x.2 → x.2 ≤ 12759/100000 →
    R.readout () () (chartWorld x) ∧ AnalyticAt ℝ chartWorld x ∧
    AnalyticAt ℝ chartSource x ∧ AnalyticAt ℝ chartRead x ∧
    (∀ W : OriginalWorld, OriginalParent W → W.1 = x.1*x.2 → W.2.1 = x.2 →
      W = chartWorld x) ∧
    originalResponse (chartWorld x) = response (chartCoordinates x) ∧
    (chartWorld x).1/(chartWorld x).2.1 = x.1

private def interiorPoint : ℝ × ℝ :=
  ((90055/100000)/(127585/1000000),127585/1000000)

private theorem interior_bounds :
    9005/10000 ≤ interiorPoint.1*interiorPoint.2 ∧
    interiorPoint.1*interiorPoint.2 ≤ 9006/10000 ∧
    12758/100000 ≤ interiorPoint.2 ∧ interiorPoint.2 ≤ 12759/100000 := by
  norm_num [interiorPoint]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h interiorPoint interior_bounds.1 interior_bounds.2.1
    interior_bounds.2.2.1 interior_bounds.2.2.2).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),chartWorld interiorPoint,(0,0,0,0),?_⟩
  intro heq
  have hg := (analytic_original_parent_chart interiorPoint interior_bounds.1
    interior_bounds.2.1 interior_bounds.2.2.1 interior_bounds.2.2.2).1
  have hb : OriginalParent (0,0,0,0) := Eq.mp heq hg
  norm_num [OriginalParent] at hb

def source_registration :
    Registration arena (type_of% @analytic_original_parent_chart) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨analytic_original_parent_chart,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@analytic_original_parent_chart) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.RegularParentChart.analytic_original_parent_chart.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.RegularParentChart.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => OriginalParent) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.RegularParentChart
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.RegularParentChart
