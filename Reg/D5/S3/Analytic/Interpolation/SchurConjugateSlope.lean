import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SchurConjugateSlope
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [normActual, realize] at hh

abbrev slopeArena : Arena where
  signature := normSignature
  Law R := ∀ (g : ℂ → ℂ) (_hg : Differentiable ℂ g) (a b : ℝ)
    (_hb : 0 < b) (_hab : a ^ 2 + b ^ 2 ≤ 1),
    R.readout () () ‖slope g a b - slope g 0 b‖ (|a| * diskNorm g)

private theorem slopeRejected : ¬ slopeArena.Law normRejected := by
  intro h
  exact h (fun _ => 0) (by fun_prop) 0 1 (by norm_num) (by norm_num)

def slopeFamily : Registration slopeArena (type_of% @slope_transport) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@slope_transport, normRejected, slopeRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    slopeArena.Law normActual normRejected slopeRejected
  dependence := normDependence

def slopeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@slope_transport) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope_transport.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slopeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨slopeArena⟩
  objectArena := .source ⟨slopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source slopeArena ⟨slopeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurConjugateSlope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev interpolantArena : Arena where
  signature := normSignature
  Law R := ∀ (g : ℂ → ℂ) (_hg : Differentiable ℂ g) (a b : ℝ)
    (_hb : 0 < b) (_hab : a ^ 2 + b ^ 2 ≤ 1) (z : ℂ),
    R.readout () () ‖deriv (interpolant g a b) z - deriv (interpolant g 0 b) z‖
      (|a| * diskNorm g)

private theorem interpolantRejected : ¬ interpolantArena.Law normRejected := by
  intro h
  exact h (fun _ => 0) (by fun_prop) 0 1 (by norm_num) (by norm_num) 0

def interpolantFamily : Registration interpolantArena (type_of% @interpolant_transport) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@interpolant_transport, normRejected, interpolantRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    interpolantArena.Law normActual normRejected interpolantRejected
  dependence := normDependence

def interpolantAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@interpolant_transport) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurConjugateSlope.interpolant_transport.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope.interpolantFamily
  realizationSource := none
  generated := false
  arena := .source ⟨interpolantArena⟩
  objectArena := .source ⟨interpolantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source interpolantArena ⟨interpolantFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurConjugateSlope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev equalitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def equalityActual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev derivativeArena : Arena where
  signature := equalitySignature
  Law R := ∀ (g : ℂ → ℂ) (a b : ℝ) (z : ℂ),
    R.readout () () (deriv (interpolant g a b) z) (slope g a b)

private theorem derivativeRejected : ¬ derivativeArena.Law equalityRejected := by
  intro h
  exact h (fun _ => 0) 0 1 0

private theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [equalityActual, realize] at hh

def derivativeFamily : Registration derivativeArena (type_of% @interpolant_deriv) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@interpolant_deriv, equalityRejected, derivativeRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    derivativeArena.Law equalityActual equalityRejected derivativeRejected
  dependence := equalityDependence

def derivativeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@interpolant_deriv) (Realization equalitySignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurConjugateSlope.interpolant_deriv.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope.derivativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨derivativeArena⟩
  objectArena := .source ⟨derivativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source derivativeArena ⟨derivativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurConjugateSlope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms slopeAudit
#print axioms interpolantAudit
#print axioms derivativeAudit

end Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope
