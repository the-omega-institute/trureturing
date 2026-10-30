import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SchurConjugateSlope
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

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
    R.readout () () ‖_root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope g a b - _root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope g 0 b‖ (|a| * diskNorm g)

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

abbrev equalitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def equalityActual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev derivativeArena : Arena where
  signature := equalitySignature
  Law R := ∀ (g : ℂ → ℂ) (a b : ℝ) (z : ℂ),
    R.readout () () (deriv (interpolant g a b) z) (_root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope g a b)

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

abbrev supremaArena : Arena where
  signature := normSignature
  Law R := ∀ (a b : ℝ) (_hb : 0 < b) (_hab : a ^ 2 + b ^ 2 ≤ 1),
    entireClass.Nonempty ∧
    (∀ g ∈ entireClass, (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) ∧
      (∃ z ∈ Metric.closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖) ∧
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖) ∧
    (outerValues a b).Nonempty ∧ BddAbove (outerValues a b) ∧
    R.readout () () (1 + |a|) (uniformError a b) ∧ uniformError a b ≤ 2 ∧
    ∃ g ∈ entireClass, g = (fun z => z ^ 2 / 2) ∧ diskNorm g = 1 ∧
      _root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope g a b = a ∧ (∀ x : ℝ,
        ‖deriv g x - deriv (interpolant g a b) x‖ = |x - a|) ∧
      sSup (innerValues g a b) = 1 + |a| ∧
      nodalDerivativeNorm a b = 2 * (1 + |a|) ∧
      (1 / 2) * nodalDerivativeNorm a b = 1 + |a| ∧
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        nodalDerivativeNorm a b = ‖deriv (nodalPolynomial a b) x‖

private theorem supremaRejected : ¬ supremaArena.Law normRejected := by
  intro h
  exact (h 0 1 (by norm_num) (by norm_num)).2.2.2.2.1

def supremaFamily : Registration supremaArena (type_of% @original_suprema_bounded) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@original_suprema_bounded, normRejected, supremaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    supremaArena.Law normActual normRejected supremaRejected
  dependence := normDependence

def supremaAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_suprema_bounded) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurConjugateSlope.original_suprema_bounded.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope.supremaFamily
  realizationSource := none
  generated := false
  arena := .source ⟨supremaArena⟩
  objectArena := .source ⟨supremaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supremaArena ⟨supremaFamily⟩
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
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev classificationSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def classificationActual : Realization classificationSignature :=
  realize classificationSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def classificationRejected : Realization classificationSignature :=
  realize classificationSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev classificationArena : Arena where
  signature := classificationSignature
  Law R := ∀ (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1),
    R.readout () () (uniformError a b) (1 + |a|) ∧
    uniformError a b = (1 / 2) * nodalDerivativeNorm a b ∧
    (∀ g ∈ entireClass, ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖deriv g (x : ℂ) - deriv (interpolant g a b) (x : ℂ)‖ ≤ 1 + |a|) ∧
    entireClass.Nonempty ∧
    (∀ g ∈ entireClass, (innerValues g a b).Nonempty ∧ BddAbove (innerValues g a b) ∧
      (∃ z ∈ Metric.closedBall (0 : ℂ) 1, diskNorm g = ‖deriv (deriv g) z‖) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        sSup (innerValues g a b) = ‖deriv g x - deriv (interpolant g a b) x‖) ∧
    (outerValues a b).Nonempty ∧ BddAbove (outerValues a b) ∧
    ∃ g ∈ entireClass, g = (fun z => z ^ 2 / 2) ∧ diskNorm g = 1 ∧
      _root_.D5.S3.Analytic.Interpolation.SchurConjugateSlope.slope g a b = a ∧
      (∀ x : ℝ, ‖deriv g x - deriv (interpolant g a b) x‖ = |x - a|) ∧
      sSup (innerValues g a b) = uniformError a b ∧
      (0 ≤ a → ‖deriv g ((-1 : ℝ) : ℂ) -
        deriv (interpolant g a b) ((-1 : ℝ) : ℂ)‖ = uniformError a b) ∧
      (a ≤ 0 → ‖deriv g ((1 : ℝ) : ℂ) -
        deriv (interpolant g a b) ((1 : ℝ) : ℂ)‖ = uniformError a b) ∧
      ∃ x ∈ Icc (-1 : ℝ) 1,
        nodalDerivativeNorm a b = ‖deriv (nodalPolynomial a b) x‖

private theorem classificationRejectedLaw : ¬ classificationArena.Law classificationRejected := by
  intro h
  exact (h 0 1 (by norm_num) (by norm_num)).1

private theorem classificationDependence :
    ObservationalDependence classificationSignature classificationActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [classificationActual, realize] at hh

def classificationFamily : Registration classificationArena (type_of% @complete_classification) where
  actual := classificationActual
  bridge := Iff.rfl
  variation := ⟨@complete_classification, classificationRejected, classificationRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    classificationArena.Law classificationActual classificationRejected classificationRejectedLaw
  dependence := classificationDependence

def classificationAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_classification) (Realization classificationSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurConjugateSlope.complete_classification.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope.classificationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classificationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize classificationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurConjugateSlope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms classificationAudit

#print axioms supremaAudit

#print axioms slopeAudit
#print axioms derivativeAudit

end Reg.D5.S3.Analytic.Interpolation.SchurConjugateSlope
