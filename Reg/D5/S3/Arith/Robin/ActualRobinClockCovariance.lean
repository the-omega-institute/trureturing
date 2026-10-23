import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.LogLogHigherDerivative
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

noncomputable section
set_option autoImplicit false

open scoped Interval
open MeasureTheory

namespace Reg.D5.S3.Arith.Robin.ActualRobinClockCovariance

open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev densityArena : Arena where
  signature := signature
  Law R := ∀ {s t : ℝ}, 1 < s → s ≤ t →
    IntervalIntegrable (R.readout () ()) volume s t

abbrev priceArena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, 1 < a → a ≤ b →
    IntervalIntegrable (fun t : ℝ => 1/t) volume a b ∧
    IntervalIntegrable (R.readout () ()) volume a b

def densityActual : Realization signature :=
  realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e)

def priceActual : Realization signature :=
  realize signature (fun _ _ t => t⁻¹ / Real.log t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => (t - 2)⁻¹) (fun e => nomatch e)

private theorem rejected_integrability :
    ¬ IntervalIntegrable (fun t : ℝ => (t - 2)⁻¹) volume 2 3 := by
  simp [intervalIntegrable_sub_inv_iff]

private theorem density_rejected_law : ¬ densityArena.Law rejected := by
  intro h
  exact rejected_integrability (h (s := 2) (t := 3) (by norm_num) (by norm_num))

private theorem price_rejected_law : ¬ priceArena.Law rejected := by
  intro h
  exact rejected_integrability (h (a := 2) (b := 3) (by norm_num) (by norm_num)).2

def densityFamily : Registration densityArena (type_of% (@density_integrable)) where
  actual := densityActual
  bridge := Iff.rfl
  variation := ⟨@density_integrable, rejected, density_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, density_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _i
    refine ⟨(), 1, 2, ?_⟩
    change activationDensity 1 ≠ activationDensity 2
    have h := _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel_pos
      1 0 0 (by norm_num : (1 : ℝ) < 2)
    have hl0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have he : activationDensity 2 =
        _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel 1 0 0 2 := by
      norm_num [activationDensity,
        _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel]
      field_simp [hl0]
    have hp : 0 < activationDensity 2 := he.symm ▸ h
    have hz : activationDensity 1 = 0 := by norm_num [activationDensity]
    rw [hz]
    exact hp.ne

def priceFamily : Registration priceArena (type_of% (@price_terms_integrable)) where
  actual := priceActual
  bridge := Iff.rfl
  variation := ⟨@price_terms_integrable, rejected, price_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, price_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℝ)⁻¹ / Real.log 1 ≠ (2 : ℝ)⁻¹ / Real.log 2
    have hp : 0 < (2 : ℝ)⁻¹ / Real.log 2 :=
      div_pos (inv_pos.mpr (by norm_num)) (Real.log_pos (by norm_num))
    have hz : (1 : ℝ)⁻¹ / Real.log 1 = 0 := by simp
    rw [hz]
    exact hp.ne

def densityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@density_integrable)
    (type_of% (realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ActualRobinClockCovariance.density_integrable.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualRobinClockCovariance.densityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨densityArena⟩
  objectArena := .source ⟨densityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source densityArena ⟨densityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualRobinClockCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms densityFamily

def priceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@price_terms_integrable)
    (type_of% (realize signature (fun _ _ t => t⁻¹ / Real.log t) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ActualRobinClockCovariance.price_terms_integrable.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualRobinClockCovariance.priceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨priceArena⟩
  objectArena := .source ⟨priceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source priceArena ⟨priceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t⁻¹ / Real.log t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualRobinClockCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms priceFamily

end Reg.D5.S3.Arith.Robin.ActualRobinClockCovariance
