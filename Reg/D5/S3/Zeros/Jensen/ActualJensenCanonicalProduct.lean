import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for differential root preservation and the Jensen criterion. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
open _root_.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open _root_.D5.S3.Analytic.Fourier.XiThetaTransform
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℂ) (fun _ => ℝ)

def imaginary : Realization signature :=
  realize signature (fun _ _ z => z.im) (fun e => nomatch e)

def real : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def constant (a : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => a) (fun e => nomatch e)

private theorem imaginaryDependence : ObservationalDependence signature imaginary := by
  intro _
  refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
  change (0 : ℂ).im ≠ Complex.I.im
  norm_num

private theorem realDependence : ObservationalDependence signature real := by
  intro _
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

private theorem degreeOneRoot : ∃ z : ℂ, (sourceJensenPolynomial 1).eval z = 0 := by
  have ha : (sourceThetaCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (source_theta_normalized.2.2.2 1))
  refine ⟨-((sourceThetaCoefficient 1 : ℂ)⁻¹), ?_⟩
  simp [sourceJensenPolynomial, Finset.sum_range_succ, source_theta_coefficient_zero,
    Nat.descFactorial, ha]

def towerArena : Arena where
  signature := signature
  Law R := RiemannHypothesis ↔ ∀ d : ℕ, 1 ≤ d →
    ∀ z : ℂ, (sourceJensenPolynomial d).eval z = 0 → R.readout () () z = 0

private theorem towerRejectedExists : ∃ R, ¬ towerArena.Law R := by
  classical
  by_cases hRH : RiemannHypothesis
  · refine ⟨constant 1, fun h => ?_⟩
    obtain ⟨z, hz⟩ := degreeOneRoot
    exact one_ne_zero (show (1 : ℝ) = 0 from h.mp hRH 1 (by decide) z hz)
  · exact ⟨constant 0, fun h => hRH (h.mpr fun _ _ _ _ => rfl)⟩

def towerEvidence : Registration towerArena (type_of% rh_iff_actual_jensen_tower) where
  actual := imaginary
  bridge := Iff.rfl
  variation := by
    obtain ⟨R, hR⟩ := towerRejectedExists
    exact ⟨rh_iff_actual_jensen_tower, R, hR⟩
  sensitivity := by
    obtain ⟨R, hR⟩ := towerRejectedExists
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity towerArena.Law imaginary R hR
  dependence := imaginaryDependence

def operatorArena : Arena where
  signature := signature
  Law R := ∀ (p : ℂ[X]) (_hp : AllRootsReal p) (a : ℝ)
    (z : ℂ) (_hz : (p - C (a : ℂ) * p.derivative).eval z = 0),
    R.readout () () z = 0

private theorem operatorRejectedLaw : ¬ operatorArena.Law (constant 1) := by
  intro h
  have hX : AllRootsReal (X : ℂ[X]) := by
    intro z hz
    simpa using congrArg Complex.im hz
  exact one_ne_zero (show (1 : ℝ) = 0 from h X hX 0 0 (by simp))

def operatorEvidence : Registration operatorArena (type_of% firstOrder_preserves_real) where
  actual := imaginary
  bridge := Iff.rfl
  variation := ⟨firstOrder_preserves_real, constant 1, operatorRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    operatorArena.Law imaginary (constant 1) operatorRejectedLaw
  dependence := imaginaryDependence

def forwardArena : Arena where
  signature := signature
  Law R :=
    let coordinate : ℂ → ℝ := R.readout () ()
    (∀ s : ℂ, Zeta23.IsNontrivialZero s → coordinate s = (1 : ℝ) / 2) →
    ∀ d : ℕ, 1 ≤ d → ∀ z : ℂ, (sourceJensenPolynomial d).eval z = 0 →
      coordinate ⟨z.im, z.re⟩ = 0

private theorem forwardRejectedLaw : ¬ forwardArena.Law (constant (1 / 2)) := by
  intro h
  obtain ⟨z, hz⟩ := degreeOneRoot
  have hh : (1 : ℝ) / 2 = 0 := h (fun _ _ => rfl) 1 (by decide) z hz
  norm_num at hh

def forwardEvidence : Registration forwardArena (type_of% actual_jensen_tower_of_zero_line) where
  actual := real
  bridge := Iff.rfl
  variation := ⟨actual_jensen_tower_of_zero_line, constant (1 / 2), forwardRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    forwardArena.Law real (constant (1 / 2)) forwardRejectedLaw
  dependence := realDependence

def towerRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    rh_iff_actual_jensen_tower (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.tower_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.towerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨towerArena⟩
  objectArena := .source ⟨towerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source towerArena ⟨towerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def operatorRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    firstOrder_preserves_real (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.operator_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.operatorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨operatorArena⟩
  objectArena := .source ⟨operatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source operatorArena ⟨operatorEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def forwardRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_jensen_tower_of_zero_line (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.forward_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct.forwardEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨forwardArena⟩
  objectArena := .source ⟨forwardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forwardArena ⟨forwardEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
