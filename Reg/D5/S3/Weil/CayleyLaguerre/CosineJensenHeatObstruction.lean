import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction

open _root_.D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction
open _root_.D5.S3.Zeros.Jensen.JensenPolynomialObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ y => ((Real.pi : ℂ) + (y : ℂ) * Complex.I).im) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (t y : ℝ), y ≠ 0 →
    let c := Real.exp t * Real.cosh y
    (∀ u z : ℂ, deriv (fun s : ℂ => cosineHeat c s z) u =
      -deriv (deriv (cosineHeat c u)) z) ∧
    (∀ (u : ℝ) (d n : ℕ), 0 < n →
      (PolynomialHyperbolic (jensenPolynomial (cosineHeatJet c u) d n) ↔
        0 < d ∨ Even n)) ∧
    cosineHeat c (t : ℂ) ((Real.pi : ℂ) + (y : ℂ) * Complex.I) = 0 ∧
    R.readout () () y ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0 1 one_ne_zero).2.2.2
  exact hbad rfl

def evidence : Registration arena (type_of% (@positive_shift_heat_counterexample)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_shift_heat_counterexample, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_shift_heat_counterexample)
    (type_of% (realize signature
      (fun _ _ y => ((Real.pi : ℂ) + (y : ℂ) * Complex.I).im) (fun e => nomatch e)))
    Type Unit where
  unitName := `Reg.D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction.heat_unit
  realizationName := `Reg.D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ y => ((Real.pi : ℂ) + (y : ℂ) * Complex.I).im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Reg.D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction
