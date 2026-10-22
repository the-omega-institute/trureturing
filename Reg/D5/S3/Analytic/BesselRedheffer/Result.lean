import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.BesselRedheffer.Result
import D5.S3.Analytic.BesselRedheffer.FirstZero
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.BesselRedheffer.Defs
open _root_.D5.S3.Analytic.BesselRedheffer.FirstZero
open _root_.D5.S3.Analytic.BesselRedheffer.Result
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.BesselRedheffer.Result

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ ν x => nbessel (ν + 1) x / nbessel ν x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ ν x =>
    (firstZero ν ^ 2 / (firstZero ν ^ 2 - x ^ 2)) ^
      (firstZero ν ^ 2 / (4 * (ν + 1) * (ν + 2)))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ ν : ℝ, 30 ≤ ν → ∃ x : ℝ,
    0 < x ∧ x < firstZero ν ∧ R.readout () ν x <
      (firstZero ν ^ 2 / (firstZero ν ^ 2 - x ^ 2)) ^
        (firstZero ν ^ 2 / (4 * (ν + 1) * (ν + 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, _, _, hx⟩ := h 30 (by norm_num)
  exact (lt_irrefl _) hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨30, 0, firstZero 30, ?_⟩
  change nbessel ((30 : ℝ) + 1) 0 / nbessel 30 0 ≠
    nbessel (30 + 1) (firstZero 30) / nbessel 30 (firstZero 30)
  rw [nbessel_firstZero (by norm_num : (30 : ℝ) ≤ 30)]
  simp only [_root_.D5.S3.Analytic.BesselRedheffer.Series.nbessel_zero,
    div_zero, div_self one_ne_zero]
  norm_num

def family : Registration arena (type_of% (@failure_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@failure_family, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@failure_family) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Result.failureUnit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ ν x => nbessel (ν + 1) x / nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.BesselRedheffer.Result
