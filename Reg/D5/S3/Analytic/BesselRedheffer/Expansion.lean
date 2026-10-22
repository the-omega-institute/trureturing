import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.BesselRedheffer.Expansion
import D5.S3.Analytic.BesselRedheffer.FirstZero
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.BesselRedheffer.Defs
open _root_.D5.S3.Analytic.BesselRedheffer.FirstZero
open _root_.D5.S3.Analytic.BesselRedheffer.Expansion
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.BesselRedheffer.Expansion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => nbessel (p.1 + 1) x / nbessel p.1 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p x =>
    (p.2 ^ 2 / (p.2 ^ 2 - x ^ 2)) ^ (p.2 ^ 2 / (4 * (p.1 + 1) * (p.1 + 2))))
    (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {ν j : ℝ}, 30 ≤ ν → 0 < j →
    j ^ 2 ≤ (6 / 5 : ℝ) * (ν + 1) * (ν + 7) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
      x < j ∧ R.readout () ⟨ν, j⟩ x <
        (j ^ 2 / (j ^ 2 - x ^ 2)) ^ (j ^ 2 / (4 * (ν + 1) * (ν + 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ε, hε, H⟩ := @h 30 1 (by norm_num) (by norm_num) (by norm_num)
  have hg := (H (ε / 2) (by linarith) (by linarith)).2
  exact (lt_irrefl _) hg

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨30, 1⟩, 0, firstZero 30, ?_⟩
  change nbessel ((30 : ℝ) + 1) 0 / nbessel 30 0 ≠
    nbessel (30 + 1) (firstZero 30) / nbessel 30 (firstZero 30)
  rw [nbessel_firstZero (by norm_num : (30 : ℝ) ≤ 30)]
  simp only [_root_.D5.S3.Analytic.BesselRedheffer.Series.nbessel_zero,
    div_zero, div_self one_ne_zero]
  norm_num

def family : Registration arena (type_of% (@failure_of_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@failure_of_energy_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@failure_of_energy_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Expansion.failureUnit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Expansion.family
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
    (fun _ p x => nbessel (p.1 + 1) x / nbessel p.1 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Expansion
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.BesselRedheffer.Expansion
