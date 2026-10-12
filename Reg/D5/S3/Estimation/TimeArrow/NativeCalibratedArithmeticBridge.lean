import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
import Reg.Support.SingleDependentReadout

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

/-- The phase readout retains its integer harmonic and arbitrary real posterior. -/
@[reducible] def phaseSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℤ (fun _ => ℝ) (fun _ => ℝ)

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ ell mu => (ell : ℝ) * (1 / 2 - mu))
    (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => (1 / 2 : ℝ)) (fun e => nomatch e)

/-- Replacing only the original phase readout leaves the entire source telescope. -/
@[reducible] def phaseArena : Arena where
  signature := phaseSignature
  Law R := ∀ (ell t : ℤ) (mu τ : ℝ),
    (∃ a : ℤ, |R.readout () ell mu - a| ≤ τ) ↔
      ∃ z : ℤ, Int.ModEq 2 z (ell * (1 - t)) ∧
        |2 * (ell : ℝ) * (mu - (t : ℝ) / 2) - z| ≤ 2 * τ

theorem phase_actual_law : phaseArena.Law phaseActual :=
  posterior_phase_iff_parity_band

theorem phase_rejected_law : ¬ phaseArena.Law phaseRejected := by
  intro h
  have hzero := (h 0 0 0 0).mpr
    (⟨0, by norm_num [Int.ModEq], by norm_num⟩)
  obtain ⟨a, ha⟩ := hzero
  change |(1 / 2 : ℝ) - (a : ℝ)| ≤ 0 at ha
  have he : (a : ℝ) = 1 / 2 := by
    have hh := abs_nonneg ((1 / 2 : ℝ) - (a : ℝ))
    have hz := abs_eq_zero.mp (le_antisymm ha hh)
    linarith
  by_cases ha0 : a ≤ 0
  · have hcast : (a : ℝ) ≤ 0 := by exact_mod_cast ha0
    linarith
  · have ha1 : (1 : ℤ) ≤ a := by omega
    have hcast : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    linarith

def phaseEvidence : Registration phaseArena (phaseArena.Law phaseActual) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨phase_actual_law, phaseRejected, phase_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    phaseArena.Law phaseActual phaseRejected phase_rejected_law
  dependence := by
    intro role
    refine ⟨1, 0, 1, ?_⟩
    norm_num [phaseActual, realize]

noncomputable def phase_registration : LeanInformationAudit.Contract.Registration
    (@D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.posterior_phase_iff_parity_band)
    (type_of% (realize phaseSignature (fun _ ell mu => (ell : ℝ) * (1 / 2 - mu))
      (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.phaseUnit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.phaseEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨phaseArena⟩,
  objectArena := .source ⟨phaseArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source phaseArena ⟨phaseEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize phaseSignature (fun _ ell mu => (ell : ℝ) * (1 / 2 - mu))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "fn", "arg", "arg", "fn",
        "arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
