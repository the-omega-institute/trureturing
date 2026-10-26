import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the finite frequency support identities. -/

namespace Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
noncomputable section

abbrev modeSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def modeActual : Realization modeSignature :=
  realize modeSignature (fun _ p s => modeValue p.1 p.2 (2 * (s : ℝ))) (fun e => nomatch e)

def modeRejected : Realization modeSignature :=
  realize modeSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev modeArena : Arena where
  signature := modeSignature
  Law R := ∀ (m j s : ℕ), s < j → j ≤ m → R.readout () ⟨m, j⟩ s = 0

private theorem modeRejected_law : ¬ modeArena.Law modeRejected := by
  intro h
  have he := h 1 1 0 (by omega) (by omega)
  norm_num [modeRejected, realize] at he

private theorem modeDependence : ObservationalDependence modeSignature modeActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  norm_num [modeActual, realize, modeValue, angle, Finset.sum_Icc_succ_top,
    Real.rpow_natCast, Real.cos_pi_div_three]

def modeSource : Registration modeArena (type_of% @modeValue_even_eq_zero) where
  actual := modeActual
  bridge := Iff.rfl
  variation := ⟨modeValue_even_eq_zero, modeRejected, modeRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    modeArena.Law modeActual modeRejected modeRejected_law
  dependence := modeDependence

def modeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_even_eq_zero) (Realization modeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros.modeUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros.modeSource
  realizationSource := none
  generated := false
  arena := .source ⟨modeArena⟩
  objectArena := .source ⟨modeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modeArena ⟨modeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeSignature
    (fun _ p s => modeValue p.1 p.2 (2 * (s : ℝ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gapSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def gapActual : Realization gapSignature :=
  realize gapSignature (fun _ p s =>
    modeValue p.1 p.2.1 (2 * (s : ℝ)) - modeValue p.1 (p.2.1 + p.2.2) (2 * (s : ℝ)))
    (fun e => nomatch e)

def gapRejected : Realization gapSignature :=
  realize gapSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev gapArena : Arena where
  signature := gapSignature
  Law R := ∀ (m j d s : ℕ), s < j → j + d ≤ m → R.readout () ⟨m, j, d⟩ s = 0

private theorem gapRejected_law : ¬ gapArena.Law gapRejected := by
  intro h
  have he := h 1 1 0 0 (by omega) (by omega)
  norm_num [gapRejected, realize] at he

private theorem gapDependence : ObservationalDependence gapSignature gapActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, 0, 1, ?_⟩
  norm_num [gapActual, realize, modeValue, angle, Finset.sum_Icc_succ_top,
    Real.rpow_natCast, Real.cos_pi_div_three, Real.cos_two_mul]

def gapSource : Registration gapArena (type_of% @modeValue_gap_even_eq_zero) where
  actual := gapActual
  bridge := Iff.rfl
  variation := ⟨modeValue_gap_even_eq_zero, gapRejected, gapRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gapArena.Law gapActual gapRejected gapRejected_law
  dependence := gapDependence

def gapAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_gap_even_eq_zero) (Realization gapSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros.gapUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros.gapSource
  realizationSource := none
  generated := false
  arena := .source ⟨gapArena⟩
  objectArena := .source ⟨gapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapArena ⟨gapSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapSignature (fun _ p s =>
    modeValue p.1 p.2.1 (2 * (s : ℝ)) - modeValue p.1 (p.2.1 + p.2.2) (2 * (s : ℝ)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
