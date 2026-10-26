import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
import Reg.Support.SingleDependentReadout

/-! Source-bound sign readouts for the Fourier modes and their short gaps. -/

namespace Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev modeSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => SignType)

def modeActual : Realization modeSignature :=
  realize modeSignature (fun _ p r => SignType.sign (modeValue p.1 p.2 r)) (fun e => nomatch e)

def modeRejected : Realization modeSignature :=
  realize modeSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev modeArena : Arena where
  signature := modeSignature
  Law R := ∀ {m j : ℕ}, 1 ≤ j → j ≤ m → ∀ r : ℝ,
    R.readout () ⟨m, j⟩ r = SignType.sign (rootProduct j r)

private theorem modeRejected_law : ¬ modeArena.Law modeRejected := by
  intro h
  have he := h (m := 1) (j := 1) (by omega) (by omega) 0
  norm_num [modeRejected, realize, rootProduct] at he

private theorem modeDependence : ObservationalDependence modeSignature modeActual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  change SignType.sign (modeValue 1 1 0) ≠ SignType.sign (modeValue 1 1 1)
  rw [modeValue_sign (by omega) (by omega), modeValue_sign (by omega) (by omega)]
  norm_num [rootProduct]

def modeSource : Registration modeArena (type_of% @modeValue_sign) where
  actual := modeActual
  bridge := Iff.rfl
  variation := ⟨modeValue_sign, modeRejected, modeRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    modeArena.Law modeActual modeRejected modeRejected_law
  dependence := modeDependence

def modeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_sign) (Realization modeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns.modeUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns.modeSource
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
    (fun _ p r => SignType.sign (modeValue p.1 p.2 r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gapSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℝ)
    (fun _ => SignType)

def gapActual : Realization gapSignature :=
  realize gapSignature (fun _ p r =>
    SignType.sign (modeValue p.1 p.2.1 r - modeValue p.1 (p.2.1 + p.2.2) r))
    (fun e => nomatch e)

def gapRejected : Realization gapSignature :=
  realize gapSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev gapArena : Arena where
  signature := gapSignature
  Law R := ∀ {m j d : ℕ}, 1 ≤ j → d = 1 ∨ d = 2 → j + d ≤ m → ∀ r : ℝ,
    R.readout () ⟨m, j, d⟩ r = SignType.sign (rootProduct j r)

private theorem gapRejected_law : ¬ gapArena.Law gapRejected := by
  intro h
  have he := h (m := 2) (j := 1) (d := 1) (by omega) (Or.inl rfl) (by omega) 0
  norm_num [gapRejected, realize, rootProduct] at he

private theorem gapDependence : ObservationalDependence gapSignature gapActual := by
  intro i
  refine ⟨⟨2, 1, 1⟩, 0, 1, ?_⟩
  change SignType.sign (modeValue 2 1 0 - modeValue 2 (1 + 1) 0) ≠
    SignType.sign (modeValue 2 1 1 - modeValue 2 (1 + 1) 1)
  rw [modeValue_gap_sign (by omega) (Or.inl rfl) (by omega),
    modeValue_gap_sign (by omega) (Or.inl rfl) (by omega)]
  norm_num [rootProduct]

def gapSource : Registration gapArena (type_of% @modeValue_gap_sign) where
  actual := gapActual
  bridge := Iff.rfl
  variation := ⟨modeValue_gap_sign, gapRejected, gapRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gapArena.Law gapActual gapRejected gapRejected_law
  dependence := gapDependence

def gapAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_gap_sign) (Realization gapSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns.gapUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns.gapSource
  realizationSource := none
  generated := false
  arena := .source ⟨gapArena⟩
  objectArena := .source ⟨gapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapArena ⟨gapSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapSignature (fun _ p r =>
    SignType.sign (modeValue p.1 p.2.1 r - modeValue p.1 (p.2.1 + p.2.2) r))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
