import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CyclicHarmonicEquality

/-! Readouts for the order of the support difference and for the admissible modulus. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicHarmonicEquality
open _root_.Reg.Support

noncomputable section

abbrev differenceSignature :=
  SingleDependentReadout.signature ℕ ZMod (fun _ => ℕ)

def differenceActual : Realization differenceSignature :=
  realize differenceSignature (fun _ _ d => addOrderOf d)
    (fun e => nomatch e)

def differenceRejected : Realization differenceSignature :=
  realize differenceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev differenceArena : Arena where
  signature := differenceSignature
  Law V := ∀ (q : ℕ) [NeZero q]
      (w : ZMod q → ℝ) (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j),
    let d := ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)
    let s := ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q)
    (s = 0 → ‖d‖ ^ 2 ≤ 1 / 2) ∧
      (s = 0 ∧ ‖d‖ ^ 2 = 1 / 2 ↔ ∃ a b : ZMod q, a ≠ b ∧ V.readout () q (b - a) = 4 ∧
        w a = 1 / 2 ∧ w b = 1 / 2 ∧ ∀ j, j ≠ a → j ≠ b → w j = 0)

private theorem rejected_difference_law : ¬ differenceArena.Law differenceRejected := by
  intro law
  obtain ⟨w, hw, hpos, hsecond, hfirst⟩ :=
    (zmod_exists_first_mode_half_of_second_zero 4).mpr (dvd_refl 4)
  obtain ⟨_, _, _, hfalse, _⟩ :=
    (law 4 w hw hpos).2.mp ⟨hsecond, hfirst⟩
  change (0 : ℕ) = 4 at hfalse
  contradiction

private theorem difference_dependence : ObservationalDependence differenceSignature differenceActual := by
  intro i
  cases i
  refine ⟨4, 1, 0, ?_⟩
  change addOrderOf (1 : ZMod 4) ≠ addOrderOf (0 : ZMod 4)
  simp

def differenceEvidence :
    Registration differenceArena (type_of% @zmod_first_mode_le_half_of_second_zero) where
  actual := differenceActual
  bridge := Iff.rfl
  variation := ⟨@zmod_first_mode_le_half_of_second_zero, differenceRejected, rejected_difference_law⟩
  sensitivity := SingleDependentReadout.sensitivity differenceArena.Law differenceActual
    differenceRejected rejected_difference_law
  dependence := difference_dependence

def differenceRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@zmod_first_mode_le_half_of_second_zero) (Realization differenceSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality.differenceUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality.differenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨differenceArena⟩
  objectArena := .source ⟨differenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source differenceArena ⟨differenceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize differenceSignature
    (fun _ _ d => addOrderOf d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicHarmonicEquality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg",
        "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev modulusSignature :=
  SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def modulusActual : Realization modulusSignature :=
  realize modulusSignature (fun _ _ q => q) (fun e => nomatch e)

def modulusRejected : Realization modulusSignature :=
  realize modulusSignature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev modulusArena : Arena where
  signature := modulusSignature
  Law V := ∀ (q : ℕ) [NeZero q],
    (∃ w : ZMod q → ℝ, (∑ j, w j) = 1 ∧ (∀ j, 0 ≤ w j) ∧
      ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q) = 0 ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)‖ ^ 2 = 1 / 2) ↔
        4 ∣ V.readout () () q

private theorem rejected_modulus_law : ¬ modulusArena.Law modulusRejected := by
  intro law
  have hw := (zmod_exists_first_mode_half_of_second_zero 4).mpr (dvd_refl 4)
  have hfalse := (law 4).mp hw
  change (4 : ℕ) ∣ 3 at hfalse
  norm_num at hfalse

private theorem modulus_dependence : ObservationalDependence modulusSignature modulusActual := by
  intro i
  cases i
  exact ⟨(), 4, 3, by decide⟩

def modulusEvidence :
    Registration modulusArena (type_of% @zmod_exists_first_mode_half_of_second_zero) where
  actual := modulusActual
  bridge := Iff.rfl
  variation := ⟨@zmod_exists_first_mode_half_of_second_zero, modulusRejected, rejected_modulus_law⟩
  sensitivity := SingleDependentReadout.sensitivity modulusArena.Law modulusActual modulusRejected
    rejected_modulus_law
  dependence := modulus_dependence

def modulusRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@zmod_exists_first_mode_half_of_second_zero) (Realization modulusSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality.modulusUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality.modulusEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨modulusArena⟩
  objectArena := .source ⟨modulusArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modulusArena ⟨modulusEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modulusSignature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicHarmonicEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicHarmonicEquality
