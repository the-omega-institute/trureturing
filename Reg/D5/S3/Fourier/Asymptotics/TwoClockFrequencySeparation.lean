import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the two-clock frequency readout. -/

namespace Reg.D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation

open _root_.D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℤ (fun _ => ℤ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m n => clockFrequency m n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℤ), (m ≠ 0 ∨ n ≠ 0) →
    1 ≤ |R.readout () m n| * (128 * (1734 : ℝ) ^ (32 * max m.natAbs n.natAbs))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0 1 (Or.inr one_ne_zero)
  norm_num [rejected, realize] at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change clockFrequency 0 0 ≠ clockFrequency 0 1
  have hzero : clockFrequency 0 0 = 0 := by simp [clockFrequency]
  rw [hzero]
  intro h
  have hsep := frequency_separation 0 1 (Or.inr one_ne_zero)
  rw [← h, abs_zero, zero_mul] at hsep
  norm_num at hsep

def source_registration : Registration arena (type_of% @frequency_separation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨frequency_separation, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@frequency_separation) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ m n => clockFrequency m n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end

end Reg.D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation
