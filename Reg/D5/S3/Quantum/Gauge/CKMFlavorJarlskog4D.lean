import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D

set_option autoImplicit false

abbrev phaseCountSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def phaseCountActual : Realization phaseCountSignature :=
  realize phaseCountSignature (fun _ _ n => physicalPhaseCount n) (fun e => nomatch e)

def phaseCountErased : Realization phaseCountSignature :=
  realize phaseCountSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev phaseCountArena : Arena where
  signature := phaseCountSignature
  Law R := ∀ N : ℕ, 0 < R.readout () () N ↔ 3 ≤ N

private theorem phase_count_erased_fails : ¬ phaseCountArena.Law phaseCountErased := by
  intro h
  exact (Nat.lt_irrefl 0) ((h 3).mpr (Nat.le_refl 3))

def phaseCountFamily : Registration phaseCountArena
    (type_of% (@cp_phase_pos_iff_three_generations)) where
  actual := phaseCountActual
  bridge := Iff.rfl
  variation := ⟨cp_phase_pos_iff_three_generations, phaseCountErased, phase_count_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    phaseCountArena.Law phaseCountActual phaseCountErased phase_count_erased_fails
  dependence := by
    intro _
    refine ⟨(), 2, 3, ?_⟩
    change physicalPhaseCount 2 ≠ physicalPhaseCount 3
    decide

def phaseCountRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cp_phase_pos_iff_three_generations) (Realization phaseCountSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D.cp_phase_pos_iff_three_generations.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D.phaseCountFamily
  realizationSource := none
  generated := false
  arena := .source ⟨phaseCountArena⟩
  objectArena := .source ⟨phaseCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phaseCountArena ⟨phaseCountFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize phaseCountSignature (fun _ _ n => physicalPhaseCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
