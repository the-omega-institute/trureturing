import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
import Reg.Support.Hardin.LagAudit

/-! Source registrations for the full-state lag certificates. -/

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
noncomputable section

open Reg.Support.HardinLagAudit (column_power_one_ne_two)

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinLargeTransferCertificates
  (rowSeven wordSeven rowSevenCoefficients wordSevenCoefficients)

namespace RowSeven

abbrev signature : Signature := Reg.Support.HardinLagAudit.signature 47

def actual : Realization signature :=
  realize signature (fun _ _ j => rowSevenCoefficients j) (fun e => Empty.elim e)

abbrev arena : Arena := Reg.Support.HardinLagAudit.arena 47 (C 6) 1

def registration : Registration arena (type_of% (@rowSeven)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    Reg.Support.HardinLagAudit.variation (T := C 6) (b := 1) (d := 47)
      rowSeven 45 46 (fun _ => 0)
      (column_power_one_ne_two 6).symm
  sensitivity :=
    Reg.Support.HardinLagAudit.sensitivity (T := C 6) (b := 1) (d := 47)
      rowSeven 45 46 (fun _ => 0)
      (column_power_one_ne_two 6).symm
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change rowSevenCoefficients 0 ≠ rowSevenCoefficients 1
    decide +kernel

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rowSeven) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates.RowSeven.information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates.RowSeven.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => rowSevenCoefficients j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "fn", "arg", "arg", "body"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }
  ]

end RowSeven

namespace WordSeven

abbrev signature : Signature := Reg.Support.HardinLagAudit.signature 20

def actual : Realization signature :=
  realize signature (fun _ _ j => wordSevenCoefficients j) (fun e => Empty.elim e)

abbrev arena : Arena := Reg.Support.HardinLagAudit.arena 20 (wordTransfer true 6) 0

private def alternatingWord : Word 6 :=
  ⟨![0, 1, 0, 1, 0, 1, 0], by decide⟩

private theorem word_power_one_ne_zero :
    ((wordTransfer true 6) ^ (1 : ℕ)).mulVec (1 : Word 6 → ℤ) alternatingWord ≠
      ((wordTransfer true 6) ^ (0 : ℕ)).mulVec (1 : Word 6 → ℤ) alternatingWord := by
  rw [word_power, word_power]
  decide +kernel

def registration : Registration arena (type_of% (@wordSeven)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    Reg.Support.HardinLagAudit.variation (T := wordTransfer true 6) (b := 0) (d := 20)
      wordSeven 18 19 alternatingWord
      word_power_one_ne_zero
  sensitivity :=
    Reg.Support.HardinLagAudit.sensitivity (T := wordTransfer true 6) (b := 0) (d := 20)
      wordSeven 18 19 alternatingWord
      word_power_one_ne_zero
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change wordSevenCoefficients 0 ≠ wordSevenCoefficients 1
    decide +kernel

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@wordSeven) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates.WordSeven.information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates.WordSeven.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => wordSevenCoefficients j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "fn", "arg", "arg", "body"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }
  ]

end WordSeven

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
