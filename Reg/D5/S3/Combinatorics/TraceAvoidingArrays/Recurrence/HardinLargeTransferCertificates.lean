import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
import Reg.Support.DependentFamily

/-! Source registrations for the full-state lag certificates. -/

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
noncomputable section

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinLargeTransferCertificates
  (rowSeven wordSeven rowSevenCoefficients wordSevenCoefficients)

namespace RowSeven

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 47
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => rowSevenCoefficients j) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    IsLagRelation (C 6) 1 rowSevenCoefficients ∧
      (∑ j : Fin 47, r.readout () () j) = 1

theorem erased_law : ¬ arena.Law erased := by
  intro h
  have hsum : (∑ _ : Fin 47, (0 : ℤ)) = 1 := h.2
  simp at hsum

def registration : Registration arena (type_of% (@rowSeven)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rowSeven, erased, erased_law⟩
  sensitivity := ⟨fun i => ⟨erased, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, erased_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
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
  readout := some (realize signature (fun _ _ j => rowSevenCoefficients j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
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

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 20
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => wordSevenCoefficients j) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    IsLagRelation (wordTransfer true 6) 0 wordSevenCoefficients ∧
      (∑ j : Fin 20, r.readout () () j) = 1

theorem erased_law : ¬ arena.Law erased := by
  intro h
  have hsum : (∑ _ : Fin 20, (0 : ℤ)) = 1 := h.2
  simp at hsum

def registration : Registration arena (type_of% (@wordSeven)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wordSeven, erased, erased_law⟩
  sensitivity := ⟨fun i => ⟨erased, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, erased_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
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
  readout := some (realize signature (fun _ _ j => wordSevenCoefficients j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinLargeTransferCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
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
