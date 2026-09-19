import LeanInformationAudit.Tests.RegistrationGates.RecursivePrograms
import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option trace.InformationTemplate.work true

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open Lean Meta Elab Command

namespace LeanInformationAudit.Tests.RecursiveTargetPermRange

open LeanInformationAudit.Tests.RecursivePrograms

abbrev arena : StructuralArena := ⟨Nat⟩

def signature : StructuralPrimitiveSignature where
  Index := Bool
  indexFintype := inferInstance
  Output := fun _ => List Nat

def listReadouts (A : StructuralArena) (sig : StructuralPrimitiveSignature)
    (f : forall i, A.State -> sig.Output i) : StructuralPrimitiveRealization A sig := ⟨f⟩

register_information_template listReadouts constructors 1 [List]

def rangeSide (n : Nat) : List Nat := List.range' 1 n

def targetSide (n : Nat) : List Nat :=
  List.append (List.range' 1 (n / 2))
    (List.reverse (List.range' (n / 2 + 1) (n - n / 2)))

def law : StructuralPrimitiveLawArena arena where
  signature := signature
  Law r := forall n, (r.readout false n).Perm (r.readout true n)

def actual : StructuralPrimitiveRealization arena law.signature :=
  listReadouts arena signature
    (fun i n => Bool.rec (targetSide n) (rangeSide n) i)

def bad : StructuralPrimitiveRealization arena law.signature :=
  listReadouts arena signature
    (fun i _ => Bool.rec [0] [] i)

theorem actualLaw : law.Law actual := by
  intro n
  change (targetSide n).Perm (rangeSide n)
  simpa [targetSide, target, rangeSide] using target_perm_range n

theorem badNotLaw : ¬ (law.Law bad) := by
  intro h
  have := List.Perm.length_eq (h 0)
  simp [bad, listReadouts] at this

theorem lawVariation : law.Nondegenerate := ⟨actual, bad, actualLaw, badNotLaw⟩

theorem slotSensitive : StructuralSlotSensitivity law := by
  intro i
  cases i with
  | false =>
      refine ⟨listReadouts arena signature
          (fun j _ => Bool.rec [] [] j),
        listReadouts arena signature
          (fun j _ => Bool.rec [0] [] j), ?_, ?_⟩
      · intro j hne
        cases j with
        | false => exact (hne rfl).elim
        | true => rfl
      · constructor
        · intro _ h
          have := List.Perm.length_eq (h 0)
          simp [listReadouts] at this
        · intro _ _
          exact List.Perm.refl []
  | true =>
      refine ⟨listReadouts arena signature
          (fun j _ => Bool.rec [] [] j),
        listReadouts arena signature
          (fun j _ => Bool.rec [] [0] j), ?_, ?_⟩
      · intro j hne
        cases j with
        | false => rfl
        | true => exact (hne rfl).elim
      · constructor
        · intro _ h
          have := List.Perm.length_eq (h 0)
          simp [listReadouts] at this
        · intro _ _
          exact List.Perm.refl []

structural_theorem exactTargetPermRange in law
  readout via (listReadouts arena signature
    (fun i n => Bool.rec (targetSide n) (rangeSide n) i))
  realization (listReadouts arena signature
    (fun i n => Bool.rec (targetSide n) (rangeSide n) i))
  nondegeneracy lawVariation sensitivity slotSensitive := by
    intro n
    change (targetSide n).Perm (rangeSide n)
    simpa [targetSide, target, rangeSide] using target_perm_range n

run_meta do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``exactTargetPermRange)
    | throwError "probe: missing target_perm_range binding record"
  match row.result with
  | .declaredValidated certificate =>
      logInfo m!"FULL_LAW_STATE target_perm_range declared_validated evidence={certificate.evidenceRef} arguments={certificate.argumentInputs.size} extraction={certificate.extractionInputs.size}"
      let wires ← TemplateBinding.reportJson #[(row.occurrence.key.registrationModule, #[row.occurrence.key])]
      logInfo m!"FULL_LAW_EVIDENCE {(Lean.Json.arr wires).compress}"
  | .declaredUnresolved diagnostic =>
      logError m!"FULL_LAW_STATE target_perm_range declared_unresolved diagnostic={diagnostic}"
  | .undeclared => logError "FULL_LAW_STATE target_perm_range undeclared"

#print axioms exactTargetPermRange

end LeanInformationAudit.Tests.RecursiveTargetPermRange
