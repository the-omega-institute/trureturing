import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Reg.Support.SingleDependentReadout

/-! A source-bound family for the sixth observation, retaining the full six-formula law. -/

namespace Reg.D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
open _root_.D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ,
    (a (6 * k), a (6 * k + 1), a (6 * k + 2),
      a (6 * k + 3), a (6 * k + 4), R.readout () () (6 * k + 5)) =
    (1, 3 * k + 1, 2 * k + 1, 3 * k + 2, 1, 6 * k + 6)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := congrArg (fun p => p.2.2.2.2.2) (h 0)
  norm_num [rejected, realize] at h0

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 5, 11, ?_⟩
    change a 5 ≠ a 11
    have h5 : a 5 = 6 := by
      simpa using congrArg (fun p => p.2.2.2.2.2) (result 0)
    have h11 : a 11 = 12 := by
      simpa using congrArg (fun p => p.2.2.2.2.2) (result 1)
    rw [h5, h11]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "arg", "arg", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
