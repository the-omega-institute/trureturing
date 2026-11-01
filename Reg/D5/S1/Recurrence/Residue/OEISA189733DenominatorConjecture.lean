import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Reg.Support.SingleDependentReadout

/-! A source-bound family retaining all six denominator observations and every index. -/

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
    (R.readout () () (6 * k), R.readout () () (6 * k + 1),
      R.readout () () (6 * k + 2), R.readout () () (6 * k + 3),
      R.readout () () (6 * k + 4), R.readout () () (6 * k + 5)) =
    (1, 3 * k + 1, 2 * k + 1, 3 * k + 2, 1, 6 * k + 6)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := congrArg Prod.fst (h 0)
  norm_num [rejected, realize] at h0

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change a 0 ≠ a 3
    norm_num [a, triangle]
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
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "fn", "arg", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "fn", "arg", "arg", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "fn", "arg", "arg", "arg", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "fn", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
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
