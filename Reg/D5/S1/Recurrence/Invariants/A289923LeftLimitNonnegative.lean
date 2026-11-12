import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
open _root_.D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ → ℤ) (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ a n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The source left-limit, its uniqueness and all indices remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ a : ℕ → ℤ, IsLeftLimit a ∧
    (∀ b : ℕ → ℤ, IsLeftLimit b → b = a) ∧
      (∀ n : ℕ, 0 ≤ R.readout () a n)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨a, _, _, h⟩
  have hh := h 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun n => (n : ℤ)), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
