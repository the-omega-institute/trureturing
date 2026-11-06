import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA097967
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.MatharA097967
open _root_.D5.S1.Recurrence.MatharA097967
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => literal n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 5 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 5 ≤ n →
    R.readout () () n + (-(n:ℚ)-6)*R.readout () () (n-1) +
      (6*(n:ℚ)+7)*R.readout () () (n-2) +
      (-13*(n:ℚ)+14)*R.readout () () (n-3) +
      4*(3*(n:ℚ)-8)*R.readout () () (n-4) +
      4*(-(n:ℚ)+4)*R.readout () () (n-5) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 5 (by decide)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change literal 0 ≠ literal 1
    norm_num [literal]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.MatharA097967.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.MatharA097967.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => literal n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA097967
    definition := some {
      owner := `D5.S1.Recurrence.MatharA097967
      name := `D5.S1.Recurrence.MatharA097967.claim
      path := #[] }
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Recurrence.MatharA097967
