import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.TebniA364822
import Reg.Support.SingleDependentReadout

/-! Exact source-bound observation families for the original arithmetic statement. -/

namespace Reg.D5.S1.Recurrence.Residue.TebniA364822
open _root_.D5.S1.Recurrence.Residue.TebniA364822
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open _root_.D5.S1.Recurrence.Residue.IntegralEGFComposition

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => eCoeff sinh n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The entire Taylor-coefficient statement is retained for every natural index. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = if Even n then 0 else 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  norm_num [rejected, realize] at h0

def family : Registration arena (type_of% @eCoeff_sinh) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eCoeff_sinh, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change eCoeff sinh 0 ≠ eCoeff sinh 1
    rw [eCoeff_sinh, eCoeff_sinh]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@eCoeff_sinh) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Residue.TebniA364822.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Residue.TebniA364822.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => eCoeff sinh n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.TebniA364822
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Residue.TebniA364822
