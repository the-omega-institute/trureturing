import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
import Reg.Support.SingleDependentReadout

/-! Exact source-bound observation families for the original arithmetic statement. -/

namespace Reg.D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
open _root_.D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ m k => (2 ^ m).choose k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The original exponent, index and oddness guard are all preserved. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m k : ℕ, Odd k → 2 ^ m ∣ R.readout () m k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1 1 (by decide)
  norm_num [rejected, realize] at h1

def family : Registration arena (type_of% @pow_two_dvd_choose_odd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pow_two_dvd_choose_odd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change (2 ^ 1).choose 0 ≠ (2 ^ 1).choose 1
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@pow_two_dvd_choose_odd) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m k => (2 ^ m).choose k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
