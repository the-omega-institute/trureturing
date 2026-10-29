import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.HannaA226838Congruence
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Residue.HannaA226838Congruence
open _root_.D5.S1.Recurrence.Residue.HannaA226838Congruence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open PowerSeries

noncomputable section

/-- Observe the rational factorial operand of the original coefficient equality. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n.factorial : ℚ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original all-index existential equality is preserved in full. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ∃ k : ℤ,
    R.readout () () n * coeff n A = 1 + 6 * (k : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, hk⟩ := h 0
  have he : (0 : ℚ) = 1 + 6 * (k : ℚ) := by
    simpa [rejected, realize] using hk
  have hi : (0 : ℤ) = 1 + 6 * k := by exact_mod_cast he
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (Nat.factorial 1 : ℚ) ≠ (Nat.factorial 2 : ℚ)
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Residue.HannaA226838Congruence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Residue.HannaA226838Congruence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n.factorial : ℚ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.HannaA226838Congruence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Residue.HannaA226838Congruence
