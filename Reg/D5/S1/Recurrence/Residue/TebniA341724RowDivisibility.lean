import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
import Reg.Support.SingleDependentReadout

/-! Exact source-bound observation families for the original arithmetic statement. -/

namespace Reg.D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
open _root_.D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open PowerSeries
open _root_.D5.S1.Recurrence.Residue.IntegralEGFComposition

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ p => Tq p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- Both integer-witness clauses, their guards, and every natural parameter remain.
The prime-row coefficient function is the sole intervened observation. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ p k : ℕ, Nat.Prime p → 0 < k → k < p →
      ∃ z : ℤ, (z : ℚ) = R.readout () () p k ∧ (p : ℤ) ∣ z) ∧
    (∀ m k : ℕ, k < 2 ^ m →
      ∃ z : ℤ, (z : ℚ) = Tq (2 ^ m) k ∧ ((2 ^ m : ℕ) : ℤ) ∣ z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz, hd⟩ := h.1 2 1 Nat.prime_two (by decide) (by decide)
  change (z : ℚ) = 1 at hz
  have hz1 : z = 1 := by exact_mod_cast hz
  norm_num [hz1] at hd

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 1
    change Tq 0 1 = Tq 1 1 at he
    have hs : constantCoeff _root_.D5.S1.Recurrence.Residue.TebniA364822.sinh = 0 := by
      simpa using _root_.D5.S1.Recurrence.Residue.TebniA364822.eCoeff_sinh 0
    have hsn : constantCoeff (rescale (-1 : ℚ)
        _root_.D5.S1.Recurrence.Residue.TebniA364822.sinh) = 0 := by
      rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
      simpa using hs
    have hd : constantCoeff denominator = 1 := by simp [denominator, hsn]
    norm_num [Tq, eCoeff, column, coeff_X_pow_mul', coeff_zero_eq_constantCoeff, hd] at he

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Residue.TebniA341724RowDivisibility.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Residue.TebniA341724RowDivisibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Tq p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
    definition := some { owner := `D5.S1.Recurrence.Residue.TebniA341724RowDivisibility, name := `D5.S1.Recurrence.Residue.TebniA341724RowDivisibility.claim, path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Residue.TebniA341724RowDivisibility
