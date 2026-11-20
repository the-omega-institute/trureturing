import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
import Reg.Support.SingleDependentReadout

/-! The sharp grid budget observes the number of available occupancy codes. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Nat

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k q : ℕ}, 2 ≤ k → 0 < q →
    (∀ d : ℕ, 0 < d → d ≤ k → d ∣ k * (k - 1) * q) → ∀ n : ℕ,
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S)
      (w : S → ℝ) (f : {p : Fin k → ℕ // ∑ i, p i = k * (k - 1) * q} → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * n) ↔
      k * q + 1 ≤ R.readout () k n

private theorem smallDivisible : ∀ d : ℕ, 0 < d → d ≤ 2 → d ∣ 2 * (2 - 1) * 1 := by
  intro d positive bound
  have h : d = 1 ∨ d = 2 := by omega
  rcases h with rfl | rfl <;> decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have existsLaw :=
    (grid_support_budget_iff (k := 2) (q := 1) (by decide) (by decide) smallDivisible 1).mpr
      (by decide)
  exact (by decide : ¬ (2 : ℕ) * 1 + 1 ≤ 0)
    ((h (k := 2) (q := 1) (by decide) (by decide) smallDivisible 1).mp existsLaw)

def family : Registration arena (type_of% (@grid_support_budget_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨grid_support_budget_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    exact (by decide : (1 : ℕ) ≠ 3)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@grid_support_budget_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
