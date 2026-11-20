import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.FractionalGridSupport
import Reg.Support.SingleDependentReadout

/-! The fractional grid budget observes the greatest common divisor of the two grid parameters. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.FractionalGridSupport

open _root_.D5.S3.ConceptDynamics.Attribution.FractionalGridSupport
open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport (CalibratingLaw)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat

noncomputable section

abbrev fractionalSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def fractionalActual : Realization fractionalSignature :=
  realize fractionalSignature (fun _ k q => k.gcd q) (fun e => nomatch e)

def fractionalRejected : Realization fractionalSignature :=
  realize fractionalSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fractionalArena : Arena where
  signature := fractionalSignature
  Law R := ∀ {k q : ℕ}, 2 ≤ k → 0 < q →
    (∀ p : ℕ, p.Prime → p ≤ k → p ∣ (k - 1) * q) → ∀ n : ℕ,
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S)
      (w : S → ℝ) (f : {p : Fin k → ℕ // ∑ i, p i = (k - 1) * q} → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * (n + 1)) ↔
      q + 1 ≤ (R.readout () k q + 1) * (k + 1)^n

private theorem fractional_rejected_law : ¬ fractionalArena.Law fractionalRejected := by
  intro alternate
  have primes : ∀ p : ℕ, p.Prime → p ≤ 2 → p ∣ (2 - 1) * 2 := by
    intro p prime le
    have equal : p = 2 := le_antisymm le prime.two_le
    subst p
    decide
  have existsLaw := (fractional_grid_budget_iff (k := 2) (q := 2)
    (by decide) (by decide) primes 0).mpr (by decide)
  exact (by decide : ¬ (3 : ℕ) ≤ 1)
    ((alternate (k := 2) (q := 2) (by decide) (by decide) primes 0).mp existsLaw)

def fractionalFamily : Registration fractionalArena (type_of% (@fractional_grid_budget_iff)) where
  actual := fractionalActual
  bridge := Iff.rfl
  variation := ⟨fractional_grid_budget_iff, fractionalRejected, fractional_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity fractionalArena.Law fractionalActual fractionalRejected fractional_rejected_law
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    exact (by decide : (1 : ℕ) ≠ 2)

def fractionalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@fractional_grid_budget_iff) (Realization fractionalSignature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FractionalGridSupport.fractional_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FractionalGridSupport.fractionalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fractionalArena⟩
  objectArena := .source ⟨fractionalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fractionalArena ⟨fractionalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fractionalSignature (fun _ k q => k.gcd q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.FractionalGridSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.FractionalGridSupport
