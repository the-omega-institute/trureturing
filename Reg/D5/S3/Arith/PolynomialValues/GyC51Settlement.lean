import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.PolynomialValues.GyC51Settlement

/-! The upper index bound as a source-bound observation of the row index. -/

namespace Reg.D5.S3.Arith.PolynomialValues.GyC51Settlement

open _root_.D5.S3.Arith.PolynomialValues.GyC51Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun anchor => nomatch anchor)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun anchor => nomatch anchor)

def arena : Arena where
  signature := signature
  Law R := ¬ (∀ x : ℕ → Polynomial ℝ, StronglyQLogConcave x →
    ∀ n p j : ℕ, 1 ≤ j → j ≤ p → p ≤ R.readout () () n →
      CoeffLogConcave (E x n p j) ∧ CoeffLogConcave (H x n p j))

private theorem erased_fails : ¬ arena.Law erased := by
  intro rejected
  apply rejected
  intro x strong n p j hj hjp hp
  change p ≤ 0 at hp
  omega

def family : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, erased, erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ erased_fails
  dependence := by
    intro role
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      result (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.PolynomialValues.GyC51Settlement.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.PolynomialValues.GyC51Settlement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PolynomialValues.GyC51Settlement
    definition := some {
      owner := `D5.S3.Arith.PolynomialValues.GyC51Settlement
      name := `D5.S3.Arith.PolynomialValues.GyC51Settlement.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.PolynomialValues.GyC51Settlement
