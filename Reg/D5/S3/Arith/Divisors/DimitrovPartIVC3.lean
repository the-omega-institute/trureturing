import D5.S3.Arith.Divisors.DimitrovPartIVC3
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete source law with the Euler-totient family as the selected observation. -/

namespace Reg.D5.S3.Arith.Divisors.DimitrovPartIVC3

open _root_.D5.S3.Arith.Divisors.DimitrovPartIVC3
open _root_.D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes (psi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => Nat.totient n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  (((R.readout () () n : ℝ) + psi n) ^ (3 * k) +
    ((psi n : ℝ) + ArithmeticFunction.sigma 1 n) ^ (3 * k) +
    ((R.readout () () n : ℝ) + ArithmeticFunction.sigma 1 n) ^ (3 * k)) /
    (((R.readout () () n : ℝ) + psi n) ^ k *
      ((psi n : ℝ) + ArithmeticFunction.sigma 1 n) ^ k *
      ((R.readout () () n : ℝ) + ArithmeticFunction.sigma 1 n) ^ k) ≥
  (2 * (n : ℝ) ^ (3 * k) + ((n : ℝ) + 1) ^ (3 * k)) /
    ((n : ℝ) ^ (2 * k) * ((n : ℝ) + 1) ^ k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (by norm_num) 1 (by norm_num)
  have hp : psi 2 = 3 := by norm_num [psi]
  have hs : ArithmeticFunction.sigma 1 2 = 3 := by decide
  norm_num [rejected, realize, hp, hs] at hh

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (2 : ℕ), (3 : ℕ), ?_⟩
    change Nat.totient 2 ≠ Nat.totient 3
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.DimitrovPartIVC3.result)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.Divisors.DimitrovPartIVC3.unit
  realizationName := `Reg.D5.S3.Arith.Divisors.DimitrovPartIVC3.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Nat.totient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.DimitrovPartIVC3
    definition := some {
      owner := `D5.S3.Arith.Divisors.DimitrovPartIVC3
      name := `D5.S3.Arith.Divisors.DimitrovPartIVC3.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.DimitrovPartIVC3
