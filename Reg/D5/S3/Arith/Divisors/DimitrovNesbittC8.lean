import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.DimitrovNesbittC8
import Reg.Support.DependentFamily

/-! Source binding for the original C8 numerator coefficient. -/

namespace Reg.D5.S3.Arith.Divisors.DimitrovNesbittC8

open _root_.D5.S3.Arith.Divisors.DimitrovNesbittC8
open _root_.D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes (psi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The source coefficient n in the numerator term 4 n² (n+1)^(2k−2). -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  let A : ℝ := (Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let B : ℝ := (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ))
  A / (B + C) + B / (A + C) + C / (A + B) ≥
    ((n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k +
      ((n : ℝ) - 1) ^ (2 * k) + 4 * (R.readout () () n) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2)) /
    (2 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2) +
      2 * (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by norm_num) 1 (by norm_num)
  norm_num [rejected, realize, psi, Nat.primeFactors, Nat.totient_two,
    ArithmeticFunction.sigma_apply] at hbad

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => (n : ℝ))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.DimitrovNesbittC8.result.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.DimitrovNesbittC8.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => (n : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.DimitrovNesbittC8
    definition := some {
      owner := `D5.S3.Arith.Divisors.DimitrovNesbittC8
      name := `D5.S3.Arith.Divisors.DimitrovNesbittC8.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Divisors.DimitrovNesbittC8
