/- GID: D5/S1/Digit/OnnisSquareThreeStepRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/OnnisSquareThreeStepRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs, mathlib/module/Mathlib.Logic.Function.Iterate, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/OnnisSquareThreeStepRefutation.claim; result=D5/S1/Digit/OnnisSquareThreeStepRefutation.result; claim=D5/S1/Digit/OnnisSquareThreeStepRefutation.claim
   digest: A positive square first reaches one after three nonzero-decimal-digit-product square steps. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The nonzero-decimal-digit-product square map has a positive square whose
first hitting time of one is three. This addresses Section 3 Conjecture 1
of Onnis's arXiv:2203.03381v1, with no restriction on natural square roots.
-/

namespace D5.S1.Digit.OnnisSquareThreeStepRefutation

/-- The product of exactly the nonzero digits in the decimal representation. -/
def nonzeroDigitProduct (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (fun d => d != 0)).prod

/-- Section 1.2's map: square the product of the nonzero decimal digits. -/
def step (n : ℕ) : ℕ := nonzeroDigitProduct n ^ 2

/-- Membership means that some finite iterate reaches one. -/
def SequenceMember (n : ℕ) : Prop := ∃ t : ℕ, step^[t] n = 1

/-- Exact convergence length, testing every earlier natural index including zero. -/
def FirstHit (n t : ℕ) : Prop :=
  step^[t] n = 1 ∧ ∀ k : ℕ, k < t → step^[k] n ≠ 1

/-- The whole prohibition in arXiv:2203.03381v1, Section 3 Conjecture 1.
The square root ranges over all natural numbers, without a digit-image restriction. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → (∃ r : ℕ, n = r ^ 2) →
    SequenceMember n → ¬ FirstHit n 3

/-- The square `235^2 = 55225` has orbit `55225, 250000, 100, 1`, first
reaching one at index three, and therefore refutes the whole prohibition. -/
theorem result : ¬ claim := by
  have hd₀ : Nat.digits 10 55225 = [5, 2, 2, 5, 5] := by
    have h := Nat.digits_ofDigits 10 (by decide) [5, 2, 2, 5, 5]
      (by decide) (by intro h; simp)
    exact h
  have hd₁ : Nat.digits 10 250000 = [0, 0, 0, 0, 5, 2] := by
    have h := Nat.digits_ofDigits 10 (by decide) [0, 0, 0, 0, 5, 2]
      (by decide) (by intro h; simp)
    exact h
  have hd₂ : Nat.digits 10 100 = [0, 0, 1] := by
    have h := Nat.digits_ofDigits 10 (by decide) [0, 0, 1]
      (by decide) (by intro h; simp)
    exact h
  have hs₀ : step 55225 = 250000 := by
    norm_num [step, nonzeroDigitProduct, hd₀]
  have hs₁ : step 250000 = 100 := by
    norm_num [step, nonzeroDigitProduct, hd₁]
  have hs₂ : step 100 = 1 := by
    norm_num [step, nonzeroDigitProduct, hd₂]
  have hi₁ : step^[1] 55225 = 250000 := by
    simpa only [Function.iterate_one] using hs₀
  have hi₂ : step^[2] 55225 = 100 := by
    rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply', hi₁, hs₁]
  have hi₃ : step^[3] 55225 = 1 := by
    rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply', hi₂, hs₂]
  intro h
  apply h 55225 (by decide) ⟨235, by decide⟩ ⟨3, hi₃⟩
  refine ⟨hi₃, ?_⟩
  intro k hk
  interval_cases k
  · change 55225 ≠ 1
    decide
  · rw [hi₁]
    decide
  · rw [hi₂]
    decide

#print axioms result

end D5.S1.Digit.OnnisSquareThreeStepRefutation
