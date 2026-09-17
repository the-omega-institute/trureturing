/- GID: D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Order.Monotone.Basic]
   utility: none
   digest: Two fixed binary models have separated predictions along all long zero words. -/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace D5.S3.ObserverMemory.PredictionFactors.FixedModelZeroWordSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Joint masses of the all-zero report word and the two final hidden bits.
The old bit emits first, then flips with probability one quarter. The emission
parameter is fixed throughout the recursion, and the initial hidden bit is fair. -/
noncomputable def zeroMass (p : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1 / 2, 1 / 2)
  | n + 1 =>
    let v := zeroMass p n
    ((3 / 4) * p * v.1 + (1 / 4) * (1 - p) * v.2,
      (1 / 4) * p * v.1 + (3 / 4) * (1 - p) * v.2)

/-- Conditional mass of hidden bit one after the zero word. -/
noncomputable def zeroPosterior (p : ℝ) (n : ℕ) : ℝ :=
  (zeroMass p n).2 / ((zeroMass p n).1 + (zeroMass p n).2)

/-- Next-zero probability, emitted from the current hidden bit. -/
noncomputable def zeroPrediction (p : ℝ) (n : ℕ) : ℝ :=
  p + (1 - 2 * p) * zeroPosterior p n

/-- The one-third model stays below a rational posterior barrier, whereas the
one-quarter posterior strictly increases. Their next-zero probabilities remain
separated by more than one twenty-fourth from length three onwards. -/
theorem fixed_model_zero_word_separation :
    (∀ n : ℕ, zeroPosterior (1 / 3) n < 9 / 14 ∧
      zeroPrediction (1 / 3) n < 23 / 42) ∧
    StrictMono (zeroPosterior (1 / 4)) ∧
    zeroPosterior (1 / 4) 3 = 19 / 28 ∧
    zeroPrediction (1 / 4) 3 = 33 / 56 ∧
    (∀ n : ℕ, 3 ≤ n →
      1 / 48 < (zeroPrediction (1 / 4) n - zeroPrediction (1 / 3) n) / 2) := by
  have thirdCone : ∀ n : ℕ,
      0 < (zeroMass (1 / 3) n).1 ∧
      0 < (zeroMass (1 / 3) n).2 ∧
      5 * (zeroMass (1 / 3) n).2 < 9 * (zeroMass (1 / 3) n).1 := by
    intro n
    induction n with
    | zero => norm_num [zeroMass]
    | succ n ih =>
      simp only [zeroMass]
      obtain ⟨h0, h1, hcone⟩ := ih
      constructor
      · positivity
      constructor
      · positivity
      · nlinarith
  have thirdBound : ∀ n : ℕ, zeroPosterior (1 / 3) n < 9 / 14 ∧
      zeroPrediction (1 / 3) n < 23 / 42 := by
    intro n
    obtain ⟨h0, h1, hcone⟩ := thirdCone n
    have hsum : 0 < (zeroMass (1 / 3) n).1 + (zeroMass (1 / 3) n).2 :=
      add_pos h0 h1
    have hq : zeroPosterior (1 / 3) n < 9 / 14 := by
      rw [zeroPosterior, div_lt_iff₀ hsum]
      linarith
    constructor
    · exact hq
    · unfold zeroPrediction
      linarith
  have quarterPositive : ∀ n : ℕ,
      0 < (zeroMass (1 / 4) n).1 ∧ 0 < (zeroMass (1 / 4) n).2 := by
    intro n
    induction n with
    | zero => norm_num [zeroMass]
    | succ n ih =>
      simp only [zeroMass]
      obtain ⟨h0, h1⟩ := ih
      constructor <;> positivity
  have crossPositive : ∀ n : ℕ,
      (zeroMass (1 / 4) n).2 * (zeroMass (1 / 4) (n + 1)).1 <
        (zeroMass (1 / 4) (n + 1)).2 * (zeroMass (1 / 4) n).1 := by
    intro n
    induction n with
    | zero => norm_num [zeroMass]
    | succ n ih =>
      have scaled := mul_pos (show (0 : ℝ) < 3 / 32 by norm_num) (sub_pos.mpr ih)
      simp only [zeroMass] at scaled ⊢
      nlinarith
  have quarterMono : StrictMono (zeroPosterior (1 / 4)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨h0, h1⟩ := quarterPositive n
    obtain ⟨h0', h1'⟩ := quarterPositive (n + 1)
    rw [zeroPosterior, zeroPosterior, div_lt_div_iff₀ (add_pos h0 h1) (add_pos h0' h1')]
    nlinarith [crossPositive n]
  have thirdStep : zeroPosterior (1 / 4) 3 = 19 / 28 := by
    norm_num [zeroPosterior, zeroMass]
  have thirdPrediction : zeroPrediction (1 / 4) 3 = 33 / 56 := by
    norm_num [zeroPrediction, thirdStep]
  refine ⟨thirdBound, quarterMono, thirdStep, thirdPrediction, ?_⟩
  intro n hn
  have hq := quarterMono.monotone hn
  rw [thirdStep] at hq
  have hb := (thirdBound n).2
  unfold zeroPrediction at hb ⊢
  linarith

#print axioms fixed_model_zero_word_separation

end D5.S3.ObserverMemory.PredictionFactors.FixedModelZeroWordSeparation
