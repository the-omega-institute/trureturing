/- GID: D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Probability tools for three prime divisors per modulus. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/ThreePrime/Probability.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Distortion
import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainProbability
import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainRearrangement
import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainTrees

/-!
# Probability tools for three prime divisors per modulus

Finite rational laws suffice: all physical prime-power coordinates have finite
height. The results here construct conditioning and joint kernels, rather than
postulating conditional independence of the physical coordinates.
-/

namespace Erdos7.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Conditioning on a positive-mass event, as an actual finite law. -/
noncomputable def condition (μ : FiniteLaw Ω) (A : Ω → Prop)
    [DecidablePred A] (hA : 0 < μ.prob A) : FiniteLaw Ω where
  weight x := if A x then μ.weight x / μ.prob A else 0
  weight_nonneg x := by
    split_ifs
    · exact div_nonneg (μ.weight_nonneg x) hA.le
    · exact le_rfl
  weight_sum := by
    have he : (∑ x, if A x then μ.weight x else 0) = μ.prob A := by
      simp only [prob, expect, mul_ite, mul_one, mul_zero]
    calc
      (∑ x, if A x then μ.weight x / μ.prob A else 0) =
          (∑ x, if A x then μ.weight x else 0) / μ.prob A := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : A x <;> simp [h]
      _ = 1 := by rw [he, div_self (ne_of_gt hA)]

theorem condition_prob (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (hA : 0 < μ.prob A) :
    (μ.condition A hA).prob B = μ.prob (fun x ↦ A x ∧ B x) / μ.prob A := by
  change (∑ x, (if A x then μ.weight x / μ.prob A else 0) *
    (if B x then 1 else 0)) =
    (∑ x, μ.weight x * (if A x ∧ B x then 1 else 0)) / μ.prob A
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]

theorem condition_prob_le (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (hA : 0 < μ.prob A) :
    (μ.condition A hA).prob B ≤ μ.prob B / μ.prob A := by
  rw [condition_prob]
  exact div_le_div_of_nonneg_right
    (μ.prob_mono _ B (fun _ h ↦ h.2)) hA.le

/-- Attach a history-dependent normalized kernel. -/
def joint (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) where
  weight z := μ.weight z.1 * (K z.1).weight z.2
  weight_nonneg z := mul_nonneg (μ.weight_nonneg _) ((K _).weight_nonneg _)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FiniteLaw.weight_sum, mul_one]

theorem joint_expect (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (f : Ω × Ξ → ℚ) :
    (μ.joint K).expect f = μ.expect (fun x ↦ (K x).expect (fun y ↦ f (x,y))) := by
  unfold expect joint
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_assoc]

/-- A normalized kernel preserves every function of the entire past. -/
theorem joint_expect_past (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (f : Ω → ℚ) : (μ.joint K).expect (fun z ↦ f z.1) = μ.expect f := by
  rw [joint_expect]
  simp only [expect_const]

theorem joint_prob_past (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (A : Ω → Prop) [DecidablePred A] :
    (μ.joint K).prob (fun z ↦ A z.1) = μ.prob A := by
  unfold prob
  exact joint_expect_past μ K (fun x ↦ if A x then (1:ℚ) else 0)

theorem joint_prob (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (A : Ω × Ξ → Prop) [DecidablePred A] :
    (μ.joint K).prob A = μ.expect (fun x ↦ (K x).prob (fun y ↦ A (x,y))) := by
  exact joint_expect μ K _

/-- The conditional cap integrated over any event of the full history. -/
theorem joint_prefix_cap (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (A : Ω → Prop) (B : Ξ → Prop) [DecidablePred A] [DecidablePred B]
    (c : ℚ) (hcap : ∀ x, (K x).prob B ≤ c) :
    (μ.joint K).prob (fun z ↦ A z.1 ∧ B z.2) ≤ c * μ.prob A := by
  rw [joint_prob]
  have he : c * μ.prob A = μ.expect (fun x ↦ if A x then c else 0) := by
    unfold prob
    rw [← μ.expect_smul]
    apply μ.expect_congr
    intro x
    by_cases h : A x <;> simp [h]
  rw [he]
  apply μ.expect_mono
  intro x
  by_cases h : A x
  · simpa [h] using hcap x
  · simp [h, prob, expect]

/-- The paper's uniform distortion cap, for any event, not just an atom. -/
theorem distort_event_cap (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (μ.distort A δ hδ0 hδ1).prob B ≤ μ.prob B / (1-δ) := by
  change (∑ x, (μ.distort A δ hδ0 hδ1).weight x * (if B x then 1 else 0)) ≤ _
  rw [prob, expect, Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : B x
  · simp only [h, if_true, mul_one]
    simpa [div_eq_mul_inv] using μ.distort_weight_le A δ (μ.weight x) hδ0 hδ1 x le_rfl
  · simp [h]

end Erdos7.FiniteLaw

namespace Erdos7.ThreePrime

/-- The positive part used throughout the manuscript. -/
def hinge (t x : ℚ) : ℚ := max (x-t) 0

theorem hinge_nonneg (t x : ℚ) : 0 ≤ hinge t x := le_max_right _ _

theorem hinge_mono (t : ℚ) : Monotone (hinge t) := by
  intro x y h
  exact max_le_max (sub_le_sub_right h t) le_rfl

theorem hinge_complement (t x : ℚ) : hinge t x = x-t + hinge x t := by
  unfold hinge
  by_cases h : t ≤ x
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem thresholdMass_eq_hinge {δ α : ℚ} (_hδ1 : δ < 1) :
    thresholdMass δ α = hinge δ α / (1-δ) := by
  unfold thresholdMass hinge
  split_ifs with h
  · rw [max_eq_right (by linarith)]
    simp
  · rw [max_eq_left (by linarith)]

/-- The scalar load inequality at a prime coordinate. -/
theorem thresholdMass_le_hinge {d δ α R : ℚ} (hd : 0 < d)
    (hδ1 : δ < 1) (hload : α ≤ R/d) :
    thresholdMass δ α ≤ hinge (d*δ) R / (d*(1-δ)) := by
  rw [thresholdMass_eq_hinge hδ1]
  have hden : 0 < 1-δ := by linarith
  calc
    hinge δ α / (1-δ) ≤ hinge δ (R/d) / (1-δ) :=
      div_le_div_of_nonneg_right (hinge_mono δ hload) hden.le
    _ = hinge (d*δ) R / (d*(1-δ)) := by
      unfold hinge
      rw [show R/d-δ = (R-d*δ)/d by field_simp]
      by_cases h : 0 ≤ R-d*δ
      · rw [max_eq_left (div_nonneg h hd.le), max_eq_left h, div_div]
      · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hd.le),
          max_eq_right (le_of_not_ge h)]
        simp

/-- The unrestricted second-moment hinge inequality. -/
theorem hinge_le_square {t u : ℚ} (ht : 0 < t) :
    hinge t u ≤ u^2/(4*t) := by
  unfold hinge
  apply max_le
  · apply (le_div_iff₀ (by positivity : (0:ℚ) < 4*t)).2
    nlinarith [sq_nonneg (u-2*t)]
  · positivity

theorem expected_hinge_complement {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (X : Ω → ℚ) (t : ℚ) :
    μ.expect (hinge t ∘ X) = μ.expect X - t + μ.expect (fun x ↦ hinge (X x) t) := by
  simp only [Function.comp_def, hinge_complement t]
  rw [μ.expect_add, μ.expect_sub, μ.expect_const]

end Erdos7.ThreePrime
