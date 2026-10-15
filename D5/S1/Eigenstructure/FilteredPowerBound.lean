/- GID: D5/S1/Eigenstructure/FilteredPowerBound
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/FilteredPowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Operator.Basic]
   utility: none
   digest: A preserving contraction plus a lowering map has a finite binomial power bound. -/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace D5.S1.Eigenstructure.FilteredPowerBound

open scoped BigOperators

private noncomputable def binomialBound (b : ℝ) (k j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range j, (k.choose l : ℝ) * b ^ l

private theorem binomialBound_nonneg {b : ℝ} (hb : 0 ≤ b) (k j : ℕ) :
    0 ≤ binomialBound b k j := by
  exact Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb _)

private theorem binomialBound_zero_succ (b : ℝ) (j : ℕ) :
    binomialBound b 0 (j + 1) = 1 := by
  simp [binomialBound, Finset.sum_range_succ']

private theorem binomialBound_succ_succ (b : ℝ) (k j : ℕ) :
    binomialBound b (k + 1) (j + 1) =
      binomialBound b k (j + 1) + binomialBound b k j * b := by
  unfold binomialBound
  rw [Finset.sum_range_succ' _ j, Finset.sum_range_succ' _ j]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  simp_rw [Nat.choose_succ_succ, Nat.cast_add, add_mul, pow_succ]
  rw [Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [Finset.sum_mul]
  ring

private theorem norm_pow_apply_le {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A B : E →L[𝕜] E) (F : ℕ → Submodule 𝕜 E) (h : ℕ)
    (hzero : F 0 = ⊥)
    (hpres : ∀ j < h, ∀ x ∈ F (j + 1), A x ∈ F (j + 1))
    (hlower : ∀ j < h, ∀ x ∈ F (j + 1), B x ∈ F j)
    (hA : ‖A‖ ≤ 1) (k j : ℕ) (hj : j ≤ h) (x : E) (hx : x ∈ F j) :
    ‖((A + B) ^ k) x‖ ≤ binomialBound ‖B‖ k j * ‖x‖ := by
  induction k generalizing j x with
  | zero =>
      cases j with
      | zero =>
          have hx0 : x = 0 := by simpa [hzero] using hx
          simp only [hx0, map_zero, norm_zero, mul_zero, le_refl]
      | succ j => simp [binomialBound_zero_succ]
  | succ k ih =>
      cases j with
      | zero =>
          have hx0 : x = 0 := by simpa [hzero] using hx
          simp only [hx0, map_zero, norm_zero, mul_zero, le_refl]
      | succ j =>
          have hjh : j < h := by omega
          have hAx : ‖A x‖ ≤ ‖x‖ := by
            calc
              ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
              _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
              _ = ‖x‖ := one_mul _
          rw [pow_succ, mul_apply_eq_comp, add_apply, map_add]
          calc
            ‖((A + B) ^ k) (A x) + ((A + B) ^ k) (B x)‖ ≤
                ‖((A + B) ^ k) (A x)‖ + ‖((A + B) ^ k) (B x)‖ := norm_add_le _ _
            _ ≤ binomialBound ‖B‖ k (j + 1) * ‖A x‖ +
                binomialBound ‖B‖ k j * ‖B x‖ :=
              add_le_add (ih (j + 1) hj (A x) (hpres j hjh x hx))
                (ih j (by omega) (B x) (hlower j hjh x hx))
            _ ≤ binomialBound ‖B‖ k (j + 1) * ‖x‖ +
                binomialBound ‖B‖ k j * (‖B‖ * ‖x‖) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hAx (binomialBound_nonneg (norm_nonneg B) _ _))
                (mul_le_mul_of_nonneg_left (B.le_opNorm x)
                  (binomialBound_nonneg (norm_nonneg B) _ _))
            _ = binomialBound ‖B‖ (k + 1) (j + 1) * ‖x‖ := by
              rw [binomialBound_succ_succ]
              ring

/-- A filtration-preserving contraction plus a lowering endomorphism has polynomially
bounded powers. The finite submodule family need not be nested; only the stated mapping
conditions and its endpoints are needed. No commutation or completeness is assumed. -/
theorem norm_add_pow_le_sum_choose {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A B : E →L[𝕜] E) (F : ℕ → Submodule 𝕜 E) (h : ℕ)
    (hzero : F 0 = ⊥) (htop : F h = ⊤)
    (hpres : ∀ j < h, ∀ x ∈ F (j + 1), A x ∈ F (j + 1))
    (hlower : ∀ j < h, ∀ x ∈ F (j + 1), B x ∈ F j)
    (hA : ‖A‖ ≤ 1) (k : ℕ) :
    ‖(A + B) ^ k‖ ≤ ∑ l ∈ Finset.range h, (k.choose l : ℝ) * ‖B‖ ^ l := by
  apply ContinuousLinearMap.opNorm_le_bound _ (binomialBound_nonneg (norm_nonneg B) k h)
  intro x
  exact norm_pow_apply_le A B F h hzero hpres hlower hA k h le_rfl x (by simp [htop])

#print axioms norm_add_pow_le_sum_choose

end D5.S1.Eigenstructure.FilteredPowerBound
