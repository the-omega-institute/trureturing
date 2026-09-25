/- GID: D5/S3/Combinatorics/Posets/GradedGamma/GammaCone
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/GammaCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Eval.Coeff]
   utility: none
   digest: Gamma-positive polynomials are closed under graded multiplication. -/

import D5.S3.Combinatorics.Posets.GradedGamma.GammaBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open scoped BigOperators
open Polynomial
noncomputable section

def GammaPositive (d : ℕ) (p : Polynomial ℝ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ j < d / 2 + 1, 0 ≤ c j) ∧
    p = ∑ j ∈ Finset.range (d / 2 + 1), C (c j) * gammaTerm ℝ d j

/-- Multiplying two nonnegative gamma expansions convolves their coordinates
and adds their declared symmetry degrees. -/
theorem gammaPositive_mul {d e : ℕ} {p q : Polynomial ℝ}
    (hp : GammaPositive d p) (hq : GammaPositive e q) :
    GammaPositive (d + e) (p * q) := by
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  let t : ℕ → ℕ → Polynomial ℝ := fun i j =>
    C (c i * b j) * gammaTerm ℝ (d + e) (i + j)
  let z : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (d / 2 + 1),
      ∑ j ∈ Finset.range (e / 2 + 1),
        if i + j = k then c i * b j else 0
  refine ⟨z, ?_, ?_⟩
  · intro k hk
    dsimp [z]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact mul_nonneg (hc i (Finset.mem_range.mp hi))
        (hb j (Finset.mem_range.mp hj))
    · exact le_rfl
  · have hterm (i j : ℕ) (hi : i < d / 2 + 1)
        (hj : j < e / 2 + 1) :
        gammaTerm ℝ d i * gammaTerm ℝ e j =
          gammaTerm ℝ (d + e) (i + j) := by
      have hid : 2 * i ≤ d := by omega
      have hje : 2 * j ≤ e := by omega
      have heq : (d - 2 * i) + (e - 2 * j) =
          d + e - 2 * (i + j) := by omega
      simp only [gammaTerm]
      calc
        X ^ i * (1 + X) ^ (d - 2 * i) *
            (X ^ j * (1 + X) ^ (e - 2 * j)) =
          X ^ (i + j) * (1 + X) ^ ((d - 2 * i) + (e - 2 * j)) := by
            rw [pow_add, pow_add]
            ring
        _ = _ := by rw [heq]
    have hrew :
        (∑ i ∈ Finset.range (d / 2 + 1), C (c i) * gammaTerm ℝ d i) *
          (∑ j ∈ Finset.range (e / 2 + 1), C (b j) * gammaTerm ℝ e j) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          ∑ j ∈ Finset.range (e / 2 + 1), t i j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [t]
      rw [← hterm i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
      simp only [map_mul]
      ring
    rw [hrew]
    symm
    dsimp [z]
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hmem : i + j ∈ Finset.range ((d + e) / 2 + 1) := by
      simp only [Finset.mem_range] at hi hj ⊢
      omega
    have hsummand (k : ℕ) :
        C (if i + j = k then c i * b j else 0) *
            gammaTerm ℝ (d + e) k =
          if i + j = k then t i j else 0 := by
      by_cases hik : i + j = k
      · subst k
        simp [t]
      · simp [hik]
    simp_rw [hsummand]
    simp [Finset.sum_ite_eq', hmem, t, map_mul, mul_assoc]

/-- A zero constant coefficient removes the first gamma coordinate. The
remaining basis terms each contain one factor of `X`. -/
theorem gammaPositive_cancel_X {d : ℕ} {q : Polynomial ℝ}
    (hp : GammaPositive (d + 2) (X * q)) : GammaPositive d q := by
  obtain ⟨c, hc, hrep⟩ := hp
  have hsize : (d + 2) / 2 + 1 = (d / 2 + 1) + 1 := by omega
  have hzero (j : ℕ) :
      (gammaTerm ℝ (d + 2) (j + 1)).coeff 0 = 0 := by
    simp [gammaTerm]
  have hc0 : c 0 = 0 := by
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 0) hrep
    rw [coeff_X_mul_zero, hsize, Finset.sum_range_succ'] at hcoeff
    simp only [coeff_add, coeff_C_mul] at hcoeff
    have hhead : (gammaTerm ℝ (d + 2) 0).coeff 0 = 1 := by
      simp [coeff_zero_eq_eval_zero, gammaTerm]
    have htail :
        (∑ j ∈ Finset.range (d / 2 + 1),
          C (c (j + 1)) * gammaTerm ℝ (d + 2) (j + 1)).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, eval_finsetSum]
      apply Finset.sum_eq_zero
      intro j _
      rw [← coeff_zero_eq_eval_zero, coeff_C_mul, hzero j]
      simp
    rw [htail, hhead] at hcoeff
    norm_num at hcoeff
    exact hcoeff.symm
  let b : ℕ → ℝ := fun j => c (j + 1)
  refine ⟨b, ?_, ?_⟩
  · intro j hj
    exact hc (j + 1) (by rw [hsize]; omega)
  · have hterm (j : ℕ) (hj : j < d / 2 + 1) :
        gammaTerm ℝ (d + 2) (j + 1) = X * gammaTerm ℝ d j := by
      have hsub : d + 2 - 2 * (j + 1) = d - 2 * j := by omega
      simp only [gammaTerm, hsub, pow_succ]
      ring
    rw [hsize, Finset.sum_range_succ'] at hrep
    simp only [hc0, map_zero, zero_mul, add_zero] at hrep
    have hsum :
        (∑ j ∈ Finset.range (d / 2 + 1),
          C (c (j + 1)) * gammaTerm ℝ (d + 2) (j + 1)) =
        X * ∑ j ∈ Finset.range (d / 2 + 1),
          C (b j) * gammaTerm ℝ d j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm j (Finset.mem_range.mp hj)]
      dsimp [b]
      ring
    rw [hsum] at hrep
    exact mul_left_cancel₀ X_ne_zero hrep

/-- Removing any forced initial descent preserves nonnegative gamma
coefficients after lowering the declared degree twice per removed `X`. -/
theorem gammaPositive_cancel_X_pow (r d : ℕ) (q : Polynomial ℝ)
    (hp : GammaPositive (d + 2 * r) (X ^ r * q)) : GammaPositive d q := by
  induction r with
  | zero => simpa using hp
  | succ r ih =>
      have hnext : GammaPositive ((d + 2 * r) + 2) (X * (X ^ r * q)) := by
        convert hp using 1 <;> ring
      exact ih (gammaPositive_cancel_X hnext)

end
end D5.S3.Combinatorics.Posets.GradedGamma
