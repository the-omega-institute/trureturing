/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuPolynomial
   mirror-E: none(waiver:literal-binomial-polynomial-construction)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer]
   utility: none
   digest: One rational polynomial interpolates every original valid rank. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Rational polynomial interpolation of the literal admissible families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu
open Polynomial

/-- The rational polynomial from the complete weak-coordinate pattern coefficients. -/
noncomputable def countingPolynomial (i : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (2 * i + 1),
    C ((patternCoefficient i k : ℚ) / (k.factorial : ℚ)) *
      (descPochhammer ℚ k).comp (X + C (1 - (i : ℚ)))

/-- This single polynomial agrees with the literal source count at every valid rank. -/
theorem countingPolynomial_eval {n i : ℕ} (hi : i ≤ n + 1) :
    (countingPolynomial i).eval (n : ℚ) = (count n (n + 1 - i) : ℚ) := by
  classical
  rw [count_eq_binomial_sum hi]
  simp only [countingPolynomial, eval_finsetSum, eval_mul, eval_C, eval_comp,
    eval_add, eval_X, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hshift : (n : ℚ) + (1 - (i : ℚ)) = ((n + 1 - i : ℕ) : ℚ) := by
    rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    ring
  rw [hshift, Nat.cast_choose_eq_descPochhammer_div]
  ring

theorem countingPolynomial_natDegree_le (i : ℕ) :
    (countingPolynomial i).natDegree ≤ 2 * i := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro k hk
  refine (natDegree_C_mul_le _ _).trans ?_
  calc
    ((descPochhammer ℚ k).comp (X + C (1 - (i : ℚ)))).natDegree ≤
        (descPochhammer ℚ k).natDegree * (X + C (1 - (i : ℚ)) : Polynomial ℚ).natDegree :=
      natDegree_comp_le
    _ = k := by rw [descPochhammer_natDegree, natDegree_X_add_C, mul_one]
    _ ≤ 2 * i := by have := Finset.mem_range.mp hk; omega

private theorem shiftedPochhammer_monic (i k : ℕ) :
    ((descPochhammer ℚ k).comp (X + C (1 - (i : ℚ)))).Monic := by
  exact (monic_descPochhammer ℚ k).comp (monic_X_add_C (1 - (i : ℚ))) (by rw [natDegree_X_add_C]; exact Nat.one_ne_zero)

private theorem shiftedPochhammer_degree (i k : ℕ) :
    ((descPochhammer ℚ k).comp (X + C (1 - (i : ℚ)))).natDegree = k := by
  rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

/-- Its top possible coefficient is exactly the top pattern count divided by (2i)!. -/
theorem countingPolynomial_top_coeff (i : ℕ) :
    (countingPolynomial i).coeff (2 * i) =
      (patternCoefficient i (2 * i) : ℚ) / ((2 * i).factorial : ℚ) := by
  classical
  rw [countingPolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single (2 * i)]
  · rw [coeff_C_mul]
    have h := (shiftedPochhammer_monic i (2 * i)).coeff_natDegree
    rw [shiftedPochhammer_degree] at h
    rw [h, mul_one]
  · intro k hk hne
    rw [coeff_C_mul]
    have hlt : k < 2 * i := by have := Finset.mem_range.mp hk; omega
    rw [coeff_eq_zero_of_natDegree_lt (by rw [shiftedPochhammer_degree]; exact hlt), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

end D5.S3.Combinatorics.MazorchukXu
