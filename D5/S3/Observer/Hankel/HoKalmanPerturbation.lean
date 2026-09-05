/- GID: D5/S3/Observer/Hankel/HoKalmanPerturbation
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/HoKalmanPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Computed inverse margins give nonsingularity and posterior solve error bounds. -/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.HoKalmanPerturbation

open scoped Matrix.Norms.Operator

/-- A row-sum bound controls Mathlib's induced infinity operator norm, including empty matrices. -/
theorem norm_le_of_row_sum_le {a b : Nat}
    (M : Matrix (Fin a) (Fin b) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hM : ∀ i, ∑ j, ‖M i j‖ ≤ t) : ‖M‖ ≤ t := by
  rw [Matrix.linfty_opNorm_def]
  have hh : (Finset.univ.sup fun i : Fin a => ∑ j : Fin b, ‖M i j‖₊) ≤
      (⟨t, ht⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    exact_mod_cast hM i
  exact_mod_cast hh

/-- Entrywise uncertainty is converted to an operator-norm budget, with its dimension factor. -/
theorem norm_le_of_entrywise_le {a b : Nat}
    (M : Matrix (Fin a) (Fin b) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hM : ∀ i j, |M i j| ≤ ε) : ‖M‖ ≤ (b : ℝ) * ε := by
  apply norm_le_of_row_sum_le M _ (mul_nonneg (Nat.cast_nonneg _) hε)
  intro i
  calc
    ∑ j, ‖M i j‖ ≤ ∑ _j : Fin b, ε := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs] using hM i j
    _ = (b : ℝ) * ε := by simp

/-- A tested inverse of the observed matrix and a strict noise margin certify
nonsingularity of the unknown true matrix. The true determinant is not assumed. -/
theorem true_det_ne_zero_of_inverse_margin {r : Nat}
    (K Kh Q : Matrix (Fin r) (Fin r) ℝ) (q δ : ℝ)
    (hQ : Q * Kh = 1) (hq : ‖Q‖ ≤ q)
    (hδ : ‖Kh - K‖ ≤ δ) (hmargin : q * δ < 1) : K.det ≠ 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  letI : CompleteSpace (Matrix (Fin r) (Fin r) ℝ) :=
    FiniteDimensional.complete ℝ (Matrix (Fin r) (Fin r) ℝ)
  have he : 1 - Q * K = Q * (Kh - K) := by
    rw [Matrix.mul_sub, hQ]
  have hn : ‖1 - Q * K‖ < 1 := by
    rw [he]
    calc
      ‖Q * (Kh - K)‖ ≤ ‖Q‖ * ‖Kh - K‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ q * δ := mul_le_mul hq hδ (norm_nonneg _) ((norm_nonneg _).trans hq)
      _ < 1 := hmargin
  have hu : IsUnit (Q * K) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  have hd : (Q * K).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro hk
  apply hd
  rw [Matrix.det_mul, hk, mul_zero]

/-- Perturbation identity derived from the actual observed solve and true equation. -/
theorem solve_error_identity {r b : Nat}
    (K Kh Q : Matrix (Fin r) (Fin r) ℝ)
    (L Lh X : Matrix (Fin r) (Fin b) ℝ)
    (hQ : Q * Kh = 1) (hX : K * X = L) :
    Q * Lh - X = Q * (Lh - L - (Kh - K) * X) := by
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub,
    ← Matrix.mul_assoc Q Kh, hQ, Matrix.one_mul, hX]
  abel

/-- Posterior solve bound. All budgets can be computed from observed rational data;
no unknown inverse norm, eigenbasis, or desired error inequality is a hypothesis. -/
theorem solve_error_le {r b : Nat}
    (K Kh Q : Matrix (Fin r) (Fin r) ℝ)
    (L Lh X : Matrix (Fin r) (Fin b) ℝ)
    (q δK δL H : ℝ)
    (hQ : Q * Kh = 1) (hX : K * X = L)
    (hq : ‖Q‖ ≤ q) (hK : ‖Kh - K‖ ≤ δK)
    (hL : ‖Lh - L‖ ≤ δL) (hH : ‖Q * Lh‖ ≤ H)
    (hmargin : q * δK < 1) :
    ‖Q * Lh - X‖ ≤ q * (δL + δK * H) / (1 - q * δK) := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hq
  have hK0 : 0 ≤ δK := (norm_nonneg _).trans hK
  have hL0 : 0 ≤ δL := (norm_nonneg _).trans hL
  have hXnorm : ‖X‖ ≤ H + ‖Q * Lh - X‖ := by
    calc
      ‖X‖ = ‖Q * Lh - (Q * Lh - X)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Q * Lh‖ + ‖Q * Lh - X‖ := norm_sub_le _ _
      _ ≤ H + ‖Q * Lh - X‖ := add_le_add_right hH _
  have he : ‖Q * Lh - X‖ ≤ q * (δL + δK * ‖X‖) := by
    rw [solve_error_identity K Kh Q L Lh X hQ hX]
    calc
      ‖Q * (Lh - L - (Kh - K) * X)‖ ≤
          ‖Q‖ * ‖Lh - L - (Kh - K) * X‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ q * (‖Lh - L‖ + ‖(Kh - K) * X‖) :=
        mul_le_mul hq (norm_sub_le _ _) (norm_nonneg _) hq0
      _ ≤ q * (δL + δK * ‖X‖) := by
        apply mul_le_mul_of_nonneg_left _ hq0
        apply add_le_add hL
        exact (Matrix.linfty_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have he' : ‖Q * Lh - X‖ ≤ q * (δL + δK * (H + ‖Q * Lh - X‖)) :=
    he.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hXnorm hK0) δL) hq0)
  apply (le_div_iff₀ (sub_pos.mpr hmargin)).mpr
  nlinarith [he']

#print axioms true_det_ne_zero_of_inverse_margin
#print axioms solve_error_le

end D5.S3.Observer.Hankel.HoKalmanPerturbation
