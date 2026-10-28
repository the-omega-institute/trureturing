/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Linear growth of actual normalized Laguerre absolute Mellin integrals. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfInverseMoment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfJacobi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Linear absolute Mellin control from the exact inverse moment.
The inverse moment and polynomial orthogonality supply the actual inputs. Orthogonality,
physical multiplication and centralNormalization remain the actual definitions.
The split estimate uses a scaled square inequality (Young/Cauchy), avoiding
an extra abstract Lp layer. No Mellin integrability premise is introduced. -/

set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory Set

namespace FiniteGaussianCap4.LaguerreSevenHalf

private theorem physicalX_psi_pair_le (n : ℕ) :
    polynomialPair (physicalX (psiPolynomial n)) (physicalX (psiPolynomial n)) ≤
      81 * ((n : ℝ) + 1) ^ 2 := by
  cases n with
  | zero =>
      simp only [physicalX_psi_zero]
      simp only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi]
      norm_num
      have h := jacobiUpper_sq 0
      norm_num at h
      nlinarith [h]
  | succ n =>
      simp only [physicalX_psi_succ]
      simp only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi]
      have h01 : n + 1 ≠ n := by omega
      have h02 : n + 2 ≠ n := by omega
      have h12 : n + 1 ≠ n + 2 := by omega
      simp only [h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
        ite_false, ite_true, mul_zero, sub_zero, mul_one]
      have hu := jacobiUpper_sq (n + 1)
      have hl := jacobiUpper_sq n
      push_cast at hu ⊢
      nlinarith [hu, hl, Nat.cast_nonneg (α := ℝ) n]

private theorem graph_density (n : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2 =
      x ^ (7 / 2 : ℝ) * physicalPolynomial (physicalX (psiPolynomial n)) x *
        physicalPolynomial (physicalX (psiPolynomial n)) x := by
  simp only [physicalPolynomial_X, physicalPolynomial_psi]
  rw [show (11 / 2 : ℝ) = 7 / 2 + 2 by norm_num,
    Real.rpow_add hx, Real.rpow_two]
  ring

private theorem centralPsi_graph_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2) (Ioi 0) := by
  exact (integrable_physical_product (physicalX (psiPolynomial n))
    (physicalX (psiPolynomial n))).congr_fun
      (fun x hx => (graph_density n x hx).symm) measurableSet_Ioi

private theorem centralPsi_graph_integral_le (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2) ≤
      81 * ((n : ℝ) + 1) ^ 2 := by
  calc
    _ = polynomialPair (physicalX (psiPolynomial n)) (physicalX (psiPolynomial n)) := by
      rw [← integral_physical_product]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => graph_density n x hx)
    _ ≤ _ := physicalX_psi_pair_le n

/-- Actual absolute Mellin integrability follows from the existing signed
Mellin integrability; positivity of x^(5/4) is proved on the physical half-line. -/
theorem centralPsi_integrable_absolute_mellin (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * |centralPsi x n|) (Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ =>
      ‖x ^ (5 / 4 : ℝ) * centralPsi x n‖) (Ioi 0) :=
    (integrable_centralPsi n).norm
  exact hi.congr_fun (fun x hx => by
    change ‖x ^ (5 / 4 : ℝ) * centralPsi x n‖ = _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)])
    measurableSet_Ioi

private theorem mellin_square_density (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (x ^ (5 / 4 : ℝ) * |centralPsi x n|) ^ 2 =
      x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2 := by
  rw [mul_pow, sq_abs, ← Real.rpow_mul_natCast hx.le]
  norm_num

private theorem centralPsi_near_mellin_le (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (5 / 4 : ℝ) * |centralPsi x n|) ≤ 11 / 14 := by
  have ha := (centralPsi_integrable_absolute_mellin n).mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)
  have hi := (centralPsi_integrable_inverse_square n).mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hle := integral_mono_ae ha ((hi.add hc).div_const 2)
    (show ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      x ^ (5 / 4 : ℝ) * |centralPsi x n| ≤
        (x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2 + 1) / 2 from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hsq := sq_nonneg (x ^ (5 / 4 : ℝ) * |centralPsi x n| - 1)
      rw [sub_sq, mellin_square_density n x hx.1] at hsq
      nlinarith)
  have himono : (∫ x in Ioc (0 : ℝ) 1, x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2) ≤ 4 / 7 := by
    rw [← centralPsi_integral_inverse_square n]
    apply setIntegral_mono_set (centralPsi_integrable_inverse_square n)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
    · exact .of_forall (fun x hx => hx.1)
  simp only [Pi.add_apply] at hle
  rw [integral_div, integral_add hi hc] at hle
  norm_num [setIntegral_const, Real.volume_real_Ioc] at hle
  linarith

private theorem mellin_tail_young (n : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ (5 / 4 : ℝ) * |centralPsi x n| ≤
      (x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2 +
        (9 * ((n : ℝ) + 1)) ^ 2 * x ^ (-3 : ℝ)) / (2 * (9 * ((n : ℝ) + 1))) := by
  let u : ℝ := x ^ (11 / 4 : ℝ) * |centralPsi x n|
  let v : ℝ := x ^ (-3 / 2 : ℝ)
  let l : ℝ := 9 * ((n : ℝ) + 1)
  have hl : 0 < l := by dsimp [l]; positivity
  have hu : u ^ 2 = x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2 := by
    dsimp [u]
    rw [mul_pow, sq_abs, ← Real.rpow_mul_natCast hx.le]
    norm_num
  have hv : v ^ 2 = x ^ (-3 : ℝ) := by
    dsimp [v]
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have huv : u * v = x ^ (5 / 4 : ℝ) * |centralPsi x n| := by
    dsimp [u, v]
    rw [mul_right_comm _ _ (x ^ (-3 / 2 : ℝ)), ← Real.rpow_add hx]
    norm_num
  rw [← hu, ← hv, ← huv]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hl)).2
  nlinarith [sq_nonneg (u - l * v)]

private theorem centralPsi_tail_mellin_le (n : ℕ) :
    (∫ x in Ioi (1 : ℝ), x ^ (5 / 4 : ℝ) * |centralPsi x n|) ≤
      (27 / 4 : ℝ) * ((n : ℝ) + 1) := by
  let l : ℝ := 9 * ((n : ℝ) + 1)
  have hl : 0 < l := by dsimp [l]; positivity
  have ha := (centralPsi_integrable_absolute_mellin n).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hi := (centralPsi_graph_integrable n).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hr : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hrval : (∫ x in Ioi (1 : ℝ), x ^ (-3 : ℝ)) = (1 / 2 : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
  have hle := integral_mono_ae ha ((hi.add (hr.const_mul (l ^ 2))).div_const (2 * l))
    (show ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      x ^ (5 / 4 : ℝ) * |centralPsi x n| ≤
        (x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2 + l ^ 2 * x ^ (-3 : ℝ)) / (2 * l) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mellin_tail_young n x (lt_trans (by norm_num : (0 : ℝ) < 1) hx))
  have himono : (∫ x in Ioi (1 : ℝ), x ^ (11 / 2 : ℝ) * centralPsi x n ^ 2) ≤
      81 * ((n : ℝ) + 1) ^ 2 := by
    apply le_trans ?_ (centralPsi_graph_integral_le n)
    apply setIntegral_mono_set (centralPsi_graph_integrable n)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
    · exact .of_forall (fun x hx => lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  simp only [Pi.add_apply] at hle
  rw [integral_div, integral_add hi (hr.const_mul (l ^ 2)), integral_const_mul, hrval] at hle
  apply le_trans hle
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hl)).2
  dsimp [l] at *
  nlinarith [himono]

/-- Uniform linear control of the actual absolute central Mellin integral.
The inputs are proved moments of the actual normalized mode, not hypotheses. -/
theorem centralPsi_absolute_mellin_le (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * |centralPsi x n|) ≤
      10 * ((n : ℝ) + 1) := by
  have ha := centralPsi_integrable_absolute_mellin n
  have ht := ha.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi ha ht
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  have hnear := centralPsi_near_mellin_le n
  have htail := centralPsi_tail_mellin_le n
  nlinarith [hnear, htail, Nat.cast_nonneg (α := ℝ) n]

end FiniteGaussianCap4.LaguerreSevenHalf
