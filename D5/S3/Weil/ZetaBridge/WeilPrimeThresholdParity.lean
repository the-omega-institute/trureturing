/- GID: D5/S3/Weil/ZetaBridge/WeilPrimeThresholdParity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilPrimeThresholdParity
   mirror-E: none(waiver:scaled-Fourier-and-full-space-Schur-identification)
   anchors: []
   utility: none
   digest: Preserve the actual even/odd arithmetic columns and prove cubic prime-activation energy on finite odd Fourier profiles. -/

import D5.S3.Weil.ZetaBridge.WeilEvenDualStencil
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Prime thresholds seen by the actual parity blocks

The first theorem expands the original `couplingColumn`, retaining the
opposite cancellations in its even and odd pairs. The executable consumer
forms these pairs BEFORE interval quantization and high-mode Gram summation.

The second part bounds the full complex odd-profile edge pairing. On the
fixed interval [-1,1], at a new shift 2-h, the odd basis values on the two
edge strips are sin(pi*n*t) and -sin(pi*n*(h-t)). Thus the negative symmetric
prime term is exactly the integral defined below. Its cubic bound follows
from the real sine inequality, finite Cauchy-Schwarz and an exact integral;
no boundary-value, assembled-energy or quadrature premise is supplied.

The dilation, identification with the original Weil prime contribution,
Neumann/logarithmic high-space bounds and uniform Schur certificate remain
paper/computer-assisted bridges. Lean and Scribe compilation are not asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilPrimeThresholdParity

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.WeilEvenDualStencil

/-- The original paired columns, with all Gamma, pole and prime coefficients.
The hypotheses only exclude collisions of exterior and retained frequencies.
The real sign of m is retained. These are the two formulas used before the
uniform interval Gram calculation, not bounds on an unrelated matrix. -/
theorem arithmetic_parity_pair_columns (c : ℕ) {n m : ℤ}
    (hn : 0 < n) (hm : (n : ℝ) < |(m : ℝ)|) :
    couplingColumn c {n, -n} (fun _ => 1) m =
      (((2 * ((n : ℝ) * arithmeticBoundarySymbol c n -
        (m : ℝ) * arithmeticBoundarySymbol c m)) /
        (Real.pi * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) : ℝ) : ℂ) ∧
    couplingColumn c {n, -n} (fun j => if j = n then 1 else -1) m =
      (((2 * ((m : ℝ) * arithmeticBoundarySymbol c n -
        (n : ℝ) * arithmeticBoundarySymbol c m)) /
        (Real.pi * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hneq : n ≠ -n := by intro h; linarith
  have hmem : n ∉ ({-n} : Finset ℤ) := by simpa using hneq
  have hprod : 0 < (|(m : ℝ)| - (n : ℝ)) * (|(m : ℝ)| + (n : ℝ)) :=
    mul_pos (sub_pos.mpr hm) (by linarith [abs_nonneg (m : ℝ)])
  have hs : 0 < (m : ℝ) ^ 2 - (n : ℝ) ^ 2 := by nlinarith [sq_abs (m : ℝ)]
  have hd1 : (m : ℂ) - (n : ℂ) ≠ 0 := by
    have hh : (m : ℝ) - (n : ℝ) ≠ 0 := by intro h; nlinarith
    exact_mod_cast hh
  have hd2 : (m : ℂ) + (n : ℂ) ≠ 0 := by
    have hh : (m : ℝ) + (n : ℝ) ≠ 0 := by intro h; nlinarith
    exact_mod_cast hh
  have hd3 : (m : ℂ) ^ 2 - (n : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hs.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor <;>
    simp only [couplingColumn, Finset.sum_insert hmem, Finset.sum_singleton,
      arithmetic_boundary_symbol_neg, Int.cast_neg, sub_neg_eq_add,
      if_pos rfl, if_neg hneq.symm, mul_one, mul_neg_one] <;>
    push_cast <;>
    field_simp [hp, hd1, hd2, hd3] <;> ring

private def oddProfile (S : Finset ℕ) (v : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, v n * (Real.sin (Real.pi * (n : ℝ) * t) : ℂ)

private def moment (S : Finset ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, (n : ℝ) * ‖v n‖

private theorem moment_nonneg (S : Finset ℕ) (v : ℕ → ℂ) : 0 ≤ moment S v := by
  unfold moment
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))

private theorem profile_bound (S : Finset ℕ) (v : ℕ → ℂ) (t : ℝ) :
    ‖oddProfile S v t‖ ≤ Real.pi * moment S v * |t| := by
  calc
    _ ≤ ∑ n ∈ S, ‖v n * (Real.sin (Real.pi * (n : ℝ) * t) : ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ S, ‖v n‖ * |Real.sin (Real.pi * (n : ℝ) * t)| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ n ∈ S, ‖v n‖ * |Real.pi * (n : ℝ) * t| :=
      Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
        Real.abs_sin_le_abs (norm_nonneg _))
    _ = _ := by
      simp only [abs_mul, abs_of_pos Real.pi_pos, Nat.abs_cast]
      unfold moment
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring

/-- The complete edge integral for the Weil prime term on an odd finite
Fourier profile. The complex cross terms are combined before taking a norm.
For 0<=h<=1 it represents the two disjoint activation strips. The expression
is also well defined for every real h. -/
def oddPrimeActivation (w h : ℝ) (S : Finset ℕ) (v : ℕ → ℂ) : ℂ :=
  (w : ℂ) * ∫ t : ℝ in 0..h,
    conj (oddProfile S v t) * oddProfile S v (h - t) +
    conj (oddProfile S v (h - t)) * oddProfile S v t

private theorem polynomial_envelope_integral (C h : ℝ) :
    (∫ t : ℝ in 0..h, 2 * C ^ 2 * t * (h - t)) = C ^ 2 * h ^ 3 / 3 := by
  have heq : (fun t : ℝ => 2 * C ^ 2 * t * (h - t)) =
      (fun t : ℝ => 2 * C ^ 2 * (h * t ^ 1 - t ^ 2)) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((show Continuous (fun t : ℝ => h * t ^ 1) by fun_prop).intervalIntegrable 0 h)
      ((show Continuous (fun t : ℝ => t ^ 2) by fun_prop).intervalIntegrable 0 h),
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  <;> ring

private theorem activation_moment_bound (w h : ℝ) (S : Finset ℕ) (v : ℕ → ℂ)
    (hw : 0 ≤ w) (hh : 0 ≤ h) :
    ‖oddPrimeActivation w h S v‖ ≤ w * Real.pi ^ 2 * h ^ 3 / 3 * moment S v ^ 2 := by
  let F := oddProfile S v
  let G := fun t : ℝ => conj (F t) * F (h - t) + conj (F (h - t)) * F t
  let C := Real.pi * moment S v
  have hC : 0 ≤ C := mul_nonneg Real.pi_pos.le (moment_nonneg S v)
  have hc : Continuous G := by dsimp [G, F, oddProfile]; fun_prop
  have hb (t : ℝ) (ht : t ∈ Icc 0 h) : ‖G t‖ ≤ 2 * C ^ 2 * t * (h - t) := by
    have h1 : ‖F t‖ ≤ C * t := by
      simpa only [F, C, abs_of_nonneg ht.1] using profile_bound S v t
    have h2 : ‖F (h - t)‖ ≤ C * (h - t) := by
      simpa only [F, C, abs_of_nonneg (sub_nonneg.mpr ht.2)] using profile_bound S v (h-t)
    have hp := mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC ht.1)
    calc
      _ ≤ ‖conj (F t) * F (h - t)‖ + ‖conj (F (h - t)) * F t‖ := norm_add_le _ _
      _ = 2 * (‖F t‖ * ‖F (h - t)‖) := by simp only [norm_mul, Complex.norm_conj]; ring
      _ ≤ 2 * C ^ 2 * t * (h - t) := by nlinarith
  have hint : ‖∫ t : ℝ in 0..h, G t‖ ≤ C ^ 2 * h ^ 3 / 3 := by
    calc
      _ ≤ ∫ t : ℝ in 0..h, ‖G t‖ := intervalIntegral.norm_integral_le_integral_norm hh
      _ ≤ ∫ t : ℝ in 0..h, 2 * C ^ 2 * t * (h-t) := by
        apply intervalIntegral.integral_mono_on hh
          (hc.norm.intervalIntegrable 0 h)
          ((show Continuous (fun t : ℝ => 2 * C ^ 2 * t * (h-t)) by fun_prop).intervalIntegrable 0 h)
        exact hb
      _ = _ := polynomial_envelope_integral C h
  change ‖(w : ℂ) * ∫ t : ℝ in 0..h, G t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  calc
    _ ≤ w * (C ^ 2 * h ^ 3 / 3) := mul_le_mul_of_nonneg_left hint hw
    _ = _ := by dsimp [C]; ring

/-- A genuine low odd block sees an entering prime at cubic order in the
edge overlap. The bound uses the actual finite complex coefficients, and
integrability of the cross terms follows from the finite sine profiles.
For S⊆{1,...,N}, the coefficient-square sum is the physical odd L2 norm. -/
theorem odd_prime_activation_cubic_bound (w h : ℝ) (S : Finset ℕ) (v : ℕ → ℂ)
    (hw : 0 ≤ w) (hh : 0 ≤ h) :
    ‖oddPrimeActivation w h S v‖ ≤
      (w * Real.pi ^ 2 * h ^ 3 / 3) *
        (∑ n ∈ S, (n : ℝ) ^ 2) * (∑ n ∈ S, ‖v n‖ ^ 2) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq S (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => ‖v n‖)
  calc
    _ ≤ (w * Real.pi ^ 2 * h ^ 3 / 3) * moment S v ^ 2 :=
      activation_moment_bound w h S v hw hh
    _ ≤ (w * Real.pi ^ 2 * h ^ 3 / 3) *
        ((∑ n ∈ S, (n : ℝ) ^ 2) * (∑ n ∈ S, ‖v n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

#print axioms arithmetic_parity_pair_columns
#print axioms odd_prime_activation_cubic_bound

end D5.S3.Weil.ZetaBridge.WeilPrimeThresholdParity
