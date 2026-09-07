/- GID: D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/NormalizedJensenDegreeLowering
   mirror-E: none(waiver:symbolic-polynomial-identity)
   anchors: []
   utility: none
   digest: Fixed theta-moment Jensen polynomials satisfy exact degree lowering. -/

import D5.S3.Zeros.Jensen.JensenPolynomialObstruction
import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering

open Polynomial MeasureTheory
open D5.S3.Zeros.CompletedZeta
open scoped ComplexConjugate

/-- The fixed theta series, extended evenly from the positive half-line. -/
def sourceThetaKernel (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * |x| / 2) -
      6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * |x| / 2)) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * |x|))

/-- The literal density expression with the canonical xi center as denominator. -/
def sourceThetaDensity (x : ℝ) : ℝ :=
  sourceThetaKernel x / (xiReading (1 / 2 : ℂ)).re

/-- Index `k` denotes the even moment of order `2*k` of the density expression. -/
def sourceThetaMoment (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ (2 * k) * sourceThetaDensity x

/-- The even moment divided by its even factorial. -/
def sourceThetaCoefficient (k : ℕ) : ℝ :=
  sourceThetaMoment k / ((2 * k).factorial : ℝ)

/-- The canonical Jensen polynomial with `gamma(k)=k!*a(k)`, shift zero and scale `1/d`. -/
def normalizedJensen (a : ℕ → ℝ) (d : ℕ) : ℂ[X] :=
  ((JensenPolynomialObstruction.jensenPolynomial (fun k => (k.factorial : ℝ) * a k)
      d 0).comp (C ((d : ℝ)⁻¹) * X)).map (algebraMap ℝ ℂ)

/-- The independent finite falling-factorial sum for the fixed density moments. -/
def sourceJensenPolynomial (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (((d.descFactorial k : ℕ) : ℂ) / (d : ℂ) ^ k * (sourceThetaCoefficient k : ℂ)) *
      X ^ k

private theorem source_xi_center_real :
    ((xiReading (1 / 2 : ℂ)).re : ℂ) = xiReading (1 / 2 : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  simpa only [map_div₀, map_one, map_ofNat] using
    (Symmetry.ZetaConjugationCovariance.xi_reading_conj (1 / 2 : ℂ)).symm

private theorem source_density_complex (x : ℝ) :
    (sourceThetaDensity x : ℂ) = (sourceThetaKernel x : ℂ) / xiReading (1 / 2 : ℂ) := by
  rw [sourceThetaDensity, Complex.ofReal_div, source_xi_center_real]

/-- The canonical adapter has exactly the finite falling-factorial normalization. -/
theorem normalizedJensen_eq_fallingFactorial_sum (a : ℕ → ℝ) (d : ℕ) (_hd : 1 ≤ d) :
    normalizedJensen a d = ∑ k ∈ Finset.range (d + 1),
      C ((d.descFactorial k : ℂ) / (d : ℂ) ^ k * (a k : ℂ)) * X ^ k := by
  unfold normalizedJensen JensenPolynomialObstruction.jensenPolynomial
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, mul_pow, ← C_pow,
    ← mul_assoc, ← C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  simp [Nat.descFactorial_eq_factorial_mul_choose, div_eq_mul_inv,
    mul_comm, mul_left_comm]

private theorem normalizedJensen_coeff (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    (normalizedJensen a d).coeff k =
      (d.descFactorial k : ℂ) / (d : ℂ) ^ k * (a k : ℂ) := by
  rw [normalizedJensen_eq_fallingFactorial_sum a d hd]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k ≤ d
  · simp [Finset.mem_range, hk]
  · simp [Finset.mem_range, hk,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hk)]

private theorem falling_degree_lowering (d k : ℕ) (hd : 1 ≤ d) :
    (d.descFactorial k : ℂ) - (d : ℂ)⁻¹ * ((d.descFactorial k : ℂ) * (k : ℂ)) =
      ((d - 1).descFactorial k : ℂ) := by
  by_cases hk : k ≤ d
  · have hnat := Nat.succ_descFactorial (d - 1) k
    rw [Nat.sub_add_cancel hd] at hnat
    have hcast := congrArg (fun n : ℕ => (n : ℂ)) hnat
    push_cast at hcast
    rw [Nat.cast_sub hk] at hcast
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
    linear_combination hcast
  · have hkd : d < k := Nat.lt_of_not_ge hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkd,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : d - 1 < k)]
    simp

/-- Degree lowering for every real coefficient sequence, as a complex polynomial identity. -/
theorem normalizedJensen_degree_lowering (a : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) :
    normalizedJensen a d - C ((d : ℂ)⁻¹) * X * (normalizedJensen a d).derivative =
      (normalizedJensen a (d - 1)).comp (C (((d - 1 : ℕ) : ℂ) / (d : ℂ)) * X) := by
  have hd1 : 1 ≤ d := by omega
  have hm1 : 1 ≤ d - 1 := by omega
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hm0 : ((d - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : d - 1 ≠ 0)
  have hder (p : ℂ[X]) (k : ℕ) : (X * p.derivative).coeff k = p.coeff k * (k : ℂ) := by
    cases k with
    | zero => simp
    | succ k => simp [coeff_X_mul, coeff_derivative]
  ext k
  simp only [coeff_sub, mul_assoc, coeff_C_mul, hder, comp_C_mul_X_coeff,
    normalizedJensen_coeff a d hd1, normalizedJensen_coeff a (d - 1) hm1]
  calc
    _ = ((d.descFactorial k : ℂ) - (d : ℂ)⁻¹ *
        ((d.descFactorial k : ℂ) * (k : ℂ))) / (d : ℂ) ^ k * (a k : ℂ) := by ring
    _ = ((d - 1).descFactorial k : ℂ) / (d : ℂ) ^ k * (a k : ℂ) := by
      rw [falling_degree_lowering d k hd1]
    _ = _ := by rw [div_pow]; field_simp

/-- The independent source sum equals the normalized canonical Jensen polynomial. -/
theorem sourceJensenPolynomial_eq_normalizedJensen (d : ℕ) (hd : 1 ≤ d) :
    sourceJensenPolynomial d = normalizedJensen sourceThetaCoefficient d := by
  exact (normalizedJensen_eq_fallingFactorial_sum sourceThetaCoefficient d hd).symm

/-- Exact degree lowering for the fixed theta-density moments at every complex argument. -/
theorem source_jensen_degree_lowering (d : ℕ) (hd : 2 ≤ d) (v : ℂ) :
    (sourceJensenPolynomial d).eval v - (v / (d : ℂ)) *
        (sourceJensenPolynomial d).derivative.eval v =
      (sourceJensenPolynomial (d - 1)).eval ((((d - 1 : ℕ) : ℂ) / (d : ℂ)) * v) := by
  rw [sourceJensenPolynomial_eq_normalizedJensen d (by omega),
    sourceJensenPolynomial_eq_normalizedJensen (d - 1) (by omega)]
  have h := congrArg (Polynomial.eval v)
    (normalizedJensen_degree_lowering sourceThetaCoefficient d hd)
  simpa only [eval_sub, eval_mul, eval_comp, eval_C, eval_X, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using h

end D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
