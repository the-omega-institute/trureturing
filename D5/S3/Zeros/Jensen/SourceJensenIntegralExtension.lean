/- GID: D5/S3/Zeros/Jensen/SourceJensenIntegralExtension
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/SourceJensenIntegralExtension
   mirror-E: none(waiver:universal-polynomial-integral)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Adjacent source Jensen polynomials differ by one exact integration constant. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open Polynomial NormalizedJensenDegreeLowering

/-- The real coefficient model of the fixed source polynomial. -/
def sourceP (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C ((d.descFactorial k : ℝ) / (d : ℝ)^k * sourceThetaCoefficient k) * X^k

private def reflected (p : ℝ[X]) (d : ℕ) : ℝ[X] :=
  (p.comp (C (-1) * X)).reflect d

/-- Polynomial reflection, including its actual constant term at zero. -/
def sourceQ (d : ℕ) : ℝ[X] := reflected (sourceP d) d

/-- The adjacent-degree dilation; all theorems use d at least two. -/
def scale (d : ℕ) : ℝ := ((d - 1 : ℕ) : ℝ) / (d : ℝ)

/-- The specified signed top coefficient. -/
def sourceConstant (d : ℕ) : ℝ :=
  (-1 : ℝ)^d * (d.factorial : ℝ) / (d : ℝ)^d * sourceThetaCoefficient d

/-- The primitive fixed at zero, with oriented real interval integration. -/
def sourcePrimitive (d : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, (d : ℝ) * scale d ^ (d - 1) *
    (sourceQ (d - 1)).eval (u / scale d)

private theorem source_map (d : ℕ) :
    (sourceP d).map (algebraMap ℝ ℂ) = sourceJensenPolynomial d := by
  simp only [sourceP, sourceJensenPolynomial, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
  congr 1
  funext k
  push_cast
  rfl

private theorem source_degree (d : ℕ) : (sourceP d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using Finset.mem_range.mp hk)

private theorem scale_ne_zero (d : ℕ) (hd : 2 ≤ d) : scale d ≠ 0 := by
  apply div_ne_zero <;> exact_mod_cast (show _ ≠ 0 by omega)

private theorem source_lowering (d : ℕ) (hd : 2 ≤ d) :
    sourceP d - C ((d : ℝ)⁻¹) * X * (sourceP d).derivative =
      (sourceP (d - 1)).comp (C (scale d) * X) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  have h := normalizedJensen_degree_lowering sourceThetaCoefficient d hd
  rw [← sourceJensenPolynomial_eq_normalizedJensen d (by omega),
    ← sourceJensenPolynomial_eq_normalizedJensen (d - 1) (by omega)] at h
  simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X,
    ← derivative_map, map_comp, source_map, scale, map_inv₀, map_natCast, map_div₀]
  exact h

private theorem reflect_transport (p r : ℝ[X]) (d : ℕ) (hd : 2 ≤ d)
    (hp : p.natDegree ≤ d) (hr : r.natDegree ≤ d - 1)
    (h : p - C ((d : ℝ)⁻¹) * X * p.derivative = r.comp (C (scale d) * X)) :
    (reflected p d).derivative =
      C ((d : ℝ) * scale d ^ (d - 1)) * (reflected r (d - 1)).comp (C ((scale d)⁻¹) * X) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have ha0 := scale_ne_zero d hd
  have hder (f : ℝ[X]) (n : ℕ) : (X * f.derivative).coeff n = f.coeff n * (n : ℝ) := by
    cases n <;> simp [coeff_X_mul, coeff_derivative]
  ext k
  by_cases hk : k < d
  · have hk1 : k + 1 ≤ d := by omega
    have hk2 : k ≤ d - 1 := by omega
    have hind : d - 1 - k = d - (k + 1) := by omega
    have hcoeff := congrArg (fun f : ℝ[X] => f.coeff (d - (k + 1))) h
    simp only [coeff_sub, mul_assoc, coeff_C_mul, hder, comp_C_mul_X_coeff] at hcoeff
    simp only [reflected, coeff_derivative, coeff_reflect, revAt_le hk1, coeff_C_mul,
      comp_C_mul_X_coeff, revAt_le hk2, hind]
    have hcast : ((d - (k + 1) : ℕ) : ℝ) = (d : ℝ) - ((k : ℝ) + 1) := by
      rw [Nat.cast_sub hk1]
      push_cast
      rfl
    rw [hcast] at hcoeff
    have hpow : scale d ^ (d - 1) * (scale d)⁻¹ ^ k = scale d ^ (d - (k + 1)) := by
      rw [← hind, pow_sub₀ (scale d) ha0 hk2, inv_pow]
    calc
      _ = (d : ℝ) * (r.coeff (d - (k + 1)) * scale d ^ (d - (k + 1))) *
          (-1 : ℝ) ^ (d - (k + 1)) := by
        field_simp at hcoeff
        linear_combination (-1 : ℝ) ^ (d - (k + 1)) * hcoeff
      _ = _ := by rw [← hpow]; ring
  · have hk1 : d < k + 1 := by omega
    have hk2 : d - 1 < k := by omega
    simp only [reflected, coeff_derivative, coeff_reflect, revAt_eq_self_of_lt hk1,
      coeff_C_mul, comp_C_mul_X_coeff, revAt_eq_self_of_lt hk2]
    rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hk1),
      coeff_eq_zero_of_natDegree_lt (hr.trans_lt hk2)]
    simp

private theorem source_derivative (d : ℕ) (hd : 2 ≤ d) :
    (sourceQ d).derivative = C ((d : ℝ) * scale d ^ (d - 1)) *
      (sourceQ (d - 1)).comp (C ((scale d)⁻¹) * X) :=
  reflect_transport _ _ d hd (source_degree d) (source_degree (d - 1))
    (source_lowering d hd)

private theorem source_zero (d : ℕ) : (sourceQ d).eval 0 = sourceConstant d := by
  rw [← coeff_zero_eq_eval_zero]
  simp only [sourceQ, reflected, coeff_reflect, revAt_zero, comp_C_mul_X_coeff,
    sourceP, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Finset.mem_range, Nat.descFactorial_self, sourceConstant]
  ring

private theorem source_integral (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    (sourceQ d).eval x = sourcePrimitive d x + sourceConstant d := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x) (fun u _ => (sourceQ d).hasDerivAt u)
    ((sourceQ d).derivative.continuous.intervalIntegrable 0 x)
  have hder (u : ℝ) : (sourceQ d).derivative.eval u =
      (d : ℝ) * scale d ^ (d - 1) * (sourceQ (d - 1)).eval (u / scale d) := by
    rw [source_derivative d hd]
    simp only [eval_mul, eval_C, eval_comp, eval_X, div_eq_mul_inv]
    rw [mul_comm ((scale d)⁻¹) u]
  simp_rw [hder] at hFTC
  simpa only [sourcePrimitive, source_zero, sub_add_cancel] using
    eq_add_of_sub_eq hFTC.symm

/-- The actual reflection, complete derivative, primitive and signed constant.
Changing the constant preserves every critical point, shifts every height, and
can include or exclude any prescribed real point from the real zero set. -/
theorem source_jensen_integral_extension (d : ℕ) (hd : 2 ≤ d) :
    (sourceQ d).map (algebraMap ℝ ℂ) =
      ((sourceJensenPolynomial d).comp (C (-1) * X)).reflect d ∧
    (sourceQ d).derivative = C ((d : ℝ) * scale d ^ (d - 1)) *
      (sourceQ (d - 1)).comp (C ((scale d)⁻¹) * X) ∧
    (sourceQ d).eval 0 = sourceConstant d ∧
    (∀ x : ℝ, (sourceQ d).eval x = sourcePrimitive d x + sourceConstant d) ∧
    (∀ b : ℝ, (sourceQ d + C (b - sourceConstant d)).derivative =
        (sourceQ d).derivative ∧
      ∀ x : ℝ, (sourceQ d + C (b - sourceConstant d)).eval x = sourcePrimitive d x + b ∧
        ((sourceQ d + C (b - sourceConstant d)).eval x = 0 ↔ sourcePrimitive d x = -b)) ∧
    (∀ x : ℝ, ∃ b₀ b₁ : ℝ,
      (sourceQ d + C (b₀ - sourceConstant d)).eval x = 0 ∧
      (sourceQ d + C (b₁ - sourceConstant d)).eval x ≠ 0) := by
  have hshift (b x : ℝ) :
      (sourceQ d + C (b - sourceConstant d)).eval x = sourcePrimitive d x + b := by
    rw [eval_add, eval_C, source_integral d hd x]
    ring
  refine ⟨?_, source_derivative d hd, source_zero d, source_integral d hd, ?_, ?_⟩
  · rw [sourceQ, reflected, ← reflect_map, map_comp]
    simp only [Polynomial.map_mul, map_C, map_X, source_map]
    norm_num
  · intro b
    refine ⟨by simp, fun x => ⟨hshift b x, ?_⟩⟩
    rw [hshift]
    exact add_eq_zero_iff_eq_neg
  · intro x
    refine ⟨-sourcePrimitive d x, 1 - sourcePrimitive d x, ?_, ?_⟩
    · rw [hshift]; ring
    · rw [hshift]; norm_num [add_sub_cancel_left]

#print axioms source_jensen_integral_extension
end D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
