/- GID: D5/S3/Analytic/Polynomial/DiagonalPadeExponential
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadeExponential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized diagonal exponential Padé denominator and its Bessel connection. -/
module

public import D5.S3.Analytic.HalfIntegerBessel
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The diagonal Padé denominator of the exponential

The rational polynomial is the diagonal specialization of Scardino's formula (1.1).
Its reversed Bessel representation uses the principal square root on `0 < z.re`.

Escape audit unfinished for the three public theorems.
https://github.com/the-omega-institute/trureturing/issues/32304
-/

public section

open Polynomial
open scoped Nat Topology
open D5.S3.Analytic.HalfIntegerBessel (I K L prefactor reverse_eval sqrt_real_mul)
open D5.S3.Analytic.HalfIntegerBesselPolynomial
  (carrier coefficient coeff_carrier natDegree_carrier)

namespace D5.S3.Analytic.Polynomial.DiagonalPadeExponential

/-- The denominator of the diagonal exponential Padé approximant, normalized at zero. -/
noncomputable def denominator (m : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (m + 1),
    monomial j ((-1 : ℚ) ^ j * (m.choose j : ℚ) * ((2 * m - j)! : ℚ) / ((2 * m)! : ℚ))

/-- The factorial factor in the Bessel representation of the normalized denominator. -/
noncomputable def normalization (m : ℕ) : ℚ := (m ! : ℚ) / ((2 * m)! : ℚ)

private theorem denominator_coeff (m j : ℕ) :
    (denominator m).coeff j =
      (-1 : ℚ) ^ j * (m.choose j : ℚ) * ((2 * m - j)! : ℚ) / ((2 * m)! : ℚ) := by
  by_cases hj : j ≤ m
  · simp [denominator, coeff_monomial, Finset.mem_range, hj]
  · simp [denominator, coeff_monomial, Finset.mem_range, hj,
      Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]

private theorem denominator_coeff_zero (m : ℕ) : (denominator m).coeff 0 = 1 := by
  rw [denominator_coeff]
  simp [Nat.factorial_ne_zero]

/-- Reverse the finite carrier, substitute `-X/2`, and normalize the constant term. -/
theorem denominator_eq_reverse (m : ℕ) :
    denominator m = C (normalization m * 2 ^ m) * (carrier m).reverse.comp (C (-1 / 2) * X) := by
  ext j
  rw [denominator_coeff, coeff_C_mul, comp_C_mul_X_coeff, coeff_reverse, natDegree_carrier]
  by_cases hj : j ≤ m
  · rw [revAt_le hj, coeff_carrier, coefficient, ite_eq_left (Nat.sub_le _ _), Nat.cast_choose ℚ hj,
      show m + (m - j) = 2 * m - j by omega, show m - (m - j) = j by omega]
    have hp : (2 : ℚ) ^ (m - j) * 2 ^ j = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hj]
    have hfact (k : ℕ) : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [normalization, div_pow, ← hp]
    field_simp [hfact]
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hj), revAt_eq_self_of_lt (lt_of_not_ge hj),
      coeff_carrier, coefficient, ite_eq_right hj]
    simp

/-- The factorial and principal square-root factor in the exact connection. -/
noncomputable def connectionFactor (m : ℕ) (z : ℂ) : ℂ :=
  (normalization m : ℂ) * z ^ m * Complex.sqrt (z / (Real.pi : ℂ))

private theorem sqrt_mul_prefactor {z : ℂ} (hz : 0 < z.re) :
    Complex.sqrt (z / (Real.pi : ℂ)) * prefactor (z / 2) = 1 := by
  have hhalf : 0 < (z / 2).re := by rw [Complex.div_ofNat_re]; positivity
  have harg : z / (Real.pi : ℂ) = ((2 / Real.pi : ℝ) : ℂ) * (z / 2) := by
    push_cast
    ring
  have hscale : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have hp := Real.pi_ne_zero
    rw [show 2 / Real.pi * (Real.pi / 2) = 1 by field_simp, Real.sqrt_one]
  have hzhalf : z / 2 ≠ 0 := by
    intro h
    simp [h] at hhalf
  have hroot : Complex.sqrt (z / 2) ≠ 0 := by
    intro h
    apply hzhalf
    have hs : Complex.sqrt (z / 2) ^ 2 = z / 2 :=
      Complex.cpow_nat_inv_pow (z / 2) (by decide : (2 : ℕ) ≠ 0)
    simpa [h] using hs.symm
  rw [harg, sqrt_real_mul (by positivity) hhalf, prefactor]
  rw [mul_comm (Real.sqrt (2 / Real.pi) : ℂ), mul_assoc, ← mul_div_assoc,
    ← Complex.ofReal_mul, hscale, Complex.ofReal_one, one_div, mul_inv_cancel₀ hroot]

/-- The normalized diagonal denominator is the exact regular/decaying combination. -/
theorem denominator_eq_bessel (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    connectionFactor m z ≠ 0 ∧
      aeval z (denominator m) = connectionFactor m z * Complex.exp (-(z / 2)) *
        (K m (z / 2) + (-1 : ℂ) ^ m * (Real.pi : ℂ) * I m (z / 2)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hcancel := sqrt_mul_prefactor hz
  constructor
  · have hnorm : (normalization m : ℂ) ≠ 0 := by
      exact_mod_cast (show normalization m ≠ 0 from div_ne_zero (by positivity) (by positivity))
    exact mul_ne_zero (mul_ne_zero hnorm (pow_ne_zero _ hz0))
      (left_ne_zero_of_mul (hcancel.trans_ne one_ne_zero))
  · have ht : -(z / 2) ≠ 0 := by simp [hz0]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
      rw [← mul_pow]; simp
    have hcombine : K m (z / 2) + (-1 : ℂ) ^ m * (Real.pi : ℂ) * I m (z / 2) =
        (-1 : ℂ) ^ m * L m (z / 2) := by
      have hI : (Real.pi : ℂ) * I m (z / 2) = L m (z / 2) - (-1 : ℂ) ^ m * K m (z / 2) := by
        rw [I]
        field_simp
      rw [mul_assoc, hI, mul_sub, ← mul_assoc ((-1 : ℂ) ^ m), hsign, one_mul]
      ring
    have hpow : (2 : ℂ) ^ m * (-(z / 2)) ^ m = (-1 : ℂ) ^ m * z ^ m := by
      rw [← mul_pow, ← mul_pow, show 2 * -(z / 2) = -1 * z by ring]
    have harg : aeval z (C (-1 / 2 : ℚ) * X) = -(z / 2) := by
      rw [map_mul, aeval_C, aeval_X]
      change ((-1 / 2 : ℚ) : ℂ) * z = _
      push_cast
      ring
    rw [denominator_eq_reverse, map_mul, aeval_C, aeval_comp, harg, reverse_eval m ht,
      hcombine, L, aeval_comp, map_neg, aeval_X, inv_neg, connectionFactor,
      Complex.exp_neg]
    change ((normalization m * 2 ^ m : ℚ) : ℂ) * _ = _
    push_cast
    calc
      _ = (normalization m : ℂ) * ((-1 : ℂ) ^ m * z ^ m) *
          aeval (-(z / 2)⁻¹) (carrier m) := by rw [← hpow]; ring
      _ = _ := by
        symm
        calc
          _ = Complex.sqrt (z / (Real.pi : ℂ)) * prefactor (z / 2) *
              ((Complex.exp (z / 2))⁻¹ * Complex.exp (z / 2)) *
              ((normalization m : ℂ) * ((-1 : ℂ) ^ m * z ^ m) *
                aeval (-(z / 2)⁻¹) (carrier m)) := by ring
          _ = _ := by rw [hcancel, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul, one_mul]

/-- The rational coefficient of degree `n` in the formal reciprocal at zero. -/
noncomputable def reciprocalCoefficient (m n : ℕ) : ℚ :=
  PowerSeries.coeff n ((denominator m : PowerSeries ℚ)⁻¹)

private theorem cast_reciprocal (m : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) ((denominator m : PowerSeries ℚ)⁻¹) =
      (PowerSeries.map (algebraMap ℚ ℂ) (denominator m : PowerSeries ℚ))⁻¹ := by
  have h : PowerSeries.constantCoeff (denominator m : PowerSeries ℚ) = 1 := by
    simpa using denominator_coeff_zero m
  have hmap : PowerSeries.constantCoeff (PowerSeries.map (algebraMap ℚ ℂ)
      (denominator m : PowerSeries ℚ)) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, h, map_one]
    exact one_ne_zero
  apply (PowerSeries.eq_inv_iff_mul_eq_one hmap).2
  rw [← map_mul, PowerSeries.inv_mul_cancel _ (by simp [h]), map_one]

private theorem hasSum_aeval (q : ℚ[X]) (z : ℂ) :
    HasSum (fun n ↦ z ^ n * (q.coeff n : ℂ)) (aeval z q) := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum]
  simpa only [Algebra.algebraMap_eq_smul_one, smul_eq_mul, Rat.smul_one_eq_cast, mul_comm] using
    (hasSum_sum_of_ne_finset_zero (s := q.support) fun n hn ↦ by simp [notMem_support_iff.mp hn] :
      HasSum (fun n ↦ z ^ n * (q.coeff n : ℂ)) (∑ n ∈ q.support, z ^ n * (q.coeff n : ℂ)))

/-- The rational formal inverse gives the actual complex Taylor expansion of the reciprocal. -/
theorem hasFPowerSeriesAt_reciprocal (m : ℕ) :
    HasFPowerSeriesAt (fun z : ℂ ↦ (aeval z (denominator m))⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (reciprocalCoefficient m n : ℂ)) 0 := by
  let q := denominator m
  let Q : PowerSeries ℂ := PowerSeries.map (algebraMap ℚ ℂ) (q : PowerSeries ℚ)
  have hzero : aeval (0 : ℂ) q = 1 := by
    rw [aeval_def, eval₂_at_zero, show q.coeff 0 = 1 from denominator_coeff_zero m, map_one]
  have hQ (n : ℕ) : PowerSeries.coeff n Q = (q.coeff n : ℂ) := by simp [Q]
  have hQ0 : PowerSeries.constantCoeff Q ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, hQ, denominator_coeff_zero]; norm_num
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ aeval z q) 0 := analyticAt_id.aeval_polynomial q
  have haInv : AnalyticAt ℂ (fun z : ℂ ↦ (aeval z q)⁻¹) 0 := ha.inv (by simp [hzero])
  obtain ⟨p, r, hp⟩ := haInv
  let P : PowerSeries ℂ := PowerSeries.mk p.coeff
  have hP (n : ℕ) : PowerSeries.coeff n P = p.coeff n := by simp [P]
  have hm : HasFPowerSeriesAt (fun _ : ℂ ↦ (1 : ℂ))
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ PowerSeries.coeff n (Q * P)) 0 := by
    rw [hasFPowerSeriesAt_iff]
    have hne : aeval (0 : ℂ) q ≠ 0 := by simp [hzero]
    filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hp.r_pos, ha.continuousAt.eventually_ne hne] with z hz hnz
    have hleft : Summable fun n ↦ ‖z ^ n * (q.coeff n : ℂ)‖ :=
      summable_of_ne_finset_zero (s := q.support) fun n hn ↦ by simp [notMem_support_iff.mp hn]
    have hz' : z ∈ Metric.eball (0 : ℂ) p.radius := Metric.eball_subset_eball hp.r_le hz
    have hright : Summable fun n ↦ ‖z ^ n * p.coeff n‖ := by
      simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using
        p.summable_norm_apply hz'
    have hsright : HasSum (fun n ↦ z ^ n * p.coeff n) (aeval z q)⁻¹ := by
      simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using
        hp.hasSum hz
    have hterm (n : ℕ) :
        z ^ n * PowerSeries.coeff n (Q * P) =
          ∑ ij ∈ Finset.antidiagonal n, (z ^ ij.1 * (q.coeff ij.1 : ℂ)) * (z ^ ij.2 * p.coeff ij.2) := by
      rw [PowerSeries.coeff_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hQ, hP, ← Finset.mem_antidiagonal.mp hij, pow_add]
      ring
    simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, hterm]
    have hsum : (∑' n, ∑ ij ∈ Finset.antidiagonal n,
        (z ^ ij.1 * (q.coeff ij.1 : ℂ)) * (z ^ ij.2 * p.coeff ij.2)) = 1 := by
      rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hleft hright,
        (hasSum_aeval q z).tsum_eq, hsright.tsum_eq, mul_inv_cancel₀ hnz]
    rw [← hsum]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hleft hright).of_norm.hasSum
  have hone : HasFPowerSeriesAt (fun _ : ℂ ↦ (1 : ℂ))
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ PowerSeries.coeff n (1 : PowerSeries ℂ)) 0 := by
    rw [hasFPowerSeriesAt_iff]
    refine Filter.Eventually.of_forall fun z ↦ ?_
    simp only [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_one, smul_eq_mul]
    have hs := hasSum_single (f := fun n ↦ z ^ n * (if n = 0 then 1 else 0)) 0
      (fun n hn ↦ by simp [hn])
    rw [show z ^ (0 : ℕ) * (if (0 : ℕ) = 0 then 1 else 0) = 1 by simp] at hs
    exact hs
  have hprod : Q * P = 1 := by
    ext n
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun a : FormalMultilinearSeries ℂ ℂ ℂ ↦ a.coeff n) (hm.eq_formalMultilinearSeries hone)
  have hinv : P = Q⁻¹ := (PowerSeries.eq_inv_iff_mul_eq_one hQ0).2 (by rwa [mul_comm])
  have hcoeff (n : ℕ) : p.coeff n = (reciprocalCoefficient m n : ℂ) := by
    rw [← hP, hinv, ← cast_reciprocal m, PowerSeries.coeff_map]
    rfl
  have hseries : p = FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (reciprocalCoefficient m n : ℂ)) := by
    ext n
    simp [FormalMultilinearSeries.ofScalars, FormalMultilinearSeries.apply_eq_prod_smul_coeff, hcoeff]
  exact hseries ▸ hp.hasFPowerSeriesAt

end D5.S3.Analytic.Polynomial.DiagonalPadeExponential
