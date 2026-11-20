/- GID: D5/S3/Analytic/Polynomial/DiagonalPadeExponential
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadeExponential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized diagonal exponential Padé denominator and its Bessel connection. -/
module

public import D5.S3.Analytic.HalfIntegerBesselSector
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The diagonal Padé denominator of the exponential

The rational polynomial is the diagonal specialization of Scardino's formula (1.1).
Its reversed Bessel representation uses the principal square root on `0 < z.re`.

Escape audit unfinished for the public theorems in this module.
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

private theorem eval_denominator_zero (m : ℕ) : aeval (0 : ℂ) (denominator m) = 1 := by
  rw [aeval_def, eval₂_at_zero, denominator_coeff_zero, map_one]

private theorem normalization_ne_zero (m : ℕ) : (normalization m : ℂ) ≠ 0 := by
  exact_mod_cast (show normalization m ≠ 0 from div_ne_zero (by positivity) (by positivity))

private theorem eval_denominator_reciprocal (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    aeval z (denominator m) =
      (normalization m : ℂ) * (-z) ^ m * aeval (-2 / z) (carrier m) := by
  have harg : aeval z (C (-1 / 2 : ℚ) * X) = -(z / 2) := by
    rw [map_mul, aeval_C, aeval_X]
    change ((-1 / 2 : ℚ) : ℂ) * z = _
    push_cast
    ring
  rw [denominator_eq_reverse, map_mul, aeval_C, aeval_comp, harg,
    reverse_eval m (by simp [hz])]
  change ((normalization m * 2 ^ m : ℚ) : ℂ) * _ = _
  push_cast
  rw [mul_assoc, ← mul_assoc ((2 : ℂ) ^ m), ← mul_pow,
    show 2 * -(z / 2) = -z by ring, show (-(z / 2))⁻¹ = -2 / z by
      rw [inv_neg, inv_div, neg_div], mul_assoc]

/-- The reflected carrier Wronskian gives the signed derivative at each complex root.
In particular, zero is not a root and each root has nonzero derivative. -/
theorem denominator_root_derivative (m : ℕ) {z : ℂ}
    (hz : aeval z (denominator m) = 0) :
    z ≠ 0 ∧ aeval z (denominator m).derivative ≠ 0 ∧
      aeval (-z) (denominator m) * aeval z (denominator m).derivative =
        (-1 : ℂ) ^ m * (normalization m : ℂ) ^ 2 * z ^ (2 * m) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact one_ne_zero ((eval_denominator_zero m).symm.trans hz)
  have hn := normalization_ne_zero m
  have hcarrier : aeval (-2 / z) (carrier m) = 0 := by
    rw [eval_denominator_reciprocal m hz0] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hn (pow_ne_zero _ (neg_ne_zero.mpr hz0)))
  have hreflect : aeval (-z) (denominator m) =
      (normalization m : ℂ) * z ^ m * aeval (2 / z) (carrier m) := by
    rw [eval_denominator_reciprocal m (neg_ne_zero.mpr hz0), neg_neg, div_neg, neg_div, neg_neg]
  have hdiff : HasDerivAt (fun t : ℂ ↦ -2 / t) (2 / z ^ 2) z := by
    convert (hasDerivAt_inv hz0).const_mul (-2 : ℂ) using 1
    · ext t
      simp [div_eq_mul_inv]
    · ring
  have hchain := ((carrier m).hasDerivAt_aeval (-2 / z)).comp z hdiff
  have hprod := (((hasDerivAt_id z).neg.pow m).const_mul (normalization m : ℂ)).mul hchain
  have hderiv : aeval z (denominator m).derivative =
      (normalization m : ℂ) * (-z) ^ m *
        (aeval (-2 / z) (carrier m).derivative * (2 / z ^ 2)) := by
    have heq : (fun t : ℂ ↦ (normalization m : ℂ) * (-t) ^ m * aeval (-2 / t) (carrier m))
        =ᶠ[𝓝 z] fun t ↦ aeval t (denominator m) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with t ht using (eval_denominator_reciprocal m ht).symm
    have hh := hprod.congr_of_eventuallyEq heq.symm
    rw [← ((denominator m).hasDerivAt_aeval z).deriv, hh.deriv]
    simp [Function.comp_apply, hcarrier, mul_comm]
  have hw := congrArg (aeval (2 / z : ℂ))
    (D5.S3.Analytic.HalfIntegerBesselPolynomial.reflected_wronskian m)
  have hw' : (2 / z : ℂ) ^ 2 *
      (aeval (2 / z) (carrier m) * aeval (-2 / z) (carrier m).derivative) = 2 := by
    simpa [derivative_comp, aeval_comp, ← neg_div, hcarrier, sub_eq_add_neg] using hw
  have hs : aeval (-z) (denominator m) * aeval z (denominator m).derivative =
      (-1 : ℂ) ^ m * (normalization m : ℂ) ^ 2 * z ^ (2 * m) := by
    rw [hreflect, hderiv, neg_eq_neg_one_mul z, mul_pow, two_mul, pow_add]
    have hp : aeval (2 / z) (carrier m) *
        (aeval (-2 / z) (carrier m).derivative * (2 / z ^ 2)) = 1 := by
      field_simp [hz0] at hw' ⊢
      linear_combination hw'
    linear_combination ((normalization m : ℂ) ^ 2 * (-1 : ℂ) ^ m * z ^ m * z ^ m) * hp
  exact ⟨hz0, right_ne_zero_of_mul (hs.trans_ne (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hn))
    (pow_ne_zero _ hz0))), hs⟩

/-- The coefficient of the geometric term `(1 - z / ζ)⁻¹` at a simple pole `ζ`. -/
noncomputable def residueWeight (m : ℕ) (ζ : ℂ) : ℂ :=
  -(ζ * aeval ζ (denominator m).derivative)⁻¹

/-- At an odd-order pole the geometric weight is the reflected denominator with factorial scale. -/
theorem residueWeight_eq (m : ℕ) (hm : Odd m) {ζ : ℂ}
    (hζ : aeval ζ (denominator m) = 0) :
    residueWeight m ζ =
      aeval (-ζ) (denominator m) / ((normalization m : ℂ) ^ 2 * ζ ^ (2 * m + 1)) := by
  obtain ⟨hζ0, hd, hs⟩ := denominator_root_derivative m hζ
  rw [hm.neg_one_pow, neg_one_mul] at hs
  rw [residueWeight, pow_succ]
  field_simp [normalization_ne_zero m, hζ0, hd]
  linear_combination -ζ * hs

private theorem natDegree_denominator (m : ℕ) : (denominator m).natDegree = m := by
  apply le_antisymm
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ by
      simp [denominator_coeff, Nat.choose_eq_zero_of_lt hj]
  · apply le_natDegree_of_ne_zero
    rw [denominator_coeff, Nat.choose_self, Nat.cast_one, mul_one, show 2 * m - m = m by omega]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) (by positivity)

private theorem denominator_ne_zero (m : ℕ) : denominator m ≠ 0 := by
  intro h
  simpa [h] using denominator_coeff_zero m

private theorem eval_complexDenominator (m : ℕ) (z : ℂ) :
    ((denominator m).map (algebraMap ℚ ℂ)).eval z = aeval z (denominator m) := by
  rw [aeval_def, eval_map]

private theorem eval_derivative_complexDenominator (m : ℕ) (z : ℂ) :
    ((denominator m).map (algebraMap ℚ ℂ)).derivative.eval z = aeval z (denominator m).derivative := by
  rw [derivative_map, aeval_def, eval_map]

private theorem denominator_aroots_nodup (m : ℕ) : ((denominator m).aroots ℂ).Nodup := by
  classical
  let Q := (denominator m).map (algebraMap ℚ ℂ)
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr (denominator_ne_zero m)
  change Q.roots.Nodup
  rw [Multiset.nodup_iff_count_le_one]
  intro ζ
  rw [count_roots]
  by_contra! hm
  obtain ⟨hz, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hQ).1 hm
  rw [IsRoot.def, eval_complexDenominator] at hz
  rw [IsRoot.def, eval_derivative_complexDenominator] at hd
  exact (denominator_root_derivative m hz).2.1 hd

private theorem reciprocal_eq_sum (m : ℕ) (hm : 0 < m) {z : ℂ}
    (hz : aeval z (denominator m) ≠ 0) :
    (aeval z (denominator m))⁻¹ =
      ∑ ζ ∈ ((denominator m).aroots ℂ).toFinset,
        residueWeight m ζ * (1 - z / ζ)⁻¹ := by
  classical
  let Q := (denominator m).map (algebraMap ℚ ℂ)
  let S := Q.roots.toFinset
  let N := Lagrange.nodal S (id : ℂ → ℂ)
  have hQ : Q ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr (denominator_ne_zero m)
  have hlead : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hs : S.val = Q.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (denominator_aroots_nodup m)]
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < S.val.card
    rw [hs, ← (IsAlgClosed.splits Q).natDegree_eq_card_roots]
    simpa [Q, natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, natDegree_denominator] using hm
  have hfactor : Q = C Q.leadingCoeff * N := by
    rw [show N = Lagrange.nodal S id by rfl, Lagrange.nodal_eq]
    change Q = C Q.leadingCoeff * (S.val.map (fun ξ ↦ X - C ξ)).prod
    rw [hs]
    exact (IsAlgClosed.splits Q).eq_prod_roots
  have hroot {ζ : ℂ} (hζ : ζ ∈ S) : aeval ζ (denominator m) = 0 := by
    rw [← eval_complexDenominator]
    exact (mem_roots hQ).mp (Multiset.mem_toFinset.mp hζ)
  have hzζ (ζ : ℂ) (hζ : ζ ∈ S) : z ≠ id ζ := fun h ↦ hz (h ▸ hroot hζ)
  have hsum := Lagrange.eval_interpolate_not_at_node (v := id) (r := (1 : ℂ → ℂ)) hzζ
  rw [Lagrange.interpolate_one (v := id) (fun _ _ _ _ h ↦ h) hS] at hsum
  simp only [eval_one, Pi.one_apply, mul_one, id_eq] at hsum
  have hqz : Q.eval z = Q.leadingCoeff * N.eval z := by
    conv_lhs => rw [hfactor]
    simp
  have hNz : N.eval z ≠ 0 := by
    intro h
    apply hz
    rw [← eval_complexDenominator]
    simpa only [h, mul_zero] using hqz
  have hD (ζ : ℂ) : Q.derivative.eval ζ = Q.leadingCoeff * N.derivative.eval ζ := by
    conv_lhs => rw [hfactor, derivative_C_mul]
    simp
  have hweight (ζ : ℂ) (hζ : ζ ∈ S) :
      (Q.leadingCoeff)⁻¹ * (Lagrange.nodalWeight S id ζ * (z - ζ)⁻¹) =
        residueWeight m ζ * (1 - z / ζ)⁻¹ := by
    have hζ0 := (denominator_root_derivative m (hroot hζ)).1
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hζ, id_eq, residueWeight]
    change Q.leadingCoeff⁻¹ * ((N.derivative.eval ζ)⁻¹ * (z - ζ)⁻¹) =
      -(ζ * aeval ζ (denominator m).derivative)⁻¹ * (1 - z / ζ)⁻¹
    rw [← eval_derivative_complexDenominator, show (1 - z / ζ) = -(z - ζ) / ζ by field_simp; ring]
    change _ = -(ζ * Q.derivative.eval ζ)⁻¹ * _
    rw [hD]
    field_simp [hζ0, sub_ne_zero.mpr (hzζ ζ hζ), hlead]
  change (aeval z (denominator m))⁻¹ = ∑ ζ ∈ S, _
  rw [← eval_complexDenominator]
  change (Q.eval z)⁻¹ = _
  have hinv : (N.eval z)⁻¹ = ∑ ζ ∈ S, Lagrange.nodalWeight S id ζ * (z - ζ)⁻¹ := by
    calc
      _ = (N.eval z)⁻¹ * 1 := (mul_one _).symm
      _ = _ := by rw [hsum, ← mul_assoc, inv_mul_cancel₀ hNz, one_mul]
  rw [hqz, mul_inv, hinv, Finset.mul_sum]
  exact Finset.sum_congr rfl hweight

/-- The rational Taylor coefficient is the sum of the simple-pole contributions. -/
theorem reciprocalCoefficient_eq_sum (m n : ℕ) (hm : 0 < m) :
    (reciprocalCoefficient m n : ℂ) =
      ∑ ζ ∈ ((denominator m).aroots ℂ).toFinset, residueWeight m ζ * (ζ⁻¹) ^ n := by
  classical
  let S := ((denominator m).aroots ℂ).toFinset
  have hf : HasFPowerSeriesAt (fun z : ℂ ↦ (aeval z (denominator m))⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k ↦ ∑ ζ ∈ S, residueWeight m ζ * (ζ⁻¹) ^ k)) 0 := by
    rw [hasFPowerSeriesAt_iff]
    have hn : ∀ᶠ z : ℂ in 𝓝 0, ∀ ζ ∈ S, ‖z / ζ‖ < 1 := by
      refine S.eventually_all.mpr fun ζ _ ↦ ?_
      exact (continuousAt_id.div_const ζ).norm.eventually_lt continuousAt_const (by simp)
    have hnz : ∀ᶠ z : ℂ in 𝓝 0, aeval z (denominator m) ≠ 0 :=
      ((denominator m).hasDerivAt_aeval (0 : ℂ)).continuousAt.eventually_ne
        (by simp [eval_denominator_zero])
    filter_upwards [hn, hnz] with z hz hnz
    rw [zero_add, reciprocal_eq_sum m hm hnz]
    simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, Finset.mul_sum]
    refine HasSum.congr_fun (hasSum_sum (s := S) (fun ζ hζ ↦
      (hasSum_geometric_of_norm_lt_one (hz ζ hζ)).mul_left (residueWeight m ζ))) fun k ↦ ?_
    refine Finset.sum_congr rfl fun ζ _ ↦ ?_
    rw [div_eq_mul_inv, mul_pow]
    ring
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun a : FormalMultilinearSeries ℂ ℂ ℂ ↦ a.coeff n)
      ((hasFPowerSeriesAt_reciprocal m).eq_formalMultilinearSeries hf)

private noncomputable def reflectedCoeff (m j : ℕ) : ℚ :=
  (m.choose j : ℚ) * ((2 * m - j)! : ℚ) / ((2 * m)! : ℚ)

private theorem eval_denominator_neg (m : ℕ) (z : ℂ) :
    aeval (-z) (denominator m) =
      ∑ j ∈ Finset.range (m + 1), (reflectedCoeff m j : ℂ) * z ^ j := by
  rw [denominator, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [aeval_monomial]
  change ((↑(((-1 : ℚ) ^ j * (m.choose j : ℚ) * ((2 * m - j)! : ℚ)) / ((2 * m)! : ℚ)) : ℂ)) *
    (-z) ^ j = (reflectedCoeff m j : ℂ) * z ^ j
  rw [show (-1 : ℚ) ^ j * (m.choose j : ℚ) * ((2 * m - j)! : ℚ) / ((2 * m)! : ℚ) =
    (-1 : ℚ) ^ j * reflectedCoeff m j by unfold reflectedCoeff; ring]
  push_cast
  rw [mul_right_comm, ← mul_pow]
  simp [mul_comm]

private noncomputable def reflectedValue (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (reflectedCoeff m j : ℝ) * r ^ j

private theorem eval_denominator_neg_ofReal (m : ℕ) (r : ℝ) :
    aeval (-(r : ℂ)) (denominator m) = (reflectedValue m r : ℂ) := by
  rw [eval_denominator_neg, reflectedValue]
  push_cast
  rfl

private theorem reflectedCoeff_nonneg (m j : ℕ) : (0 : ℝ) ≤ (reflectedCoeff m j : ℝ) := by
  unfold reflectedCoeff
  positivity

private theorem reflectedValue_pos (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 < reflectedValue m r := by
  have h0 : 0 ∈ Finset.range (m + 1) := by simp
  have h := Finset.single_le_sum
    (f := fun j ↦ (reflectedCoeff m j : ℝ) * r ^ j)
    (fun j _ ↦ mul_nonneg (reflectedCoeff_nonneg m j) (pow_nonneg hr _)) h0
  have hc : reflectedCoeff m 0 = 1 := by simp [reflectedCoeff, Nat.factorial_ne_zero]
  rw [hc] at h
  simp only [Rat.cast_one, pow_zero, mul_one] at h
  exact zero_lt_one.trans_le h

/-- At a positive real odd-order pole the weight is a positive real number. -/
theorem residueWeight_pos (m : ℕ) (hm : Odd m) {r : ℝ} (hr : 0 < r)
    (hroot : aeval (r : ℂ) (denominator m) = 0) :
    ∃ a : ℝ, 0 < a ∧ residueWeight m (r : ℂ) = (a : ℂ) := by
  refine ⟨reflectedValue m r / ((normalization m : ℝ) ^ 2 * r ^ (2 * m + 1)), ?_, ?_⟩
  · apply div_pos (reflectedValue_pos m hr.le)
    unfold normalization
    positivity
  · rw [residueWeight_eq m hm hroot, eval_denominator_neg_ofReal]
    push_cast
    rfl

private theorem norm_reflected_le (m : ℕ) {r : ℝ} (hr : 0 < r) {ζ : ℂ} (hle : r ≤ ‖ζ‖) :
    ‖aeval (-ζ) (denominator m)‖ ≤ reflectedValue m r * (‖ζ‖ / r) ^ m := by
  rw [eval_denominator_neg, reflectedValue, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
  have hjm : j ≤ m := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
  have hc := reflectedCoeff_nonneg m j
  have hpow := pow_le_pow_right₀ ((one_le_div hr).mpr hle) hjm
  rw [norm_mul, norm_pow]
  have hcast : ‖(reflectedCoeff m j : ℂ)‖ = (reflectedCoeff m j : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_of_nonneg hc]
  rw [hcast, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    ‖ζ‖ ^ j = r ^ j * (‖ζ‖ / r) ^ j := by rw [← mul_pow, mul_div_cancel₀ _ hr.ne']
    _ ≤ r ^ j * (‖ζ‖ / r) ^ m := mul_le_mul_of_nonneg_left hpow (pow_nonneg hr.le _)

/-- A root of modulus at least that of a positive real pole satisfies the normalized weight bound. -/
theorem norm_normalized_residueWeight_le (m n : ℕ) (hm : Odd m) {r : ℝ} {ζ : ℂ}
    (hr : 0 < r) (hrroot : aeval (r : ℂ) (denominator m) = 0)
    (hζ : aeval ζ (denominator m) = 0) (hle : r ≤ ‖ζ‖) :
    ‖(residueWeight m ζ / residueWeight m (r : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
      (r / ‖ζ‖) ^ (n + m + 1) := by
  have hrnorm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hζnorm := hr.trans_le hle
  have hA : 0 < ‖(normalization m : ℂ)‖ := norm_pos_iff.mpr (normalization_ne_zero m)
  have hp := reflectedValue_pos m hr.le
  have hrweight : ‖residueWeight m (r : ℂ)‖ =
      reflectedValue m r / (‖(normalization m : ℂ)‖ ^ 2 * r ^ (2 * m + 1)) := by
    rw [residueWeight_eq m hm hrroot, eval_denominator_neg_ofReal, norm_div,
      norm_mul, norm_pow, norm_pow, hrnorm, Complex.norm_real, Real.norm_of_nonneg hp.le]
  rw [norm_mul, norm_div, norm_pow, norm_div, hrnorm, residueWeight_eq m hm hζ,
    norm_div, norm_mul, norm_pow, norm_pow, hrweight]
  calc
    _ ≤ (reflectedValue m r * (‖ζ‖ / r) ^ m /
          (‖(normalization m : ℂ)‖ ^ 2 * ‖ζ‖ ^ (2 * m + 1))) /
          (reflectedValue m r / (‖(normalization m : ℂ)‖ ^ 2 * r ^ (2 * m + 1))) *
          (r / ‖ζ‖) ^ n := by
      gcongr
      exact norm_reflected_le m hr hle
    _ = _ := by
      simp only [two_mul, pow_add, div_pow, pow_one]
      field_simp [hA.ne', hp.ne', hr.ne', hζnorm.ne']

end D5.S3.Analytic.Polynomial.DiagonalPadeExponential
