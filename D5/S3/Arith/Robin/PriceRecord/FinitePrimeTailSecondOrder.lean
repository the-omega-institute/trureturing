/- GID: D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Finite Abel tail with three logarithmic coefficients and both endpoints. -/
/-! Native finite real-endpoint prime-square tail estimate. No infinite tail is used; both finite endpoints remain explicit. -/
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FinitePrimeTailSecondOrder
open Real Set Filter MeasureTheory Asymptotics
open scoped Topology
open PrimeBoundaryAbel QuantitativePrimeAbel

private lemma count_weight_integrable {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc y z)) :
    IntervalIntegrable (fun t => f t * primeCount t) volume y z := by
  classical
  have hindicator (t : ℝ) :
      (∑ p ∈ Icc 0 ⌊t⌋₊, if p.Prime then (1 : ℝ) else 0) = primeCount t := by
    rw [← sum_filter, ← Nat.primesLE_eq_filter_Icc_zero]
    simp only [sum_const, nsmul_eq_mul, mul_one, primeCount,
      Nat.primesLE_card_eq_primeCounting]
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr
  have hi := integrableOn_mul_sum_Icc
    (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) hy hf.integrableOn_Icc (m := 0)
  simpa only [hindicator] using hi


def tailPolynomial (x : ℝ) : ℝ :=
  1 / (x * log x) - 1 / (x * log x ^ 2) + 2 / (x * log x ^ 3)

private def K (k : ℕ) (x : ℝ) : ℝ := 1 / (x ^ 2 * log x ^ k)
private def E (k : ℕ) (x : ℝ) : ℝ := 1 / (x * log x ^ k)

private lemma K_continuous {y z : ℝ} (hy : 1 < y) (k : ℕ) :
    ContinuousOn (K k) (Icc y z) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hlt : log t ≠ 0 := (log_pos (hy.trans_le ht.1)).ne'
  exact ContinuousAt.continuousWithinAt (by dsimp only [K]; fun_prop)

private lemma E_deriv {x : ℝ} (hx : 1 < x) (k : ℕ) :
    HasDerivAt (E k) (-K k x - (k : ℝ) * K (k + 1) x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have h := (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_id x).mul ((hasDerivAt_log hx0).pow k))
    (mul_ne_zero hx0 (pow_ne_zero k hl))
  convert h using 1 <;> dsimp only [E, K]
  cases k with
  | zero => simp; field_simp [hx0, hl]; ring
  | succ k => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]
              field_simp [hx0, hl]; ring

private lemma E_mono {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) (k : ℕ) :
    E k z ≤ E k y := by
  apply one_div_le_one_div_of_le
    (mul_pos (by linarith : 0 < y) (pow_pos (log_pos hy) k))
  exact mul_le_mul hyz
    (pow_le_pow_left₀ (log_pos hy).le (log_le_log (by linarith) hyz) k)
    (pow_nonneg (log_pos hy).le k) (by linarith)

private lemma kernel_integral_bounds {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (k : ℕ) :
    0 ≤ (∫ t in y..z, K k t) ∧ (∫ t in y..z, K k t) ≤ E k y := by
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz (K_continuous hy k)
  have hj := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz (K_continuous hy (k + 1))
  have hI : 0 ≤ (∫ t in y..z, K k t) :=
    intervalIntegral.integral_nonneg hyz (fun t ht => by
      dsimp only [K]; positivity [(log_pos (hy.trans_le ht.1)).le])
  have hJ : 0 ≤ (∫ t in y..z, K (k + 1) t) :=
    intervalIntegral.integral_nonneg hyz (fun t ht => by
      dsimp only [K]; positivity [(log_pos (hy.trans_le ht.1)).le])
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => E_deriv (by rw [uIcc_of_le hyz] at ht; exact hy.trans_le ht.1) k)
    (hi.neg.sub (hj.const_mul (k : ℝ)))
  rw [intervalIntegral.integral_sub hi.neg (hj.const_mul (k : ℝ)),
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hFTC
  have hEz : 0 ≤ E k z := by
    dsimp only [E]; positivity [log_pos (hy.trans_le hyz)]
  exact ⟨hI, by nlinarith [Nat.cast_nonneg (α := ℝ) k]⟩

private lemma model_tail_identity {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    countingPolynomial z / z ^ 2 - countingPolynomial y / y ^ 2 +
        2 * (∫ t in y..z, countingPolynomial t / t ^ 3) =
      tailPolynomial y - tailPolynomial z -
        6 * (∫ t in y..z, K 4 t) - 24 * (∫ t in y..z, K 5 t) := by
  let W : ℝ → ℝ := fun t =>
    (2 / log t + 4 / log t ^ 3 + 6 / log t ^ 4) / t
  have hder (t : ℝ) (ht : t ∈ Icc y z) :
      HasDerivAt W
        (-2 * (countingPolynomial t / t ^ 3) - 6 * K 4 t - 24 * K 5 t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hl : log t ≠ 0 := (log_pos (hy.trans_le ht.1)).ne'
    have hd (k : ℕ) (c : ℝ) : HasDerivAt (fun u : ℝ => c / log u ^ k)
        (-(c * (k : ℝ) * log t ^ (k - 1) * t⁻¹) / (log t ^ k) ^ 2) t := by
      convert (hasDerivAt_const t c).div ((hasDerivAt_log ht0).pow k)
        (pow_ne_zero k hl) using 1 <;> ring
    have h := (((hd 1 2).add (hd 3 4)).add (hd 4 6)).div
      (hasDerivAt_id t) ht0
    convert h using 1 <;> dsimp only [W, K, countingPolynomial] <;> norm_num <;>
      field_simp [ht0, hl] <;> ring
  have hc : ContinuousOn (fun t : ℝ => countingPolynomial t / t ^ 3) (Icc y z) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hl : log t ≠ 0 := (log_pos (hy.trans_le ht.1)).ne'
    exact ContinuousAt.continuousWithinAt (by dsimp only [countingPolynomial]; fun_prop)
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz hc
  have h4 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz (K_continuous hy 4)
  have h5 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz (K_continuous hy 5)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hder t (by simpa only [uIcc_of_le hyz] using ht))
    (((hi.const_mul (-2)).sub (h4.const_mul 6)).sub (h5.const_mul 24))
  rw [intervalIntegral.integral_sub ((hi.const_mul (-2)).sub (h4.const_mul 6))
      (h5.const_mul 24),
    intervalIntegral.integral_sub (hi.const_mul (-2)) (h4.const_mul 6),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  have hW (t : ℝ) (ht : 1 < t) :
      W t = countingPolynomial t / t ^ 2 + tailPolynomial t := by
    dsimp only [W, countingPolynomial, tailPolynomial]
    field_simp [show t ≠ 0 by linarith, (log_pos ht).ne']
    <;> ring
  rw [hW y hy, hW z (hy.trans_le hyz)] at hFTC
  linarith only [hFTC]

/-- There is ONE unconditional threshold for every finite interval (y,z].
The upper endpoint polynomial is retained; tied primes at y are excluded
by the exact Mathlib Ioc Abel formula in finite_prime_square_abel. -/
theorem finite_square_three_terms :
    ∃ X : ℝ, 1 < X ∧ ∀ y z : ℝ, X ≤ y → y ≤ z →
      |squareSum y z - (tailPolynomial y - tailPolynomial z)| ≤
        130 / (y * log y ^ 4) := by
  obtain ⟨X, hX, hpnt⟩ := prime_counting_four_terms_uniform
  refine ⟨max X (exp 1), lt_of_lt_of_le hX (le_max_left _ _), ?_⟩
  intro y z hY hyz
  have hy : 1 < y := hX.trans_le ((le_max_left _ _).trans hY)
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := hy0.trans_le hyz
  have hly : 1 ≤ log y :=
    (le_log_iff_exp_le hy0).mpr ((le_max_right _ _).trans hY)
  have hlt (t : ℝ) (ht : t ∈ Icc y z) : 0 < log t := log_pos (hy.trans_le ht.1)
  have hcp (t : ℝ) (ht : t ∈ Icc y z) :
      |primeCount t - countingPolynomial t| ≤ 25 * t / log t ^ 5 :=
    hpnt t (((le_max_left _ _).trans hY).trans ht.1)
  have hc : ContinuousOn (fun t : ℝ => countingPolynomial t / t ^ 3) (Icc y z) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hy0.trans_le ht.1)
    have hl : log t ≠ 0 := (hlt t ht).ne'
    exact ContinuousAt.continuousWithinAt (by dsimp only [countingPolynomial]; fun_prop)
  have hcount := count_weight_integrable hy0.le hyz
    (f := fun t => 1 / t ^ 3)
    (continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne'))
  have hi : IntervalIntegrable (fun t => primeCount t / t ^ 3) volume y z := by
    simpa only [one_div_mul_eq_div] using hcount
  have hj := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz hc
  have hk := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz (K_continuous hy 5)
  have hpoint (t : ℝ) (ht : t ∈ Icc y z) :
      |(primeCount t - countingPolynomial t) / t ^ 3| ≤ 25 * K 5 t := by
    have ht0 := hy0.trans_le ht.1
    rw [abs_div, abs_of_pos (pow_pos ht0 3)]
    calc
      _ ≤ (25 * t / log t ^ 5) / t ^ 3 :=
        div_le_div_of_nonneg_right (hcp t ht) (pow_nonneg ht0.le 3)
      _ = _ := by dsimp only [K]; field_simp [ht0.ne', (hlt t ht).ne']; ring
  have hIe : |(∫ t in y..z, primeCount t / t ^ 3) -
      (∫ t in y..z, countingPolynomial t / t ^ 3)| ≤ 25 * E 5 y := by
    rw [← intervalIntegral.integral_sub hi hj]
    have hh := (intervalIntegral.abs_integral_le_integral_abs hyz
      (f := fun t => primeCount t / t ^ 3 - countingPolynomial t / t ^ 3)).trans
      (intervalIntegral.integral_mono_on hyz (hi.sub hj).abs (hk.const_mul 25)
        (fun t ht => by simpa only [← sub_div] using hpoint t ht))
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (kernel_integral_bounds hy hyz 5).2
      (by norm_num))
  have endpoint_error (t : ℝ) (ht : t ∈ Icc y z) :
      |primeCount t / t ^ 2 - countingPolynomial t / t ^ 2| ≤ 25 * E 5 y := by
    have ht0 := hy0.trans_le ht.1
    rw [← sub_div, abs_div, abs_of_pos (pow_pos ht0 2)]
    calc
      _ ≤ (25 * t / log t ^ 5) / t ^ 2 :=
        div_le_div_of_nonneg_right (hcp t ht) (sq_nonneg t)
      _ = 25 * E 5 t := by dsimp only [E]; field_simp [ht0.ne', (hlt t ht).ne']; ring
      _ ≤ 25 * E 5 y := mul_le_mul_of_nonneg_left (E_mono hy ht.1 5) (by norm_num)
  have h4 := kernel_integral_bounds hy hyz 4
  have h5 := kernel_integral_bounds hy hyz 5
  have hI4 : 0 ≤ (∫ t in y..z, K 4 t) := h4.1
  have hI5 : 0 ≤ (∫ t in y..z, K 5 t) := h5.1
  have hE54 : E 5 y ≤ E 4 y := by
    have hpow : log y ^ 4 ≤ log y ^ 5 := by
      calc
        log y ^ 4 = log y ^ 4 * 1 := by ring
        _ ≤ log y ^ 4 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 4)
        _ = log y ^ 5 := by ring
    exact one_div_le_one_div_of_le
      (mul_pos hy0 (pow_pos (log_pos hy) 4))
      (mul_le_mul_of_nonneg_left hpow hy0.le)
  have habel := finite_prime_square_abel hy0 hyz
  have hmodel := model_tail_identity hy hyz
  have htri := abs_add_le
    ((primeCount z / z ^ 2 - countingPolynomial z / z ^ 2) -
      (primeCount y / y ^ 2 - countingPolynomial y / y ^ 2))
    (2 * ((∫ t in y..z, primeCount t / t ^ 3) -
      (∫ t in y..z, countingPolynomial t / t ^ 3)))
  have htri2 := abs_sub_le
    (primeCount z / z ^ 2 - countingPolynomial z / z ^ 2)
    (primeCount y / y ^ 2 - countingPolynomial y / y ^ 2)
  have hcorr : |6 * (∫ t in y..z, K 4 t) + 24 * (∫ t in y..z, K 5 t)| ≤
      6 * E 4 y + 24 * E 5 y := by
    rw [abs_of_nonneg (by positivity)]
    linarith only [h4.2, h5.2]
  have hfinal := abs_sub_le
    ((primeCount z / z ^ 2 - countingPolynomial z / z ^ 2) -
      (primeCount y / y ^ 2 - countingPolynomial y / y ^ 2) +
      2 * ((∫ t in y..z, primeCount t / t ^ 3) -
        (∫ t in y..z, countingPolynomial t / t ^ 3)))
    (6 * (∫ t in y..z, K 4 t) + 24 * (∫ t in y..z, K 5 t))
  have hid : squareSum y z - (tailPolynomial y - tailPolynomial z) =
      (primeCount z / z ^ 2 - countingPolynomial z / z ^ 2) -
      (primeCount y / y ^ 2 - countingPolynomial y / y ^ 2) +
      2 * ((∫ t in y..z, primeCount t / t ^ 3) -
        (∫ t in y..z, countingPolynomial t / t ^ 3)) -
      (6 * (∫ t in y..z, K 4 t) + 24 * (∫ t in y..z, K 5 t)) := by
    linarith only [habel, hmodel]
  rw [hid]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  have hh :
      |(primeCount z / z ^ 2 - countingPolynomial z / z ^ 2) -
        (primeCount y / y ^ 2 - countingPolynomial y / y ^ 2) +
        2 * ((∫ t in y..z, primeCount t / t ^ 3) -
          (∫ t in y..z, countingPolynomial t / t ^ 3)) -
        (6 * (∫ t in y..z, K 4 t) + 24 * (∫ t in y..z, K 5 t))| ≤ 130 * E 4 y := by
    linarith only [hfinal, htri, htri2, endpoint_error z ⟨hyz, le_rfl⟩,
      endpoint_error y ⟨le_rfl, hyz⟩, hIe, hcorr, hE54]
  simpa only [E, one_div, div_eq_mul_inv] using hh

end D5.S3.Arith.Robin.PriceRecord.FinitePrimeTailSecondOrder
