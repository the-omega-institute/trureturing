/- GID: D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Actual calibrated prime prefix through its second inverse-log coefficient. -/
/- SOURCE_ONLY_UNCOMPILED. Original prefixQ, phi and image sInf are imported.
Prime-height limits come from the repaired CalibrationPrimeBridges identity.
Both finite endpoints, the additive one in C, and activation ties remain. -/
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
open Real Filter MeasureTheory Asymptotics
open scoped Topology
open OwnClockFixedSupport BoundaryPrimePrice QuantitativePrimeAbel
open RealInfimumPrimeBoundary
open QuantitativePrimeAbel

private def tailPolynomial (x : ℝ) : ℝ :=
  1 / (x * log x) - 1 / (x * log x ^ 2) + 2 / (x * log x ^ 3)

private lemma C_identity (P : ℕ) : prefixC P = 1 + prefixH P * prefixEll P := by
  simp only [prefixC, prefixPrice, cutoff,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.g, one_div, inv_inv, prefixEll]

private lemma H_top : Tendsto prefixH atTop atTop :=
  prefixH_atTop
private lemma l_top : Tendsto (fun P => log (prefixY P)) atTop atTop :=
  tendsto_log_atTop.comp prefix_Y_atTop

private lemma log_power_small (k : ℕ) :
    Tendsto (fun x : ℝ => log x ^ k / x) atTop (𝓝 0) := by
  simpa only [rpow_natCast, rpow_one] using
    (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero

private lemma pi_normalized :
    Tendsto (fun x : ℝ => log x * primeCount x / x) atTop (𝓝 1) := by
  have hi := tendsto_log_atTop.const_div_atTop 1
  have hc1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (((hc1.add hi).add ((hi.pow 2).const_mul 2)).add
    ((hi.pow 3).const_mul 6)).add (prime_counting_four_terms.mul (hi.pow 4))
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [countingPolynomial]
  field_simp [show x ≠ 0 by linarith, (log_pos hx).ne']
  <;> ring

private lemma log_square_over_square_sub_one :
    Tendsto (fun x : ℝ => log x ^ 2 / (x ^ 2 - 1)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_id.const_div_atTop (1 : ℝ)).pow 2
  have h := ((log_power_small 2).mul
    (tendsto_id.const_div_atTop (1 : ℝ))).div
    (tendsto_const_nhds.sub hinv) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  field_simp [show x ≠ 0 by linarith, show x ^ 2 - 1 ≠ 0 by nlinarith]
  <;> ring

/-- The exact Q decomposition uses the genuine max boundary, includes
ties in pi(r), and keeps the strict tail (r,P]. No theta(P)<=P is used. -/
theorem eventual_Q_exact :
    ∀ᶠ P : ℕ in atTop,
      prefixQ P =
        2 * (primeCount (prefixY P) * log (prefixY P) - Chebyshev.theta (prefixY P)) /
          (prefixY P ^ 2 - 1) +
        primeCount (prefixY P) * (-log (1 - 1 / prefixY P ^ 2)) +
        logarithmicTail (prefixY P) (P : ℝ) := by
  filter_upwards [eventual_prefix_domains, eventual_scale_positivity] with P hdom hpos
  rcases hpos with ⟨hH, he, hC, hr, hl, _, hP, _⟩
  have hsq : prefixY P ^ 2 = prefixC P := sq_sqrt hC.le
  have hform := prime_prefix_boundary_formulas P hdom.2.2.2.1
  dsimp only at hform
  rw [min_eq_right hdom.2.2.2.2.2.le] at hform
  have hlog : log (prefixC P) = 2 * log (prefixY P) := by
    dsimp only [prefixY]
    rw [log_sqrt hC.le]
    ring
  have hclock : clock (Nat.primesLE P) (prefixBoundary P) - prefixH P =
      2 * (primeCount (prefixY P) * log (prefixY P) - Chebyshev.theta (prefixY P)) := by
    rw [hlog] at hform
    convert hform.1 using 1 <;> dsimp only [primeCount] <;> ring
  have hdef : deficiency (Nat.primesLE P) (prefixBoundary P) =
      primeCount (prefixY P) * (-log (1 - 1 / prefixY P ^ 2)) +
      logarithmicTail (prefixY P) (P : ℝ) := by
    simpa only [primeCount, logarithmicTail, primeInterval, Nat.floor_natCast, hsq] using hform.2
  have hden : prefixH P * prefixEll P = prefixY P ^ 2 - 1 := by
    rw [hsq, C_identity]
    ring
  have hQ := fixed_price_Q_identity hdom.1 hdom.2.1
  change prefixQ P = deficiency (Nat.primesLE P) (prefixBoundary P) +
    (clock (Nat.primesLE P) (prefixBoundary P) - prefixH P) /
      (prefixH P * prefixEll P) at hQ
  rw [hQ, hclock, hdef, hden]
  ring

private lemma head_euler_error :
    Tendsto (fun x : ℝ => x * log x ^ 3 *
      (primeCount x * (-log (1 - 1 / x ^ 2)) - primeCount x / x ^ 2))
      atTop (𝓝 0) := by
  have hu := pi_normalized.mul log_square_over_square_sub_one
  norm_num only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hq : 1 / x ^ 2 < 1 := (div_lt_one (pow_pos hx0 2)).mpr (by nlinarith)
    have hb := (log_deficit_bounds (by positivity : 0 ≤ 1 / x ^ 2) hq).1
    have hp : 0 ≤ primeCount x := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hb hp
    exact mul_nonneg (by positivity [log_pos hx]) (by nlinarith only [hm])
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hq : 1 / x ^ 2 < 1 := (div_lt_one (pow_pos hx0 2)).mpr (by nlinarith)
    have hb := (log_deficit_bounds (by positivity : 0 ≤ 1 / x ^ 2) hq).2
    have hp : 0 ≤ primeCount x := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hb hp
    have hid : (primeCount x * ((1 / x ^ 2) / (1 - 1 / x ^ 2)) -
        primeCount x / x ^ 2) * (x * log x ^ 3) =
        (log x * primeCount x / x) * (log x ^ 2 / (x ^ 2 - 1)) := by
      field_simp [hx0.ne', show x ^ 2 - 1 ≠ 0 by nlinarith,
        show 1 - 1 / x ^ 2 ≠ 0 by linarith]
      <;> ring
    rw [← hid]
    have hm' := sub_le_sub_right hm (primeCount x / x ^ 2)
    have hh := mul_le_mul_of_nonneg_right hm'
      (show 0 ≤ x * log x ^ 3 by positivity [log_pos hx])
    simpa only [mul_comm] using hh

private lemma finite_endpoint_separation :
    Tendsto (fun P : ℕ => prefixY P * log (prefixY P) ^ 3 / (P : ℝ))
      atTop (𝓝 0) := by
  have h := (((prefix_C_div_H_ell.mul (prefix_log_Y_div_ell.pow 6)).mul
    ((log_power_small 7).comp H_top)).mul (prefix_H_ratio.pow 2)).sqrt
  norm_num only [mul_zero, zero_mul, sqrt_zero] at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, he, hC, hr, hl, _, hp, _⟩
  have hs : prefixY P ^ 2 = prefixC P := sq_sqrt hC.le
  have hid : prefixC P / (prefixH P * prefixEll P) *
      (log (prefixY P) / prefixEll P) ^ 6 * (log (prefixH P) ^ 7 / prefixH P) *
      (prefixH P / (P : ℝ)) ^ 2 =
      (prefixY P * log (prefixY P) ^ 3 / (P : ℝ)) ^ 2 := by
    dsimp only [prefixEll] at *
    rw [← hs]
    field_simp [hH.ne', he.ne', hp.ne']
    <;> ring
  rw [hid, sqrt_sq (by positivity : 0 ≤ prefixY P * log (prefixY P) ^ 3 / (P : ℝ))]

private lemma finite_endpoint_zero :
    Tendsto (fun P : ℕ => prefixY P * log (prefixY P) ^ 3 * tailPolynomial (P : ℝ))
      atTop (𝓝 0) := by
  have hinv := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hpoly := ((hinv.sub (hinv.pow 2)).add ((hinv.pow 3).const_mul 2))
  have h := finite_endpoint_separation.mul hpoly
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with P hP
  have hp : (1 : ℝ) < P := by exact_mod_cast hP
  dsimp only [tailPolynomial]
  field_simp [show (P : ℝ) ≠ 0 by linarith, (log_pos hp).ne']
  <;> ring

private lemma square_tail_error_zero :
    Tendsto (fun P : ℕ => prefixY P * log (prefixY P) ^ 3 *
      (squareSum (prefixY P) (P : ℝ) - tailPolynomial (prefixY P)))
      atTop (𝓝 0) := by
  obtain ⟨X, hX, hbound⟩ :=
    D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail.prime_square_tail_logarithmic_refinements
  have hbound' : ∀ y z : ℝ, X ≤ y → y ≤ z →
      |squareSum y z - (tailPolynomial y - tailPolynomial z)| ≤
        130 / (y * log y ^ 4) := by
    intro y z hY hyz
    have hy : 1 < y := by
      have : Real.exp 1 < y := hX.trans_le hY
      exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans this
    have hy0 : 0 < y := by linarith
    have hly : 1 ≤ log y :=
      (le_log_iff_exp_le hy0).mpr (hX.le.trans hY)
    have hpow : log y ^ 4 ≤ log y ^ 9 := by
      calc
        log y ^ 4 = log y ^ 4 * 1 := by ring
        _ ≤ log y ^ 4 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 4)
        _ = log y ^ 5 := by ring
        _ ≤ log y ^ 5 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 5)
        _ = log y ^ 6 := by ring
        _ ≤ log y ^ 6 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 6)
        _ = log y ^ 7 := by ring
        _ ≤ log y ^ 7 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 7)
        _ = log y ^ 8 := by ring
        _ ≤ log y ^ 8 * log y :=
          mul_le_mul_of_nonneg_left hly (pow_nonneg (log_pos hy).le 8)
        _ = log y ^ 9 := by ring
    have hden4 : 0 < y * log y ^ 4 := mul_pos hy0 (pow_pos (log_pos hy) 4)
    have hdenle : y * log y ^ 4 ≤ y * log y ^ 9 :=
      mul_le_mul_of_nonneg_left hpow hy0.le
    have hfrac : 5 / (y * log y ^ 9) ≤ 5 / (y * log y ^ 4) := by
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hden4 hdenle)
          (by norm_num : (0 : ℝ) ≤ 5))
    have hs := (hbound y z hY hyz).2
    dsimp only [squareSum, primeInterval, tailPolynomial]
    dsimp only [tailPolynomial] at hs
    calc
      |(∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) -
          ((1 / (y * log y) - 1 / (y * log y ^ 2) + 2 / (y * log y ^ 3)) -
            (1 / (z * log z) - 1 / (z * log z ^ 2) + 2 / (z * log z ^ 3)))| =
          |(∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) -
            (1 / (y * log y) - 1 / (y * log y ^ 2) + 2 / (y * log y ^ 3)) +
            (1 / (z * log z) - 1 / (z * log z ^ 2) + 2 / (z * log z ^ 3))| := by
              congr 1 <;> ring
      _ ≤ 6 / (y * log y ^ 4) + 5 / (y * log y ^ 9) := hs
      _ ≤ 6 / (y * log y ^ 4) + 5 / (y * log y ^ 4) :=
        add_le_add_left hfrac _
      _ = 11 / (y * log y ^ 4) := by ring
      _ ≤ 130 / (y * log y ^ 4) := by
        exact (div_le_div_iff₀ hden4 hden4).mpr (by nlinarith [hden4])
  have hu := l_top.const_div_atTop 130
  have hz : Tendsto (fun P : ℕ => prefixY P * log (prefixY P) ^ 3 *
      (squareSum (prefixY P) (P : ℝ) -
        (tailPolynomial (prefixY P) - tailPolynomial (P : ℝ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [prefix_Y_atTop.eventually_ge_atTop X, eventual_prefix_domains] with P hPX hdom
    have hy : 1 < prefixY P :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans
        (hX.trans_le hPX)
    have hb := hbound' (prefixY P) (P : ℝ) hPX hdom.2.2.2.2.2.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity [log_pos hy])]
    calc
      _ ≤ (prefixY P * log (prefixY P) ^ 3) *
          (130 / (prefixY P * log (prefixY P) ^ 4)) :=
        mul_le_mul_of_nonneg_left hb (by positivity [log_pos hy])
      _ = _ := by field_simp [show prefixY P ≠ 0 by linarith, (log_pos hy).ne']; ring
  have h := hz.sub finite_endpoint_zero
  norm_num only [sub_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun P => by ring)

private lemma tail_euler_error :
    Tendsto (fun P : ℕ => prefixY P * log (prefixY P) ^ 3 *
      (logarithmicTail (prefixY P) (P : ℝ) - squareSum (prefixY P) (P : ℝ)))
      atTop (𝓝 0) := by
  have htail : Tendsto (fun P : ℕ => prefixY P * log (prefixY P) *
      squareSum (prefixY P) (P : ℝ)) atTop (𝓝 1) := by
    have hi := l_top.const_div_atTop 1
    have h := (square_tail_error_zero.mul (hi.pow 2)).add
      ((tendsto_const_nhds.sub hi).add ((hi.pow 2).const_mul 2))
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hp
    dsimp only [tailPolynomial]
    field_simp [hp.2.2.2.1.ne', hp.2.2.2.2.1.ne']
    <;> ring
  have hu := htail.mul (log_square_over_square_sub_one.comp prefix_Y_atTop)
  norm_num only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventual_prefix_domains] with P hP
    have hy : 1 < prefixY P := by linarith [hP.2.2.2.2.1]
    exact mul_nonneg (by positivity [log_pos hy])
      (sub_nonneg.mpr (finite_logarithmic_tail_squeeze hy).1)
  · filter_upwards [eventual_prefix_domains] with P hP
    have hy : 1 < prefixY P := by linarith [hP.2.2.2.2.1]
    have hy0 : 0 < prefixY P := by linarith
    have hb := (finite_logarithmic_tail_squeeze (z := (P : ℝ)) hy).2
    have hid : prefixY P * log (prefixY P) ^ 3 *
        (squareSum (prefixY P) (P : ℝ) / (1 - 1 / prefixY P ^ 2) -
          squareSum (prefixY P) (P : ℝ)) =
        (prefixY P * log (prefixY P) * squareSum (prefixY P) (P : ℝ)) *
          (log (prefixY P) ^ 2 / (prefixY P ^ 2 - 1)) := by
      field_simp [hy0.ne', show prefixY P ^ 2 - 1 ≠ 0 by nlinarith,
        show 1 - 1 / prefixY P ^ 2 ≠ 0 by
          have hh : 1 / prefixY P ^ 2 < 1 :=
            (div_lt_one (pow_pos hy0 2)).mpr (by nlinarith)
          linarith]
      <;> ring
    rw [← hid]
    exact mul_le_mul_of_nonneg_left (by linarith only [hb]) (by positivity [log_pos hy])

/-- Three relative coefficients for the ORIGINAL finite calibrated Q:
Q = 4/(r*l)*(1+1/l+4/l^2+o(l^-2)). The tail estimate above actually
has O(l^-3) relative remainder; this theorem retains the exact 16. -/
theorem calibrated_Q_second_order :
    Tendsto (fun P : ℕ => log (prefixY P) ^ 2 *
      (prefixY P * log (prefixY P) * prefixQ P - 4 - 4 / log (prefixY P)))
      atTop (𝓝 16) := by
  let r := prefixY
  let l : ℕ → ℝ := fun P => log (r P)
  let e : ℕ → ℝ := fun P =>
    (primeCount (r P) - countingPolynomial (r P)) / (r P / l P ^ 5)
  let v : ℕ → ℝ := fun P =>
    (Chebyshev.theta (r P) - r P) / (r P / l P ^ 3)
  let u : ℕ → ℝ := fun P => r P ^ 2 / (r P ^ 2 - 1)
  have he : Tendsto e atTop (𝓝 24) := prime_counting_four_terms.comp prefix_Y_atTop
  have hv : Tendsto v atTop (𝓝 0) :=
    (theta_error_log_power 3).tendsto_div_nhds_zero.comp prefix_Y_atTop
  have hinv : Tendsto (fun P => 1 / l P) atTop (𝓝 0) := l_top.const_div_atTop 1
  have hq : Tendsto (fun P => 1 / r P ^ 2) atTop (𝓝 0) := by
    simpa using (prefix_Y_atTop.const_div_atTop (1 : ℝ)).pow 2
  have hu : Tendsto u atTop (𝓝 1) := by
    have h := (tendsto_const_nhds.sub hq).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_prefix_domains] with P hP
    have hr : 1 < r P := by dsimp only [r]; linarith [hP.2.2.2.2.1]
    dsimp only [u]
    field_simp [show r P ≠ 0 by linarith, show r P ^ 2 - 1 ≠ 0 by nlinarith]
    <;> ring
  have huf : Tendsto (fun P => l P ^ 2 * (u P - 1)) atTop (𝓝 0) := by
    apply (log_square_over_square_sub_one.comp prefix_Y_atTop).congr'
    filter_upwards [eventual_prefix_domains] with P hP
    have hr : 1 < r P := by dsimp only [r]; linarith [hP.2.2.2.2.1]
    dsimp only [u, l]
    field_simp [show r P ^ 2 - 1 ≠ 0 by nlinarith]
    <;> ring
  have hhead := head_euler_error.comp prefix_Y_atTop
  have htail := tail_euler_error.add square_tail_error_zero
  norm_num only [add_zero] at htail
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have h := (((((((huf.const_mul 2).add ((huf.mul hinv).const_mul 4)).add
    (hu.const_mul 12)).add (((hu.mul he).mul hinv).const_mul 2)).sub
    ((hu.mul hv).const_mul 2)).add
      ((hc2.add (hinv.const_mul 6)).add (he.mul (hinv.pow 2)))).add
        hc2).add (hhead.add htail)
  norm_num at h
  apply h.congr'
  filter_upwards [eventual_Q_exact, eventual_prefix_domains] with P hQ hP
  have hr : 1 < r P := by dsimp only [r]; linarith [hP.2.2.2.2.1]
  have hr0 : r P ≠ 0 := ne_of_gt (by linarith)
  have hl : l P ≠ 0 := (log_pos hr).ne'
  rw [hQ]
  dsimp only [r, l, e, v, u, countingPolynomial, tailPolynomial] at *
  field_simp [hr0, hl, show prefixY P ^ 2 - 1 ≠ 0 by
    change r P ^ 2 - 1 ≠ 0; nlinarith]
  <;> ring

end D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
