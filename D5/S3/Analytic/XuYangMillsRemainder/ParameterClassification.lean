/- GID: D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/ParameterClassification
   mirror-E: none
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Taylor]
   utility: none
   digest: Polynomial moments locate the sign thresholds of the native Mills remainder. -/

import D5.S3.Analytic.XuYangMillsRemainder.Result

/-! Native Mills coefficients and the polynomial moment thresholds. -/

open Set Real MeasureTheory Filter
open scoped Topology ContDiff Interval
noncomputable section
namespace D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification

open D5.S3.Analytic.XuYangMillsRemainder.Result

def B (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * (1 + v ^ 2) ^ j
def theta (j : ℕ) : ℝ := (1 - intPow j / B j) / 2

private lemma B_eq (j : ℕ) : B j = intPow (j + 1) - intPow j := by
  unfold B intPow
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [pow_succ]
  ring

private lemma moment_pos (j : ℕ) : 0 < B j ∧ B j < intPow j := by
  have hc : Continuous (fun v : ℝ => v ^ 2 * (1 + v ^ 2) ^ j) := by fun_prop
  have hi : Continuous (fun v : ℝ => (1 + v ^ 2) ^ j) := by fun_prop
  constructor
  · have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := (0 : ℝ)) (b := 1) (f := fun _ => 0) (g := fun v => v ^ 2 * (1 + v ^ 2) ^ j)
      (by norm_num) continuous_const.continuousOn hc.continuousOn
      (fun v _ => by positivity) ⟨1 / 2, by norm_num, by positivity⟩
    simpa [B] using h
  · exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num) hc.continuousOn hi.continuousOn
      (fun v hv => mul_le_of_le_one_left (by positivity) (by nlinarith [hv.1, hv.2]))
      ⟨0, by norm_num, by norm_num⟩

private lemma u_moment (j : ℕ) (a : ℝ) :
    u (j + 2) a (a - 2) =
      ((2 * j + 3).factorial : ℝ) / (4 ^ (j + 1) * j.factorial) *
        (intPow j + (2 * a - 1) * B j) := by
  have hs := coeff_sum (j + 1)
  have hf := coeff_factorial (j + 1)
  have hr := intPow_rec j
  have hu : u (j + 2) a (a - 2) =
      (a - 1) * coeff (j + 2) + (j + 2 - a) * (j + 1).factorial *
        (∑ k ∈ Finset.range (j + 2), coeff k / k.factorial) := by
    simp only [u, coeff, show j + 2 - 1 = j + 1 by omega]
    push_cast
    congr 1
    · ring
    · congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
  have he : (a - 1) * (2 : ℝ) ^ (j + 1) + (j + 2 - a) * intPow (j + 1) =
      (j + 1) * (intPow j + (2 * a - 1) * B j) := by
    rw [B_eq]
    linear_combination (1 - a) * hr
  have hcoef : coeff (j + 2) * (2 ^ (j + 1) * ((j + 1).factorial : ℝ)) =
      ((2 * j + 3).factorial : ℝ) := by
    convert hf using 1 <;> congr 1 <;> omega
  have h4 : (4 : ℝ) ^ (j + 1) = (2 ^ (j + 1)) ^ 2 := by
    calc
      (4 : ℝ) ^ (j + 1) = ((2 : ℝ) ^ 2) ^ (j + 1) := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; omega
  calc
    _ = coeff (j + 2) / 2 ^ (j + 1) *
        ((a - 1) * 2 ^ (j + 1) + (j + 2 - a) * intPow (j + 1)) := by
      rw [hu, hs]
      field_simp
    _ = coeff (j + 2) / 2 ^ (j + 1) *
        ((j + 1) * (intPow j + (2 * a - 1) * B j)) := by rw [he]
    _ = _ := by
      rw [← hcoef, h4, Nat.factorial_succ]
      push_cast
      field_simp
      <;> ring

@[fun_prop] private lemma mills_continuous : Continuous millsRatio := by
  have hi : Integrable (fun t : ℝ => exp (-t ^ 2 / 2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext t
    congr 1
    ring
  have he (x : ℝ) : (∫ t in Ioi x, exp (-t ^ 2 / 2)) =
      (∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2) := by
    linear_combination -intervalIntegral.integral_Ioi_sub_Ioi' (hi.integrableOn (s := Ioi 0))
      (hi.integrableOn (s := Ioi x))
  have hc : Continuous (fun x : ℝ => exp (x ^ 2 / 2) *
      ((∫ t in Ioi (0 : ℝ), exp (-t ^ 2 / 2)) - ∫ t in (0 : ℝ)..x, exp (-t ^ 2 / 2))) := by
    apply Continuous.mul (by fun_prop)
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous (by fun_prop)).continuous
  convert hc using 1
  funext x
  rw [millsRatio, he x]

private lemma native_zero_limit (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n) * ((-1 : ℝ) ^ n * D n x a))
      (𝓝[>] 0) (𝓝 (-u n a (a - 2))) := by
  let P : ℝ → ℝ := fun x => (-1 : ℝ) ^ n *
    (x ^ (2 * n) * (Y a (a - 2) x - (a - 1)) -
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * n - 2 * k))
  have hc : Continuous P := by
    dsimp [P, Y]
    fun_prop
  have hp : P 0 = -u n a (a - 2) := by
    have hs : (∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) *
        (0 : ℝ) ^ (2 * n - 2 * k)) = (-1 : ℝ) ^ n * u n a (a - 2) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro k hk hkn
        have hk' := Finset.mem_Icc.mp hk
        simp [zero_pow (show 2 * n - 2 * k ≠ 0 by omega)]
      · exact fun h => (h (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)).elim
    dsimp [P]
    rw [hs, zero_pow (by omega : 2 * n ≠ 0)]
    have hsgn : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    simpa only [zero_mul, zero_sub, mul_neg, ← mul_assoc, hsgn, one_mul]
  rw [← hp]
  apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  dsimp [P, D]
  have hs : (∑ k ∈ Finset.Icc 1 n, x ^ (2 * n) *
      ((-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k))) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) * x ^ (2 * n - 2 * k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (Finset.mem_Icc.mp hk).2
    rw [pow_sub₀ x hx0 (by omega : 2 * k ≤ 2 * n)]
    ring
  rw [← hs]
  simp only [← Finset.mul_sum]
  ring

private lemma exp_remainder_integral (m : ℕ) {y : ℝ} (hy : 0 < y) :
    expRemainder (m + 1) y =
      ∫ t in (0 : ℝ)..y, (y - t) ^ m / m.factorial * exp (-t) := by
  let f : ℝ → ℝ := fun t => exp ((-1 : ℝ) * t)
  have hc : ContDiff ℝ ⊤ f := by dsimp [f]; fun_prop
  have hs : taylorWithinEval f m (uIcc 0 y) 0 y =
      ∑ j ∈ Finset.range (m + 1), (-y) ^ j / j.factorial := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (ne_of_lt hy))
      (hc.of_le (by exact_mod_cast le_top)).contDiffAt left_mem_uIcc,
      iteratedDeriv_exp_const_mul]
    simp only [f, mul_zero, exp_zero, mul_one, sub_zero, smul_eq_mul,
      neg_mul, one_mul, div_eq_mul_inv]
    rw [neg_pow]
    ring
  have ht := taylor_integral_remainder (f := f)
    ((hc.of_le (by exact_mod_cast le_top : (m + 1 : ℕ∞ω) ≤ ⊤)).contDiffOn)
    (x₀ := 0) (x := y)
  have hfy : f y = exp (-y) := by simp [f]
  rw [hs, hfy] at ht
  rw [expRemainder_eq, ht, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  change (-1 : ℝ) ^ (m + 1) * ((y - t) ^ m / (m.factorial : ℝ) *
    iteratedDerivWithin (m + 1) f (uIcc 0 y) t) = _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (ne_of_lt hy))
    (hc.of_le (by exact_mod_cast le_top)).contDiffAt ht,
    iteratedDeriv_exp_const_mul]
  have hsgn : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1) = 1 := by
    rw [← mul_pow]; norm_num
  dsimp [f]
  simp only [neg_one_mul, smul_eq_mul]
  linear_combination ((y - t) ^ m / (m.factorial : ℝ) * exp (-t)) * hsgn

private lemma exp_remainder_scaled (m : ℕ) {y : ℝ} (hy : 0 < y) :
    expRemainder (m + 1) y / y ^ (m + 1) =
      ∫ s in (0 : ℝ)..1, (1 - s) ^ m / m.factorial * exp (-y * s) := by
  rw [exp_remainder_integral m hy]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => (y - t) ^ m / m.factorial * exp (-t))
    (a := (0 : ℝ)) (b := 1) y
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show y - y * s = y * (1 - s) by ring, mul_pow, pow_succ]
  field_simp

private lemma exp_remainder_upper_monotone (m : ℕ) :
    AntitoneOn (fun y : ℝ => expRemainder (m + 1) y / y ^ (m + 1)) (Ioi 0) := by
  intro y hy z hz hyz
  change 0 < y at hy
  change 0 < z at hz
  dsimp only
  rw [exp_remainder_scaled m hz, exp_remainder_scaled m hy]
  apply intervalIntegral.integral_mono_on zero_le_one
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro s hs
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (pow_nonneg (by linarith [hs.2]) m) (by positivity))
  apply exp_le_exp.mpr
  nlinarith [hs.1]

private lemma exp_remainder_lower_monotone (m : ℕ) :
    MonotoneOn (fun y : ℝ => expRemainder (m + 1) y / y ^ m) (Ioi 0) := by
  intro y hy z hz hyz
  change 0 < y at hy
  change 0 < z at hz
  dsimp only
  have he (q : ℝ) (hq : 0 < q) : expRemainder (m + 1) q / q ^ m =
      ∫ t in (0 : ℝ)..q, (1 - t / q) ^ m / m.factorial * exp (-t) := by
    rw [exp_remainder_integral m hq, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show 1 - t / q = (q - t) / q by field_simp, div_pow]
    ring
  rw [he y hy, he z hz]
  calc
    _ ≤ ∫ t in (0 : ℝ)..y, (1 - t / z) ^ m / m.factorial * exp (-t) := by
      apply intervalIntegral.integral_mono_on hy.le
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro t ht
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by have := (div_le_one hy).mpr ht.2; linarith)
      have hdiv := div_le_div_of_nonneg_left ht.1 hy hyz
      linarith
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval le_rfl hy.le hyz ?_
        (by apply Continuous.intervalIntegrable; fun_prop)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Ioc (0 : ℝ) z := by simpa [uIoc_of_le hz.le] using ht
      apply mul_nonneg _ (exp_nonneg _)
      apply div_nonneg _ (by positivity)
      exact pow_nonneg (sub_nonneg.mpr ((div_le_one hz).mpr ht'.2)) m

private lemma crossing_nonneg {w q : ℝ → ℝ} (hw : Continuous w) (hq : Continuous q)
    (hwn : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ w v)
    (hqm : MonotoneOn q (Icc (0 : ℝ) 1)) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (hcenter : (∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v) = 0) :
    0 ≤ ∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v * q v := by
  let c := sqrt μ
  have hc : c ∈ Icc (0 : ℝ) 1 := ⟨sqrt_nonneg _, (sqrt_le_one).mpr hμ.2⟩
  have hc2 : c ^ 2 = μ := sq_sqrt hμ.1
  have hnon : 0 ≤ ∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v * (q v - q c) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro v hv
    by_cases hvc : v ≤ c
    · have hvμ : v ^ 2 - μ ≤ 0 := by nlinarith [hv.1, hc.1]
      have hqv : q v - q c ≤ 0 := sub_nonpos.mpr (hqm hv hc hvc)
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hvμ (hwn v hv)) hqv
    · have hvμ : 0 ≤ v ^ 2 - μ := by nlinarith [hv.1, hc.1, lt_of_not_ge hvc]
      have hqv : 0 ≤ q v - q c := sub_nonneg.mpr (hqm hc hv (le_of_not_ge hvc))
      exact mul_nonneg (mul_nonneg hvμ (hwn v hv)) hqv
  have he : (∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v * (q v - q c)) =
      (∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v * q v) -
        q c * ∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * w v := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    ring
  rwa [he, hcenter, mul_zero, sub_zero] at hnon

private lemma mean_comparison (j : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hm : MonotoneOn (fun v => f v / (1 + v ^ 2) ^ j) (Icc (0 : ℝ) 1)) :
    B j * (∫ v in (0 : ℝ)..1, f v) ≤
      intPow j * ∫ v in (0 : ℝ)..1, v ^ 2 * f v := by
  have hb := moment_pos j
  have hi : 0 < intPow j := hb.1.trans hb.2
  let μ := B j / intPow j
  have hμ : μ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb.1.le hi.le, (div_le_one hi).mpr hb.2.le⟩
  have hc : Continuous (fun v : ℝ => f v / (1 + v ^ 2) ^ j) := by
    apply hf.div (by fun_prop)
    intro v
    positivity
  have he : (∫ v in (0 : ℝ)..1, (v ^ 2 - μ) * (1 + v ^ 2) ^ j) = 0 := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
    change B j - μ * intPow j = 0
    dsimp [μ]
    field_simp
    ring
  have h := crossing_nonneg (w := fun v : ℝ => (1 + v ^ 2) ^ j)
    (by fun_prop) hc (fun v _ => by positivity) hm hμ he
  have he' : (∫ v in (0 : ℝ)..1,
      (v ^ 2 - μ) * (1 + v ^ 2) ^ j * (f v / (1 + v ^ 2) ^ j)) =
      (∫ v in (0 : ℝ)..1, v ^ 2 * f v) - μ * ∫ v in (0 : ℝ)..1, f v := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    field_simp
    <;> ring
  rw [he'] at h
  have hmul := mul_nonneg hi.le h
  dsimp [μ] at hmul
  field_simp at hmul
  nlinarith

private lemma scaled_ratio_order (j r : ℕ) {z : ℝ} (hz : 0 < z)
    (hm : MonotoneOn (fun y : ℝ => expRemainder r y / y ^ j) (Ioi 0)) :
    MonotoneOn (fun v : ℝ => expRemainder r (z * (1 + v ^ 2)) / (1 + v ^ 2) ^ j)
      (Icc (0 : ℝ) 1) := by
  intro v hv w hw hvw
  have ha (v : ℝ) : 0 < z * (1 + v ^ 2) := by positivity
  have harg : z * (1 + v ^ 2) ≤ z * (1 + w ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hz.le
    have hs : v ^ 2 ≤ w ^ 2 := (sq_le_sq₀ hv.1 hw.1).mpr hvw
    linarith
  have h := mul_le_mul_of_nonneg_left (hm (ha v) (ha w) harg) (pow_nonneg hz.le j)
  have hz0 := hz.ne'
  convert h using 1 <;> simp only [mul_pow] <;> field_simp

private theorem taylor_moment_bounds (m : ℕ) {z : ℝ} (hz : 0 < z) :
    B m * (∫ v in (0 : ℝ)..1, expRemainder (m + 1) (z * (1 + v ^ 2))) ≤
      intPow m * ∫ v in (0 : ℝ)..1, v ^ 2 * expRemainder (m + 1) (z * (1 + v ^ 2)) ∧
    intPow (m + 1) * (∫ v in (0 : ℝ)..1, v ^ 2 * expRemainder (m + 1) (z * (1 + v ^ 2))) ≤
      B (m + 1) * ∫ v in (0 : ℝ)..1, expRemainder (m + 1) (z * (1 + v ^ 2)) := by
  have hc : Continuous (fun v : ℝ => expRemainder (m + 1) (z * (1 + v ^ 2))) :=
    (expRemainderContinuous _).comp (by fun_prop)
  constructor
  · exact mean_comparison m hc (scaled_ratio_order m (m + 1) hz (exp_remainder_lower_monotone m))
  · have hn : MonotoneOn (fun y : ℝ => -expRemainder (m + 1) y / y ^ (m + 1)) (Ioi 0) := by
      intro y hy z hz hyz
      simpa only [neg_div, neg_le_neg_iff] using exp_remainder_upper_monotone m hy hz hyz
    have hm : MonotoneOn (fun v : ℝ => -expRemainder (m + 1) (z * (1 + v ^ 2)) /
        (1 + v ^ 2) ^ (m + 1)) (Icc (0 : ℝ) 1) := by
      intro v hv w hw hvw
      have h := hn (by positivity : 0 < z * (1 + v ^ 2))
        (by positivity : 0 < z * (1 + w ^ 2)) (by
          apply mul_le_mul_of_nonneg_left _ hz.le
          have hs : v ^ 2 ≤ w ^ 2 := (sq_le_sq₀ hv.1 hw.1).mpr hvw
          linarith)
      have h := mul_le_mul_of_nonneg_left h (pow_nonneg hz.le (m + 1))
      have hz0 := hz.ne'
      convert h using 1 <;> simp only [mul_pow] <;> field_simp
    have h := mean_comparison (m + 1) hc.neg hm
    simpa only [Pi.neg_apply, mul_neg, intervalIntegral.integral_neg, neg_le_neg_iff] using h

private theorem parameter_le_of_native_nonneg (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * D n x a) :
    a ≤ theta (n - 2) := by
  have hu : u n a (a - 2) ≤ 0 := by
    have hpos : ∀ᶠ x : ℝ in (𝓝[>] 0), 0 ≤ x ^ (2 * n) * ((-1 : ℝ) ^ n * D n x a) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (pow_nonneg (le_of_lt hx) _) (h x hx)
    have hh : 0 ≤ -u n a (a - 2) :=
      ge_of_tendsto (native_zero_limit n (by omega) a) hpos
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [u_moment] at hu
  have hfac : 0 < ((2 * j + 3).factorial : ℝ) / (4 ^ (j + 1) * j.factorial) := by positivity
  have hh : intPow j + (2 * a - 1) * B j ≤ 0 := by
    by_contra! hh
    have := mul_pos hfac hh
    linarith
  have hb := (moment_pos j).1
  have hdiv : intPow j / B j ≤ 1 - 2 * a := (div_le_iff₀ hb).mpr (by nlinarith)
  simp only [Nat.add_sub_cancel, theta]
  linarith

private lemma native_kernel_base {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Y a (a - 2) x - (a - 1) =
      ∫ t in Ioi (0 : ℝ), exp (-x * t) *
        (t ^ 3 / 4 * J (fun v => 1 + (2 * a - 1) * v ^ 2) t) := by
  have hr : millsRatio x = ∫ t in Ioi (0 : ℝ), exp (-x * t) * exp (-t ^ 2 / 2) := by
    rw [millsLaplace]
    apply integral_congr_ae
    filter_upwards with t
    rw [← exp_add]
    congr 1
    ring
  have hr2 : millsRatio x ^ 2 = ∫ t in Ioi (0 : ℝ), exp (-x * t) * q0 t := by
    rw [millsSquareConvolution hx.le]
    apply integral_congr_ae
    filter_upwards with t
    rw [convolutionClosed]
    simp only [q0, J, one_mul]
  have hh : IntegrableOn (fun t : ℝ => exp (-x * t) * exp (-t ^ 2 / 2)) (Ioi 0) := by
    apply (millsLaplaceIntegrable hx.le).congr_fun _ measurableSet_Ioi
    intro t _
    dsimp only
    rw [← exp_add]
    congr 1
    ring
  have hth : IntegrableOn (fun t : ℝ => exp (-x * t) * (-t * exp (-t ^ 2 / 2))) (Ioi 0) := by
    have he := (TwoScaleEndpointMoments.exponential_moment x hx 1).1
    simp only [← neg_mul] at he
    apply he.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (exp_nonneg _), norm_neg,
      Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (exp_nonneg _)]
    simp only [pow_one]
    nlinarith [mul_le_of_le_one_right (mul_nonneg (exp_nonneg (-x * t)) ht.le)
      (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]) : exp (-t ^ 2 / 2) ≤ 1)]
  have lh : Tendsto (fun t : ℝ => exp (-x * t) * exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t : ℝ => exp (-x * t)) (fun t => ?_)
      (by simpa only [rpow_zero, one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 x hx)
    simp only [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
    exact mul_le_of_le_one_right (exp_nonneg _) (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  have ibh := laplaceIBP (f := fun t : ℝ => exp (-t ^ 2 / 2))
    (g := fun t : ℝ => -t * exp (-t ^ 2 / 2))
    (fun t => by
      convert (((hasDerivAt_id t).pow 2).neg.div_const 2).exp using 1 <;>
        (try ext z) <;> dsimp <;> ring) hh hth lh
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, exp_zero] at ibh
  have hq : IntegrableOn (fun t : ℝ => exp (-x * t) * q0 t) (Ioi 0) := by
    convert JMomentIntegrable (fun _ => 1) continuous_const 1 hx using 1
    ext t
    dsimp [q0]
    ring
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * K t) (Ioi 0) := by
    apply ((JMomentIntegrable (fun v => v ^ 2 * (1 - v ^ 2)) (by fun_prop) 5 hx).div_const 8).congr
    filter_upwards with t
    dsimp [K]
    ring
  have hid (t : ℝ) : K t + (a + 1) * (q0 t - t * exp (-t ^ 2 / 2)) =
      t ^ 3 / 4 * J (fun v => 1 + (2 * a - 1) * v ^ 2) t := by
    let e : ℝ → ℝ := fun v => exp (-(1 + v ^ 2) * t ^ 2 / 4)
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1)
      (f := fun v => v * e v) (f' := fun v => (1 - v ^ 2 * t ^ 2 / 2) * e v)
      (fun v _ => by
        dsimp [e]
        convert (hasDerivAt_id v).mul ((((hasDerivAt_id v).pow 2).const_add 1 |>.neg |>.mul_const (t ^ 2) |>.div_const 4).exp) using 1 <;>
          (try ext z) <;> dsimp <;> ring)
      (by apply Continuous.intervalIntegrable; dsimp [e]; fun_prop)
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1)
      (f := fun v => v * (1 - v ^ 2) * e v)
      (f' := fun v => ((1 - 3 * v ^ 2) - t ^ 2 / 2 * (v ^ 2 * (1 - v ^ 2))) * e v)
      (fun v _ => by
        dsimp [e]
        convert ((hasDerivAt_id v).mul ((hasDerivAt_const v 1).sub ((hasDerivAt_id v).pow 2))).mul
          ((((hasDerivAt_id v).pow 2).const_add 1 |>.neg |>.mul_const (t ^ 2) |>.div_const 4).exp) using 1 <;>
          (try ext z) <;> dsimp <;> ring)
      (by apply Continuous.intervalIntegrable; dsimp [e]; fun_prop)
    have hc0 : (∫ v in (0 : ℝ)..1, (1 - v ^ 2 * t ^ 2 / 2) * e v) =
        J (fun _ => 1) t - t ^ 2 / 2 * J (fun v => v ^ 2) t := by
      unfold J
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp [e]
      ring
    have hc1 : (∫ v in (0 : ℝ)..1,
        ((1 - 3 * v ^ 2) - t ^ 2 / 2 * (v ^ 2 * (1 - v ^ 2))) * e v) =
        J (fun _ => 1) t - 3 * J (fun v => v ^ 2) t -
          t ^ 2 / 2 * J (fun v => v ^ 2 * (1 - v ^ 2)) t := by
      unfold J
      repeat rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp [e]
      ring
    have hc2 : J (fun v => 1 + (2 * a - 1) * v ^ 2) t =
        J (fun _ => 1) t + (2 * a - 1) * J (fun v => v ^ 2) t := by
      unfold J
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      ring
    rw [hc0] at h0
    rw [hc1] at h1
    dsimp [e] at h0 h1
    norm_num only [one_pow, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
      one_mul, sub_self, sub_zero] at h0 h1
    have h0' : J (fun _ => 1) t - t ^ 2 / 2 * J (fun v => v ^ 2) t = exp (-t ^ 2 / 2) := by
      convert h0 using 1 <;> congr 1 <;> ring
    unfold K q0
    rw [hc2]
    linear_combination (a + 1) * t * h0' - t ^ 3 / 4 * h1
  have he : (∫ t in Ioi (0 : ℝ), exp (-x * t) *
      (t ^ 3 / 4 * J (fun v => 1 + (2 * a - 1) * v ^ 2) t)) =
      (∫ t in Ioi (0 : ℝ), exp (-x * t) * K t) +
        (a + 1) * ((∫ t in Ioi (0 : ℝ), exp (-x * t) * q0 t) +
          ∫ t in Ioi (0 : ℝ), exp (-x * t) * (-t * exp (-t ^ 2 / 2))) := by
    rw [← integral_add hq hth, ← integral_const_mul]
    have he1 := integral_add hk ((hq.add hth).const_mul (a + 1))
    simp only [Pi.add_apply] at he1
    rw [← he1]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hid]
    ring
  rw [he, ← kernelLaplace hx (millsRatio x) hr hr2, ← hr2, ibh, ← hr]
  unfold Y
  ring

private def kernel (r : ℕ) (a t : ℝ) : ℝ :=
  t ^ 3 / 4 * ∫ v in (0 : ℝ)..1,
    ((1 - 2 * a) * v ^ 2 - 1) * expRemainder r ((1 + v ^ 2) * t ^ 2 / 4)

private lemma kernel_continuous (r : ℕ) (a : ℝ) : Continuous (kernel r a) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ((1 - 2 * a) * p.2 ^ 2 - 1) * expRemainder r ((1 + p.2 ^ 2) * p.1 ^ 2 / 4)) := by
    apply Continuous.mul (by fun_prop)
    exact (expRemainderContinuous r).comp (by fun_prop)
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun t v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) * expRemainder r ((1 + v ^ 2) * t ^ 2 / 4))
    hc (s := Icc (0 : ℝ) 1) isCompact_Icc
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  exact (by fun_prop : Continuous (fun t : ℝ => t ^ 3 / 4)).mul hi

private lemma kernel_bound (r : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖kernel r a t‖ ≤ (|1 - 2 * a| + 1) * t ^ (2 * r + 3) := by
  have hb (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖((1 - 2 * a) * v ^ 2 - 1) * expRemainder r ((1 + v ^ 2) * t ^ 2 / 4)‖ ≤
        (|1 - 2 * a| + 1) * t ^ (2 * r) := by
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have harg : 0 ≤ (1 + v ^ 2) * t ^ 2 / 4 := by positivity
    have harg' : (1 + v ^ 2) * t ^ 2 / 4 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    have he := expRemainderBounds r harg
    have he' : expRemainder r ((1 + v ^ 2) * t ^ 2 / 4) ≤ t ^ (2 * r) := by
      calc
        _ ≤ ((1 + v ^ 2) * t ^ 2 / 4) ^ r / r.factorial := he.2
        _ ≤ (t ^ 2) ^ r := (div_le_self (by positivity)
          (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos r))).trans
            (pow_le_pow_left₀ harg harg' r)
        _ = _ := by rw [← pow_mul]
    have hw : |(1 - 2 * a) * v ^ 2 - 1| ≤ |1 - 2 * a| + 1 := by
      calc
        _ ≤ |(1 - 2 * a) * v ^ 2| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg v), abs_one]; nlinarith [abs_nonneg (1 - 2 * a)]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg he.1]
    exact mul_le_mul hw he' he.1 (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (|1 - 2 * a| + 1) * t ^ (2 * r))
    (f := fun v => ((1 - 2 * a) * v ^ 2 - 1) * expRemainder r ((1 + v ^ 2) * t ^ 2 / 4))
    (fun v hv => hb v (Ioc_subset_Icc_self (by simpa [uIoc_of_le zero_le_one] using hv)))
  simp only [sub_zero, abs_one, mul_one] at hi
  unfold kernel
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ t ^ 3 / 4)]
  calc
    _ ≤ t ^ 3 / 4 * ((|1 - 2 * a| + 1) * t ^ (2 * r)) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := by
      rw [pow_add]
      have hnon : 0 ≤ (|1 - 2 * a| + 1) * (t ^ (2 * r) * t ^ 3) := by positivity
      nlinarith

private lemma kernel_moments (r m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-x * t) * kernel r a t) (Ioi 0) := by
  have he := (TwoScaleEndpointMoments.exponential_moment x hx (m + 2 * r + 3)).1
  simp only [← neg_mul] at he
  apply (he.const_mul (|1 - 2 * a| + 1)).mono'
    (((by fun_prop : Continuous (fun t : ℝ => t ^ m * exp (-x * t))).mul
      (kernel_continuous r a)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t ^ m * exp (-x * t) * kernel r a t‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))]
  calc
    _ ≤ t ^ m * exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 3)) :=
      mul_le_mul_of_nonneg_left (kernel_bound r a ht.le)
        (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    _ = _ := by rw [show m + 2 * r + 3 = m + (2 * r + 3) by omega, pow_add]; ring

private lemma kernel_rec (r : ℕ) (a t : ℝ) :
    kernel (r + 1) a t =
      -(t ^ (2 * r + 3) / (4 ^ (r + 1) * r.factorial) * (intPow r + (2 * a - 1) * B r)) -
        kernel r a t := by
  unfold kernel
  simp_rw [expRemainderRec]
  have hid (v : ℝ) :
      ((1 - 2 * a) * v ^ 2 - 1) * (((1 + v ^ 2) * t ^ 2 / 4) ^ r / r.factorial -
        expRemainder r ((1 + v ^ 2) * t ^ 2 / 4)) =
      -(t ^ (2 * r) / (4 ^ r * r.factorial)) *
        ((1 + v ^ 2) ^ r + (2 * a - 1) * (v ^ 2 * (1 + v ^ 2) ^ r)) -
      ((1 - 2 * a) * v ^ 2 - 1) * expRemainder r ((1 + v ^ 2) * t ^ 2 / 4) := by
    rw [div_pow, mul_pow, ← pow_mul]
    ring
  simp_rw [hid]
  have hc : Continuous (fun v : ℝ => ((1 - 2 * a) * v ^ 2 - 1) *
      expRemainder r ((1 + v ^ 2) * t ^ 2 / 4)) :=
    (by fun_prop : Continuous (fun v : ℝ => (1 - 2 * a) * v ^ 2 - 1)).mul
      ((expRemainderContinuous r).comp (by fun_prop))
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
  change _ = -(t ^ (2 * r + 3) / (4 ^ (r + 1) * r.factorial) * (intPow r + (2 * a - 1) * B r)) - _
  unfold intPow B
  rw [pow_add, pow_succ]
  ring

private lemma native_D_rec (n : ℕ) (x a : ℝ) :
    D (n + 1) x a = D n x a - (-1 : ℝ) ^ (n + 1) * u (n + 1) a (a - 2) / x ^ (2 * (n + 1)) := by
  rw [D, D, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  ring

private lemma u_one (a : ℝ) : u 1 a (a - 2) = 0 := by
  have he : u 1 a (a - 2) = (a - 1) * coeff 1 + (1 - a) * coeff 0 := by
    norm_num [u, coeff]
    ring
  rw [he, show (1 : ℕ) = 0 + 1 from rfl, coeff_rec, coeff_zero]
  ring

private lemma kernel_laplace_rec (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    moment (kernel (r + 1) a) 0 x =
      -u (r + 2) a (a - 2) / x ^ (2 * r + 4) - moment (kernel r a) 0 x := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x * t) * kernel r a t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using kernel_moments r 0 a hx
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 3)
  simp only [← neg_mul] at hm
  calc
    _ = ∫ t in Ioi (0 : ℝ), -(t ^ (2 * r + 3) * exp (-x * t)) *
        ((intPow r + (2 * a - 1) * B r) / (4 ^ (r + 1) * r.factorial)) -
        exp (-x * t) * kernel r a t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernel_rec]
      simp only [pow_zero, one_mul]
      ring
    _ = -((2 * r + 3).factorial : ℝ) / x ^ (2 * r + 4) *
        ((intPow r + (2 * a - 1) * B r) / (4 ^ (r + 1) * r.factorial)) -
        moment (kernel r a) 0 x := by
      have hsub := integral_sub
        (hm.1.neg.mul_const ((intPow r + (2 * a - 1) * B r) / (4 ^ (r + 1) * r.factorial))) hk
      simp only [Pi.neg_apply, Pi.sub_apply] at hsub
      rw [hsub, integral_mul_const, integral_neg, hm.2]
      simp only [moment, pow_zero, one_mul, show 2 * r + 3 + 1 = 2 * r + 4 by omega]
      ring
    _ = _ := by rw [u_moment]; ring

private lemma native_representation (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ (r + 1) * D (r + 1) x a = moment (kernel r a) 0 x := by
  induction r with
  | zero =>
    have hd : D 1 x a = Y a (a - 2) x - (a - 1) := by simp [D, u_one]
    have hk0 (t : ℝ) : kernel 0 a t = -(t ^ 3 / 4 * J (fun v => 1 + (2 * a - 1) * v ^ 2) t) := by
      unfold kernel J
      simp only [expRemainder_eq, pow_zero, Finset.range_zero, Finset.sum_empty, sub_zero, one_mul]
      rw [← mul_neg, ← intervalIntegral.integral_neg]
      congr 1
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      ring
    rw [Nat.zero_add, pow_one, hd, native_kernel_base hx a, moment]
    simp only [pow_zero, one_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [hk0]
    ring
  | succ r ih =>
    rw [show r + 1 + 1 = (r + 1) + 1 by omega, native_D_rec,
      kernel_laplace_rec r a hx, ← ih]
    have hs : (-1 : ℝ) ^ (r + 1) * (-1 : ℝ) ^ (r + 1) = 1 := by rw [← mul_pow]; norm_num
    simp only [pow_succ, show 2 * (r + 1 + 1) = 2 * r + 4 by omega]
    linear_combination -(u (r + 2) a (a - 2) / x ^ (2 * r + 4)) * hs

private lemma kernel_signs (m : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (a ≤ theta m → 0 ≤ kernel (m + 1) a t) ∧
      (theta (m + 1) ≤ a → kernel (m + 1) a t ≤ 0) := by
  let z := t ^ 2 / 4
  have hz : 0 < z := by dsimp [z]; positivity
  let M : ℝ := ∫ v in (0 : ℝ)..1, expRemainder (m + 1) (z * (1 + v ^ 2))
  let N : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * expRemainder (m + 1) (z * (1 + v ^ 2))
  have hN : 0 ≤ N := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro v _
    exact mul_nonneg (sq_nonneg v) (expRemainderBounds (m + 1) (by positivity)).1
  have hcomp : B m * M ≤ intPow m * N ∧ intPow (m + 1) * N ≤ B (m + 1) * M :=
    taylor_moment_bounds m hz
  have hc : Continuous (fun v : ℝ => expRemainder (m + 1) (z * (1 + v ^ 2))) :=
    (expRemainderContinuous _).comp (by fun_prop)
  have he : kernel (m + 1) a t = t ^ 3 / 4 * ((1 - 2 * a) * N - M) := by
    unfold kernel
    congr 1
    dsimp [N, M]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; exact (by fun_prop).mul hc)
        (hc.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [show (1 + v ^ 2) * t ^ 2 / 4 = z * (1 + v ^ 2) by dsimp [z]; ring]
    ring
  rw [he]
  constructor
  · intro ha
    have hb := (moment_pos m).1
    have hparam : intPow m / B m ≤ 1 - 2 * a := by dsimp [theta] at ha; linarith
    have hparam' := (div_le_iff₀ hb).mp hparam
    have hchain := hcomp.1.trans (mul_le_mul_of_nonneg_right hparam' hN)
    have hinner : M ≤ (1 - 2 * a) * N := (mul_le_mul_iff_right₀ hb).mp (by
      convert hchain using 1 <;> ring)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hinner)
  · intro ha
    have hb := (moment_pos (m + 1)).1
    have hparam : 1 - 2 * a ≤ intPow (m + 1) / B (m + 1) := by dsimp [theta] at ha; linarith
    have hparam' := (le_div_iff₀ hb).mp hparam
    have hchain := (mul_le_mul_of_nonneg_right hparam' hN).trans hcomp.2
    have hinner : (1 - 2 * a) * N ≤ M := (mul_le_mul_iff_right₀ hb).mp (by
      convert hchain using 1 <;> ring)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hinner)

private lemma native_cm_ranges (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (a ≤ theta (n - 2) → CompletelyMonotoneOn (fun x => (-1 : ℝ) ^ n * D n x a)) ∧
    (theta (n - 1) ≤ a → CompletelyMonotoneOn (fun x => -((-1 : ℝ) ^ n * D n x a))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have transfer {f g : ℝ → ℝ} (hg : CompletelyMonotoneOn g) (he : EqOn f g (Ioi 0)) :
      CompletelyMonotoneOn f := by
    refine ⟨hg.1.congr (fun x hx => he hx), ?_⟩
    intro k x hx
    rw [he.iteratedDeriv_of_isOpen isOpen_Ioi k hx]
    exact hg.2 k x hx
  have he : EqOn (fun x => (-1 : ℝ) ^ (m + 2) * D (m + 2) x a)
      (moment (kernel (m + 1) a) 0) (Ioi 0) := by
    intro x hx
    exact native_representation (m + 1) a hx
  constructor
  · intro ha
    have hc := laplaceCM (kernel_continuous (m + 1) a)
      (fun t ht => (kernel_signs m a ht).1 (by simpa using ha))
      (fun k x hx => kernel_moments (m + 1) k a hx)
    exact transfer hc he
  · intro ha
    have hc := laplaceCM (kernel_continuous (m + 1) a).neg
      (fun t ht => neg_nonneg.mpr ((kernel_signs m a ht).2 (by simpa using ha)))
      (fun k x hx => by
        apply (kernel_moments (m + 1) k a hx).neg.congr
        filter_upwards with t
        dsimp only [Pi.neg_apply]
        ring)
    apply transfer hc
    intro x hx
    change -((-1 : ℝ) ^ (m + 2) * D (m + 2) x a) = moment (-kernel (m + 1) a) 0 x
    rw [show moment (-kernel (m + 1) a) 0 x = -moment (kernel (m + 1) a) 0 x by
      simp only [moment, Pi.neg_apply, mul_neg, integral_neg]
    ]
    exact congrArg Neg.neg (he hx)

private lemma moment_bound (r : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖moment (kernel r a) 0 x‖ ≤
      (|1 - 2 * a| + 1) * ((2 * r + 3).factorial : ℝ) / x ^ (2 * r + 4) := by
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2 * r + 3)
  simp only [← neg_mul] at hm
  have hi := norm_integral_le_of_norm_le (hm.1.const_mul (|1 - 2 * a| + 1)) (f := fun t : ℝ => exp (-x * t) * kernel r a t) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
    calc
      _ ≤ exp (-x * t) * ((|1 - 2 * a| + 1) * t ^ (2 * r + 3)) :=
        mul_le_mul_of_nonneg_left (kernel_bound r a ht.le) (exp_nonneg _)
      _ = _ := by ring)
  rw [integral_const_mul, hm.2] at hi
  simpa only [moment, pow_zero, one_mul, show 2 * r + 3 + 1 = 2 * r + 4 by omega,
    mul_div_assoc] using hi

private lemma signed_D_rec (n : ℕ) (x a : ℝ) :
    (-1 : ℝ) ^ n * D n x a + (-1 : ℝ) ^ (n + 1) * D (n + 1) x a =
      -u (n + 1) a (a - 2) / x ^ (2 * (n + 1)) := by
  rw [native_D_rec]
  have hs : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  simp only [pow_succ] at hs ⊢
  linear_combination -(u (n + 1) a (a - 2) / x ^ (2 * (n + 1))) * hs

private lemma native_infinity_limit (n : ℕ) (a : ℝ) :
    Tendsto (fun x : ℝ => x ^ (2 * n + 2) * ((-1 : ℝ) ^ n * D n x a))
      atTop (𝓝 (-u (n + 1) a (a - 2))) := by
  have hsmall : Tendsto (fun x : ℝ => x ^ (2 * n + 2) *
      ((-1 : ℝ) ^ (n + 1) * D (n + 1) x a)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => ((|1 - 2 * a| + 1) * (2 * n + 3).factorial) * (x⁻¹) ^ 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow 2).const_mul
        ((|1 - 2 * a| + 1) * ((2 * n + 3).factorial : ℝ))
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [native_representation n a hx, norm_mul,
      Real.norm_of_nonneg (pow_nonneg hx.le _)]
    calc
      _ ≤ x ^ (2 * n + 2) *
          ((|1 - 2 * a| + 1) * ((2 * n + 3).factorial : ℝ) / x ^ (2 * n + 4)) :=
        mul_le_mul_of_nonneg_left (moment_bound n a hx) (by positivity)
      _ = _ := by
        have hx0 := hx.ne'
        rw [show 2 * n + 4 = (2 * n + 2) + 2 by omega, pow_add]
        field_simp
        <;> ring
  have hlim : Tendsto (fun x : ℝ => -u (n + 1) a (a - 2) -
      x ^ (2 * n + 2) * ((-1 : ℝ) ^ (n + 1) * D (n + 1) x a))
      atTop (𝓝 (-u (n + 1) a (a - 2))) := by
    simpa using tendsto_const_nhds.sub hsmall
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hrec := signed_D_rec n x a
  have hx0 := hx.ne'
  have hpow : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [hpow] at hrec
  field_simp at hrec
  linear_combination -hrec

private lemma parameter_ge_of_native_nonpos (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (h : ∀ x : ℝ, 0 < x → 0 ≤ -((-1 : ℝ) ^ n * D n x a)) :
    theta (n - 1) ≤ a := by
  have hu : 0 ≤ u (n + 1) a (a - 2) := by
    have hpos : ∀ᶠ x : ℝ in atTop, x ^ (2 * n + 2) * ((-1 : ℝ) ^ n * D n x a) ≤ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonneg.mp (h x hx))
    have hh : -u (n + 1) a (a - 2) ≤ 0 := le_of_tendsto (native_infinity_limit n a) hpos
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by omega, u_moment] at hu
  have hfac : 0 < ((2 * j + 3).factorial : ℝ) / (4 ^ (j + 1) * j.factorial) := by positivity
  have hh : 0 ≤ intPow j + (2 * a - 1) * B j := by
    by_contra! hh
    have := mul_neg_of_pos_of_neg hfac hh
    linarith
  have hb := (moment_pos j).1
  have hdiv : 1 - 2 * a ≤ intPow j / B j := (le_div_iff₀ hb).mpr (by nlinarith)
  simp only [Nat.add_sub_cancel, theta]
  linarith

/-- Both global-sign and complete-monotonicity classifications for the original remainder. -/
theorem result (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (((∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * D n x a) ↔
        CompletelyMonotoneOn (fun x => (-1 : ℝ) ^ n * D n x a)) ∧
      (CompletelyMonotoneOn (fun x => (-1 : ℝ) ^ n * D n x a) ↔ a ≤ theta (n - 2))) ∧
    (((∀ x : ℝ, 0 < x → 0 ≤ -((-1 : ℝ) ^ n * D n x a)) ↔
        CompletelyMonotoneOn (fun x => -((-1 : ℝ) ^ n * D n x a))) ∧
      (CompletelyMonotoneOn (fun x => -((-1 : ℝ) ^ n * D n x a)) ↔ theta (n - 1) ≤ a)) := by
  have hzero {f : ℝ → ℝ} (hf : CompletelyMonotoneOn f) : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
    intro x hx
    simpa only [pow_zero, iteratedDeriv_zero, one_mul] using hf.2 0 x hx
  have hp := (native_cm_ranges n hn a).1
  have hm := (native_cm_ranges n hn a).2
  exact ⟨⟨⟨fun h => hp (parameter_le_of_native_nonneg n hn a h), hzero⟩,
      ⟨fun h => parameter_le_of_native_nonneg n hn a (hzero h), hp⟩⟩,
    ⟨⟨fun h => hm (parameter_ge_of_native_nonpos n hn a h), hzero⟩,
      ⟨fun h => parameter_ge_of_native_nonpos n hn a (hzero h), hm⟩⟩⟩

end D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
