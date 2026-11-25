/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerPrimeTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerPrimeTail
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Finite prime-power tails and arbitrary fixed clipped activation layers. -/

import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder

/-!
# Finite prime-power tails and fixed activation layers

The real interval `(y,z]` is the finite prime interval of
`QuantitativePrimeAbel`. The finite Abel proof follows the method of
`CubicActivationResidual` with variable natural exponent. For `k = m - 1`,
the negative derivative of `1 / (u ^ k * log u)` supplies an integrable
comparison on the same finite interval. The upper endpoint contributes a
factor bounded by `y / z`. The lower endpoint contributes `-1` to the
normalized limit, and the integral contributes `m / (m - 1)`.

The activation cutoff solves `t ^ m * log t = prefixH P * prefixEll P`.
Its normalization is `t / (prefixH P) ^ (1 / m)`. Multiplying this
normalization by the sum of `theta t / t` and the normalized finite tail
gives the scaled activation layer by an exact identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail

open Real Filter MeasureTheory Finset
open scoped Topology BigOperators
open QuantitativePrimeAbel RealInfimumPrimeBoundary

/-- The reciprocal power sum over actual primes in the real interval `(y,z]`. -/
def primePowerTail (m : ℕ) (y z : ℝ) : ℝ :=
  ∑ p ∈ primeInterval y z, 1 / (p : ℝ) ^ m

private theorem finite_power_abel (k : ℕ) {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    IntervalIntegrable (fun u => primeCount u / u ^ (k + 2)) volume y z ∧
    primePowerTail (k + 1) y z = primeCount z / z ^ (k + 1) -
      primeCount y / y ^ (k + 1) +
      ((k : ℝ) + 1) * (∫ u in y..z, primeCount u / u ^ (k + 2)) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  let f : ℝ → ℝ := fun u => 1 / u ^ (k + 1)
  let a : ℝ := (k : ℝ) + 1
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hy0 : 0 < y := by linarith
  have hc (u : ℝ) : (∑ p ∈ Icc 0 ⌊u⌋₊, c p) = primeCount u := by
    rw [primeCount, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
    simp only [c, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hd (u : ℝ) (hu : u ∈ Set.Icc y z) :
      HasDerivAt f (-a / u ^ (k + 2)) u := by
    have hu0 := (hy0.trans_le hu.1).ne'
    have hp : HasDerivAt (fun v : ℝ => v ^ (k + 1)) (a * u ^ k) u := by
      simpa only [a, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq, mul_one] using
        (hasDerivAt_id' u).fun_pow (k + 1)
    change HasDerivAt (fun v : ℝ => 1 / v ^ (k + 1)) (-a / u ^ (k + 2)) u
    convert (hasDerivAt_const u (1 : ℝ)).fun_div hp (pow_ne_zero (k + 1) hu0) using 1
    simp only [zero_mul, one_mul, zero_sub]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ u (k + 1), pow_succ u k]
    field_simp [hu0, pow_ne_zero k hu0]
  have hf : IntegrableOn (deriv f) (Set.Icc y z) := by
    have hcont : ContinuousOn (fun u : ℝ => -a / u ^ (k + 2)) (Set.Icc y z) :=
      continuousOn_const.div (continuousOn_id.pow (k + 2))
        (fun u hu => pow_ne_zero _ (hy0.trans_le hu.1).ne')
    exact hcont.integrableOn_Icc.congr_fun (fun u hu => (hd u hu).deriv.symm)
      measurableSet_Icc
  have hs : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) = primePowerTail (k + 1) y z := by
    simp only [primePowerTail, primeInterval, sum_filter, c, f, mul_ite, mul_one, mul_zero]
  have hab := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun u hu => (hd u hu).differentiableAt) hf
  simp_rw [hc] at hab
  rw [hs, ← intervalIntegral.integral_of_le hyz] at hab
  have hprod : IntervalIntegrable (fun u => deriv f u * primeCount u) volume y z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr (by
      simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hf (m := 0))
  have heq (u : ℝ) (hu : u ∈ Set.Icc y z) :
      deriv f u * primeCount u = -a * (primeCount u / u ^ (k + 2)) := by
    rw [(hd u hu).deriv]
    ring
  have hi : IntervalIntegrable (fun u => primeCount u / u ^ (k + 2)) volume y z := by
    refine (hprod.const_mul (-1 / a)).congr ?_
    intro u hu
    rw [Set.uIoc_of_le hyz] at hu
    change (-1 / a) * (deriv f u * primeCount u) = primeCount u / u ^ (k + 2)
    rw [heq u ⟨hu.1.le, hu.2⟩, ← mul_assoc]
    have hcanc : (-1 / a) * -a = 1 := by field_simp [ha0.ne']
    rw [hcanc, one_mul]
  have hI : (∫ u in y..z, deriv f u * primeCount u) =
      -a * (∫ u in y..z, primeCount u / u ^ (k + 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hyz]
    exact heq
  rw [hI] at hab
  refine ⟨hi, ?_⟩
  rw [hab]
  dsimp [f, a]
  ring

private def tailPrimitive (k : ℕ) (u : ℝ) : ℝ := 1 / (u ^ k * log u)

private def tailKernel (k : ℕ) (u : ℝ) : ℝ :=
  ((k : ℝ) + 1 / log u) / (u ^ (k + 1) * log u)

private theorem tail_primitive_integral (k : ℕ) (hk : 1 ≤ k) {y z : ℝ}
    (hy : 1 < y) (hyz : y ≤ z) :
    IntervalIntegrable (tailKernel k) volume y z ∧
    (∫ u in y..z, tailKernel k u) = tailPrimitive k y - tailPrimitive k z := by
  have hd (u : ℝ) (hu : u ∈ Set.Icc y z) :
      HasDerivAt (tailPrimitive k) (-tailKernel k u) u := by
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hlog := (log_pos (hy.trans_le hu.1)).ne'
    have hp : HasDerivAt (fun v : ℝ => v ^ k) ((k : ℝ) * u ^ (k - 1)) u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id' u).fun_pow k
    change HasDerivAt (fun v : ℝ => 1 / (v ^ k * log v)) (-tailKernel k u) u
    convert (hasDerivAt_const u (1 : ℝ)).fun_div (hp.mul (hasDerivAt_log hu0))
      (mul_ne_zero (pow_ne_zero k hu0) hlog) using 1
    dsimp only [tailKernel, Pi.mul_apply]
    rw [pow_succ u k, show u ^ k = u ^ (k - 1) * u by
      calc
        u ^ k = u ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk]
        _ = _ := pow_succ _ _]
    field_simp [hu0, hlog, pow_ne_zero (k - 1) hu0]
    ring
  have hi : IntervalIntegrable (tailKernel k) volume y z := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hlog := (log_pos (hy.trans_le hu.1)).ne'
    have hl := (hasDerivAt_log hu0).continuousAt
    exact ((continuousAt_const.add (continuousAt_const.div hl hlog)).div
      ((continuousAt_id.pow (k + 1)).mul hl) (mul_ne_zero (pow_ne_zero _ hu0) hlog)
      ).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := tailPrimitive k) (f' := fun u => -tailKernel k u) (a := y) (b := z)
    (fun u hu => hd u (by simpa only [Set.uIcc_of_le hyz] using hu)) hi.neg
  rw [intervalIntegral.integral_neg] at h
  exact ⟨hi, by linarith only [h]⟩

private theorem endpoint_factor_le (k : ℕ) (hk : 1 ≤ k) {y z : ℝ}
    (hy : 1 < y) (hyz : y ≤ z) :
    y ^ k * log y / (z ^ k * log z) ≤ y / z := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := hy0.trans_le hyz
  have hLz := log_pos (hy.trans_le hyz)
  cases k with
  | zero => omega
  | succ j =>
    rw [pow_succ y j, pow_succ z j]
    apply (div_le_div_iff₀ (mul_pos (mul_pos (pow_pos hz0 j) hz0) hLz) hz0).mpr
    calc
      (y ^ j * y * log y) * z = (y ^ j * log y) * (y * z) := by ring
      _ ≤ (z ^ j * log z) * (y * z) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ hy0.le hyz _) (log_le_log hy0 hyz)
            (log_pos hy).le (pow_nonneg hz0.le _)) (mul_nonneg hy0.le hz0.le)
      _ = y * (z ^ j * z * log z) := by ring

/-- Finite uniform comparison with both endpoint values from Abel summation. -/
private theorem finite_power_error (k : ℕ) (hk : 1 ≤ k) {y z η : ℝ}
    (hy : 1 < y) (hyz : y ≤ z) (hη : 0 ≤ η)
    (hlog : 1 / log y ≤ η)
    (hπ : ∀ u ∈ Set.Icc y z, |log u * primeCount u / u - 1| ≤ η) :
    |y ^ k * log y * primePowerTail (k + 1) y z - 1 / (k : ℝ)| ≤
      6 * η + y ^ k * log y / (z ^ k * log z) := by
  let D : ℝ := y ^ k * log y
  let R : ℝ := D / (z ^ k * log z)
  let I : ℝ := ∫ u in y..z, primeCount u / u ^ (k + 2)
  let J : ℝ := D * ((k : ℝ) * I)
  let a : ℝ := 1 + 1 / (k : ℝ)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 := hy0.trans_le hyz
  have hLy := log_pos hy
  have hLz := log_pos (hy.trans_le hyz)
  have hD : 0 < D := mul_pos (pow_pos hy0 _) hLy
  have hR : 0 ≤ R := div_nonneg hD.le (mul_nonneg (pow_nonneg hz0.le _) hLz.le)
  have hR1 : R ≤ 1 := (endpoint_factor_le k hk hy hyz).trans
    ((div_le_iff₀ hz0).mpr (by simpa only [one_mul] using hyz))
  obtain ⟨hi, hab⟩ := finite_power_abel k hy hyz
  obtain ⟨hki, hki_eq⟩ := tail_primitive_integral k hk hy hyz
  have hnorm : D * (∫ u in y..z, tailKernel k u) = 1 - R := by
    rw [hki_eq, mul_sub]
    change D * (1 / D) - D * (1 / (z ^ k * log z)) = 1 - R
    rw [mul_one_div, div_self hD.ne', mul_one_div]
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc y z) :
      (1 - 2 * η) * tailKernel k u ≤ (k : ℝ) * (primeCount u / u ^ (k + 2)) ∧
      (k : ℝ) * (primeCount u / u ^ (k + 2)) ≤ (1 + η) * tailKernel k u := by
    have hu0 := hy0.trans_le hu.1
    have hLu := log_pos (hy.trans_le hu.1)
    let δ : ℝ := 1 / log u
    have hδ : δ ≤ η := (one_div_le_one_div_of_le hLy (log_le_log hy0 hu.1)).trans hlog
    have hδ0 : 0 ≤ δ := div_nonneg zero_le_one hLu.le
    obtain ⟨hl, hh⟩ := abs_le.mp (hπ u hu)
    have hid : primeCount u / u ^ (k + 2) =
        (log u * primeCount u / u) / (u ^ (k + 1) * log u) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ u (k + 1)]
      field_simp [hu0.ne', hLu.ne', pow_ne_zero (k + 1) hu0.ne']
    have hscaled : (k : ℝ) * (primeCount u / u ^ (k + 2)) =
        ((k : ℝ) * (log u * primeCount u / u)) / (u ^ (k + 1) * log u) := by
      rw [hid]
      exact (mul_div_assoc _ _ _).symm
    have hden : 0 < u ^ (k + 1) * log u := mul_pos (pow_pos hu0 _) hLu
    rw [hscaled]
    constructor
    · rw [tailKernel, ← mul_div_assoc (1 - 2 * η)]
      apply div_le_div_of_nonneg_right _ hden.le
      change (1 - 2 * η) * ((k : ℝ) + δ) ≤ (k : ℝ) * (log u * primeCount u / u)
      have hδ' : (1 - 2 * η) * δ ≤ η := by
        exact (mul_le_of_le_one_left hδ0 (by linarith)).trans hδ
      have hkη : η ≤ (k : ℝ) * η := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 hη
      have hp := mul_le_mul_of_nonneg_left
        (show 1 - η ≤ log u * primeCount u / u by linarith only [hl]) hk0.le
      nlinarith only [hδ', hkη, hp]
    · rw [tailKernel, ← mul_div_assoc (1 + η)]
      apply div_le_div_of_nonneg_right _ hden.le
      change (k : ℝ) * (log u * primeCount u / u) ≤ (1 + η) * ((k : ℝ) + δ)
      calc
        _ ≤ (k : ℝ) * (1 + η) := mul_le_mul_of_nonneg_left (by linarith only [hh]) hk0.le
        _ = (1 + η) * (k : ℝ) := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ0) (by linarith)
  have hJlo : (1 - 2 * η) * (1 - R) ≤ J := by
    have h := intervalIntegral.integral_mono_on hyz (hki.const_mul (1 - 2 * η))
      (hi.const_mul (k : ℝ)) (fun u hu => (hpoint u hu).1)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    calc
      _ = D * ((1 - 2 * η) * (∫ u in y..z, tailKernel k u)) := by rw [← hnorm]; ring
      _ ≤ J := mul_le_mul_of_nonneg_left h hD.le
  have hJhi : J ≤ (1 + η) * (1 - R) := by
    have h := intervalIntegral.integral_mono_on hyz (hi.const_mul (k : ℝ))
      (hki.const_mul (1 + η)) (fun u hu => (hpoint u hu).2)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    calc
      J ≤ D * ((1 + η) * (∫ u in y..z, tailKernel k u)) :=
        mul_le_mul_of_nonneg_left h hD.le
      _ = _ := by rw [← hnorm]; ring
  have hJ : |J - (1 - R)| ≤ 2 * η := by
    have hηR := mul_nonneg hη hR
    exact abs_le.mpr ⟨by nlinarith only [hJlo, hηR], by nlinarith only [hJhi, hηR, hη]⟩
  have hbot : D * (primeCount y / y ^ (k + 1)) = log y * primeCount y / y := by
    dsimp only [D]
    rw [pow_succ y k]
    field_simp [hy0.ne', pow_ne_zero k hy0.ne']
  have htop : D * (primeCount z / z ^ (k + 1)) = R * (log z * primeCount z / z) := by
    dsimp only [R]
    rw [pow_succ z k]
    field_simp [hz0.ne', hLz.ne', pow_ne_zero k hz0.ne']
  have hsplit : D * primePowerTail (k + 1) y z = R * (log z * primeCount z / z) -
      log y * primeCount y / y + a * J := by
    have hcoef : a * (k : ℝ) = (k : ℝ) + 1 := by
      dsimp only [a]
      rw [add_mul, one_mul, one_div_mul_cancel hk0.ne']
    have hterm : D * (((k : ℝ) + 1) * I) = a * J := by
      rw [← hcoef]
      dsimp only [J]
      ring
    rw [hab, mul_add, mul_sub, hbot, htop]
    change _ + D * (((k : ℝ) + 1) * I) = _ + a * J
    rw [hterm]
  have he : D * primePowerTail (k + 1) y z - 1 / (k : ℝ) =
      R * (log z * primeCount z / z - 1) - (log y * primeCount y / y - 1) +
        a * (J - (1 - R)) - R / (k : ℝ) := by
    rw [hsplit]
    dsimp only [a]
    ring
  have hRz : |R * (log z * primeCount z / z - 1)| ≤ η := by
    rw [abs_mul, abs_of_nonneg hR]
    calc
      _ ≤ R * η := mul_le_mul_of_nonneg_left (hπ z ⟨hyz, le_rfl⟩) hR
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hR1 hη
      _ = η := one_mul _
  have haJ : |a * (J - (1 - R))| ≤ 4 * η := by
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha2 : a ≤ 2 := by
      dsimp only [a]
      have hh : 1 / (k : ℝ) ≤ 1 := by
        simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hk1
      linarith only [hh]
    rw [abs_mul, abs_of_nonneg ha0]
    calc
      _ ≤ a * (2 * η) := mul_le_mul_of_nonneg_left hJ ha0
      _ ≤ 2 * (2 * η) := mul_le_mul_of_nonneg_right ha2 (by linarith)
      _ = 4 * η := by ring
  have hRk : |R / (k : ℝ)| ≤ R := by
    rw [abs_of_nonneg (div_nonneg hR hk0.le)]
    exact (div_le_iff₀ hk0).mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hk1 hR)
  have hyπ := hπ y ⟨le_rfl, hyz⟩
  let U := R * (log z * primeCount z / z - 1)
  let V := log y * primeCount y / y - 1
  let W := a * (J - (1 - R))
  change |D * primePowerTail (k + 1) y z - 1 / (k : ℝ)| ≤ 6 * η + R
  rw [he]
  change |U - V + W - R / (k : ℝ)| ≤ _
  calc
    _ ≤ |U - V + W| + |R / (k : ℝ)| := abs_sub _ _
    _ ≤ (|U - V| + |W|) + |R / (k : ℝ)| := add_le_add_left (abs_add_le _ _) _
    _ ≤ (|U| + |V| + |W|) + |R / (k : ℝ)| :=
      add_le_add_left (add_le_add_left (abs_sub _ _) _) _
    _ ≤ _ := by
      change |U| ≤ η at hRz
      change |V| ≤ η at hyπ
      change |W| ≤ 4 * η at haJ
      linarith only [hRz, hyπ, haJ, hRk]

private theorem prime_power_tail_uniform (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 < C ∧ ∃ Y : ℝ, 1 < Y ∧ ∀ y z : ℝ, Y ≤ y → C * y ≤ z →
      |y ^ k * log y * primePowerTail (k + 1) y z - 1 / (k : ℝ)| < ε := by
  let η : ℝ := min (ε / 16) (1 / 16)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 16 := min_le_right _ _
  have hηε : η ≤ ε / 16 := min_le_left _ _
  let C : ℝ := 1 / η
  have hC : 1 < C := (lt_div_iff₀ hη).mpr (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (PrimeBoundarySecondOrder.pi_normalized.eventually (Metric.ball_mem_nhds (1 : ℝ) hη))
  let Y : ℝ := max T (exp C)
  have hY : 1 < Y := (one_lt_exp_iff.mpr (show 0 < C by linarith)).trans_le
    (le_max_right _ _)
  refine ⟨C, hC, Y, hY, ?_⟩
  intro y z hy hz
  have hy1 := hY.trans_le hy
  have hy0 : 0 < y := by linarith
  have hyz : y ≤ z :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC.le hy0.le :
      y ≤ C * y).trans hz
  have hz0 := hy0.trans_le hyz
  have hCy : C ≤ log y := by
    simpa only [log_exp] using log_le_log (exp_pos C) ((le_max_right T _).trans hy)
  have hlog : 1 / log y ≤ η := by
    apply (div_le_iff₀ (log_pos hy1)).mpr
    have heq : η * C = 1 := by dsimp [C]; field_simp [hη.ne']
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hCy hη.le
  have hπ (u : ℝ) (hu : u ∈ Set.Icc y z) :
      |log u * primeCount u / u - 1| ≤ η := by
    have ht := hT u ((le_max_left T (exp C)).trans (hy.trans hu.1))
    exact le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)
  have hratio : y / z ≤ η := by
    apply (div_le_iff₀ hz0).mpr
    have hh := mul_le_mul_of_nonneg_left hz hη.le
    have heq : η * (C * y) = y := by dsimp [C]; field_simp [hη.ne']
    rwa [heq] at hh
  have hR := (endpoint_factor_le k hk hy1 hyz).trans hratio
  exact (finite_power_error k hk hy1 hyz hη.le hlog hπ).trans_lt
    (by linarith only [hR, hηε, hε])

/-- The normalized finite tail along real endpoints with diverging ratio. -/
theorem prime_power_tail_tendsto (m : ℕ) (hm : 2 ≤ m)
    {ι : Type*} {l : Filter ι} {y z : ι → ℝ}
    (hy : Tendsto y l atTop) (hz : Tendsto (fun i => z i / y i) l atTop) :
    Tendsto (fun i => y i ^ (m - 1) * log (y i) * primePowerTail m (y i) (z i))
      l (𝓝 (1 / ((m : ℝ) - 1))) := by
  let k := m - 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k + 1 = m := by dsimp [k]; omega
  have hkcast : (k : ℝ) = (m : ℝ) - 1 := by
    dsimp only [k]
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, _, Y, hY, h⟩ := prime_power_tail_uniform k hk ε hε
  filter_upwards [hy.eventually_ge_atTop Y, hz.eventually_ge_atTop C] with i hi hj
  have hy0 : 0 < y i := by linarith
  have hh := h (y i) (z i) hi ((le_div_iff₀ hy0).mp hj)
  rw [hkm, hkcast] at hh
  simpa only [Real.dist_eq] using hh

/-- The fixed layer at the exact prime-prefix price. -/
def activationLayer (m P : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE P, min (prefixPrice P * log (p : ℝ)) (1 / (p : ℝ) ^ m)

private theorem activation_layer_split (m : ℕ) (hm : 2 ≤ m) {P : ℕ} {y : ℝ}
    (hy : 1 < y) (hyP : y ≤ (P : ℝ)) (hprice : 0 < prefixH P * prefixEll P)
    (hroot : y ^ m * log y = prefixH P * prefixEll P) :
    activationLayer m P = (1 / (prefixH P * prefixEll P)) * Chebyshev.theta y +
      primePowerTail m y P := by
  classical
  have hy0 : 0 ≤ y := by linarith
  have hm0 : m ≠ 0 := by omega
  have hfloor : ⌊y⌋₊ ≤ P := by exact_mod_cast (Nat.floor_le hy0).trans hyP
  have hsub := Nat.primesLE_mono hfloor
  have htail : Nat.primesLE P \ Nat.primesLE ⌊y⌋₊ = primeInterval y (P : ℝ) := by
    ext p
    by_cases hp : p.Prime <;>
      simp [primeInterval, Nat.mem_primesLE, hp, not_le, and_comm]
  have hmono : StrictMonoOn (fun u : ℝ => u ^ m * log u) (Set.Ioi 1) := by
    intro a ha b _ hab
    have ha1 : 1 < a := ha
    have ha0 : 0 < a := by linarith
    calc
      a ^ m * log a < b ^ m * log a :=
        mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hab ha0.le hm0) (log_pos ha1)
      _ ≤ b ^ m * log b :=
        mul_le_mul_of_nonneg_left (log_le_log ha0 hab.le) (pow_pos (ha0.trans hab) m).le
  have hbranch (p : ℕ) (hp : p.Prime) :
      log (p : ℝ) / (prefixH P * prefixEll P) ≤ 1 / (p : ℝ) ^ m ↔ (p : ℝ) ≤ y := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    calc
      _ ↔ (p : ℝ) ^ m * log (p : ℝ) ≤ prefixH P * prefixEll P := by
        rw [div_le_div_iff₀ hprice (pow_pos hp0 m), one_mul, mul_comm (log _)]
      _ ↔ _ := by
        rw [← hroot]
        exact hmono.le_iff_le hp1 hy
  unfold activationLayer
  rw [← sum_sdiff hsub, htail, add_comm]
  rw [Chebyshev.theta_eq_sum_primesLE, mul_sum]
  unfold primePowerTail
  congr 1
  · apply sum_congr rfl
    intro p hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
    change min ((1 / (prefixH P * prefixEll P)) * log (p : ℝ)) (1 / (p : ℝ) ^ m) = _
    simp only [one_div_mul_eq_div,
      min_eq_left ((hbranch p hprime).mpr ((Nat.le_floor_iff hy0).mp hle))]
  · apply sum_congr rfl
    intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    have hpy := (Nat.floor_lt hy0).mp (mem_Ioc.mp hpI).1
    change min ((1 / (prefixH P * prefixEll P)) * log (p : ℝ)) (1 / (p : ℝ) ^ m) = _
    rw [one_div_mul_eq_div,
      min_eq_right (le_of_not_ge (fun hh => (not_le_of_gt hpy) ((hbranch p hprime).mp hh)))]

private def cutoffBase (m : ℕ) (H : ℝ) : ℝ := H ^ (1 / (m : ℝ))

private theorem cutoff_exists {m : ℕ} (hm : 2 ≤ m) {H : ℝ} (hH : 1 < H) :
    ∃ t : ℝ, t ∈ Set.Icc (cutoffBase m H) ((m : ℝ) * cutoffBase m H) ∧
      1 < t ∧ t ^ m * log t = H * log H := by
  let b := cutoffBase m H
  have hm0 : m ≠ 0 := by omega
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmR : (0 : ℝ) < m := by linarith
  have hH0 : 0 < H := by linarith
  have hb : 1 < b := one_lt_rpow hH (one_div_pos.mpr hmR)
  have hb0 : 0 < b := by linarith
  have hbb : b ≤ (m : ℝ) * b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hb0.le
  have hbm : b ^ m = H := by
    dsimp only [b, cutoffBase]
    rw [← rpow_mul_natCast hH0.le, one_div_mul_cancel hmR.ne', rpow_one]
  have hLb : log b = (1 / (m : ℝ)) * log H := log_rpow hH0 _
  have hL := log_pos hH
  have hcont : ContinuousOn (fun u : ℝ => u ^ m * log u) (Set.Icc b ((m : ℝ) * b)) :=
    (continuousOn_id.pow m).mul
      (continuousOn_log.mono (fun u hu => (hb0.trans_le hu.1).ne'))
  have hends : H * log H ∈ Set.Icc (b ^ m * log b) (((m : ℝ) * b) ^ m * log ((m : ℝ) * b)) := by
    constructor
    · change b ^ m * log b ≤ H * log H
      rw [hbm, hLb]
      have hfrac : 1 / (m : ℝ) ≤ 1 := by
        simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hm1
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac hL.le) hH0.le
    · change H * log H ≤ ((m : ℝ) * b) ^ m * log ((m : ℝ) * b)
      calc
        H * log H = ((m : ℝ) * H) * log b := by
          rw [hLb]
          field_simp [hmR.ne']
        _ ≤ ((m : ℝ) ^ m * H) * log b :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_self_pow₀ hm1 hm0) hH0.le) (log_pos hb).le
        _ ≤ _ := by
          rw [mul_pow, hbm]
          exact mul_le_mul_of_nonneg_left (log_le_log hb0 hbb)
            (mul_nonneg (pow_nonneg hmR.le m) hH0.le)
  obtain ⟨t, ht, hroot⟩ := intermediate_value_Icc hbb hcont hends
  exact ⟨t, ht, hb.trans_le ht.1, hroot⟩

private def activationCutoffData (m P : ℕ) :
    {t : ℝ // 2 ≤ m → 1 < prefixH P →
      t ∈ Set.Icc (cutoffBase m (prefixH P)) ((m : ℝ) * cutoffBase m (prefixH P)) ∧
      1 < t ∧ t ^ m * log t = prefixH P * prefixEll P} :=
  if h : 2 ≤ m ∧ 1 < prefixH P then
    ⟨Classical.choose (cutoff_exists h.1 h.2),
      fun _ _ => Classical.choose_spec (cutoff_exists h.1 h.2)⟩
  else
    ⟨1, fun hm hH => (h ⟨hm, hH⟩).elim⟩

private def activationCutoff (m P : ℕ) : ℝ := (activationCutoffData m P).val

private theorem activationCutoff_atTop {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (activationCutoff m) atTop atTop := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply tendsto_atTop_mono' atTop _
    ((tendsto_rpow_atTop (one_div_pos.mpr hmR)).comp prefixH_atTop)
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
  exact ((activationCutoffData m P).property hm hH).1.1

private theorem cutoff_log_ratio {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ => log (activationCutoff m P) / prefixEll P)
      atTop (𝓝 (1 / (m : ℝ))) := by
  have h := ((tendsto_log_atTop.comp prefixH_atTop).const_div_atTop (log (m : ℝ))).const_add
    (1 / (m : ℝ))
  simp only [add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
    have hH0 : 0 < prefixH P := by linarith
    have hb0 : 0 < cutoffBase m (prefixH P) := rpow_pos_of_pos hH0 _
    have hL : 0 < prefixEll P := log_pos hH
    have hlow : cutoffBase m (prefixH P) ≤ activationCutoff m P :=
      ((activationCutoffData m P).property hm hH).1.1
    have hl := log_le_log hb0 hlow
    rw [cutoffBase, log_rpow hH0] at hl
    exact (le_div_iff₀ hL).mpr hl
  · filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hH0 : 0 < prefixH P := by linarith
    have hb0 : 0 < cutoffBase m (prefixH P) := rpow_pos_of_pos hH0 _
    have hbounds : activationCutoff m P ∈
        Set.Icc (cutoffBase m (prefixH P)) ((m : ℝ) * cutoffBase m (prefixH P)) :=
      ((activationCutoffData m P).property hm hH).1
    have ht0 := hb0.trans_le hbounds.1
    have hL : 0 < prefixEll P := log_pos hH
    have hu := log_le_log ht0 hbounds.2
    rw [log_mul hmR.ne' hb0.ne', cutoffBase, log_rpow hH0] at hu
    apply (div_le_iff₀ hL).mpr
    change log (activationCutoff m P) ≤ (1 / (m : ℝ) + log (m : ℝ) / prefixEll P) * prefixEll P
    rw [add_mul, div_mul_cancel₀ _ hL.ne']
    exact hu.trans_eq (add_comm _ _)

private theorem cutoff_ratio {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ => activationCutoff m P / cutoffBase m (prefixH P))
      atTop (𝓝 ((m : ℝ) ^ (1 / (m : ℝ)))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h := (cutoff_log_ratio hm).inv₀ (one_div_ne_zero hmR.ne')
  have hinv : Tendsto (fun P : ℕ => prefixEll P / log (activationCutoff m P))
      atTop (𝓝 (m : ℝ)) := by
    simpa only [Pi.inv_apply, inv_div, one_div, inv_inv] using h
  have hcont := continuousAt_rpow_const (m : ℝ) (1 / (m : ℝ)) (Or.inl hmR.ne')
  apply (hcont.tendsto.comp hinv).congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
  let b := cutoffBase m (prefixH P)
  let t := activationCutoff m P
  have hH0 : 0 < prefixH P := by linarith
  have ht : 1 < t := ((activationCutoffData m P).property hm hH).2.1
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := rpow_pos_of_pos hH0 _
  have hLt := log_pos ht
  have hb_pow : b ^ m = prefixH P := by
    dsimp only [b, cutoffBase]
    rw [← rpow_mul_natCast hH0.le, one_div_mul_cancel hmR.ne', rpow_one]
  have he : (t / b) ^ m = prefixEll P / log t := by
    rw [div_pow, hb_pow]
    apply (div_eq_div_iff hH0.ne' hLt.ne').mpr
    rw [mul_comm (prefixEll P)]
    exact ((activationCutoffData m P).property hm hH).2.2
  change (prefixEll P / log t) ^ (1 / (m : ℝ)) = t / b
  rw [← he, ← rpow_natCast_mul (div_nonneg ht0.le hb0.le) m (1 / (m : ℝ)),
    mul_one_div, div_self hmR.ne', rpow_one]

private theorem cutoff_endpoint_ratio {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ => (P : ℝ) / activationCutoff m P) atTop atTop := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hq : 0 < ((m : ℝ) - 1) / (m : ℝ) := div_pos (by linarith) hmR
  have hc : 0 < (m : ℝ) ^ (1 / (m : ℝ)) := rpow_pos_of_pos hmR _
  have hPH : Tendsto (fun P : ℕ => (P : ℝ) / prefixH P) atTop (𝓝 1) := by
    simpa only [Pi.inv_apply, inv_div, inv_one] using prefix_H_ratio.inv₀ one_ne_zero
  have h := Tendsto.pos_mul_atTop (div_pos zero_lt_one hc) (hPH.div (cutoff_ratio hm) hc.ne')
    ((tendsto_rpow_atTop hq).comp prefixH_atTop)
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
  let H := prefixH P
  let t := activationCutoff m P
  let b := cutoffBase m H
  have hH0 : 0 < H := by dsimp [H]; linarith
  have hb0 : 0 < b := rpow_pos_of_pos hH0 _
  have ht0 : 0 < t := zero_lt_one.trans ((activationCutoffData m P).property hm hH).2.1
  have hmul : b * H ^ (((m : ℝ) - 1) / (m : ℝ)) = H := by
    dsimp only [b, cutoffBase]
    rw [← rpow_add hH0, ← add_div, show 1 + ((m : ℝ) - 1) = m by ring,
      div_self hmR.ne', rpow_one]
  change ((P : ℝ) / H) / (t / b) * H ^ (((m : ℝ) - 1) / (m : ℝ)) = (P : ℝ) / t
  calc
    _ = ((P : ℝ) / t) * ((b * H ^ (((m : ℝ) - 1) / (m : ℝ))) / H) := by
      field_simp [hH0.ne', ht0.ne', hb0.ne']
    _ = _ := by rw [hmul, div_self hH0.ne', mul_one]

/-- The asymptotic constant of the fixed clipped layer over the actual prime prefix. -/
theorem activation_layer_tendsto (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ =>
      prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P * activationLayer m P)
      atTop (𝓝 (((m : ℝ) / ((m : ℝ) - 1)) * (m : ℝ) ^ (1 / (m : ℝ)))) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have htail := prime_power_tail_tendsto m hm (activationCutoff_atTop hm) (cutoff_endpoint_ratio hm)
  have hhead := EulerLayerRootCorrection.prime_number_limits.2.comp (activationCutoff_atTop hm)
  have h := (cutoff_ratio hm).mul (hhead.add htail)
  have hc : (m : ℝ) ^ (1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) - 1)) =
      ((m : ℝ) / ((m : ℝ) - 1)) * (m : ℝ) ^ (1 / (m : ℝ)) := by
    field_simp [hm1]
    ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1,
    (cutoff_endpoint_ratio hm).eventually_ge_atTop 1] with P hH hPt
  let t := activationCutoff m P
  let H := prefixH P
  let L := prefixEll P
  let b := cutoffBase m H
  have hH0 : 0 < H := by dsimp [H]; linarith
  have ht : 1 < t := ((activationCutoffData m P).property hm hH).2.1
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hL : 0 < L := log_pos hH
  have hb : 0 < b := rpow_pos_of_pos hH0 _
  have htP : t ≤ (P : ℝ) := by simpa only [one_mul] using (le_div_iff₀ ht0).mp hPt
  have hroot : t ^ m * log t = H * L := ((activationCutoffData m P).property hm hH).2.2
  have hscale : H ^ (((m : ℝ) - 1) / (m : ℝ)) * L = (H * L) / b := by
    apply (eq_div_iff hb.ne').mpr
    rw [mul_right_comm, mul_comm (H ^ (((m : ℝ) - 1) / (m : ℝ))) b]
    dsimp only [b, cutoffBase]
    rw [← rpow_add hH0, ← add_div, show 1 + ((m : ℝ) - 1) = m by ring,
      div_self hm0, rpow_one]
  have hhead_eq : ((H * L) / b) * ((1 / (H * L)) * Chebyshev.theta t) =
      t / b * (Chebyshev.theta t / t) := by
    field_simp [hH0.ne', hL.ne', hb.ne', ht0.ne']
  have htail_eq : ((H * L) / b) * primePowerTail m t P =
      t / b * (t ^ (m - 1) * log t * primePowerTail m t P) := by
    have hpow : t ^ m = t ^ (m - 1) * t := by
      calc
        t ^ m = t ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = _ := pow_succ _ _
    rw [← hroot, hpow]
    ring
  change t / b * (Chebyshev.theta t / t + t ^ (m - 1) * log t * primePowerTail m t P) =
    H ^ (((m : ℝ) - 1) / (m : ℝ)) * L * activationLayer m P
  rw [activation_layer_split m hm ht htP (mul_pos hH0 hL) hroot, hscale,
    mul_add, mul_add, hhead_eq, htail_eq]

end D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
