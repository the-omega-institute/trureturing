/- GID: D5/S3/Arith/Robin/PriceRecord/CubicActivationResidual
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CubicActivationResidual
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: The cubic activation residual of the complete integer Robin infimum on prime prefixes. -/

import D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder

/-!
# Cubic activation residual on prime prefixes

The second activation splits at the real cubic-log cutoff. Finite Abel
summation and the prime number theorem give the normalized cubic tail.
The integer activation envelope then transfers the limit to the exact
residual of the full integer infimum after first activation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual

open Real Filter MeasureTheory Finset Asymptotics
open scoped Topology BigOperators Chebyshev
open QuantitativePrimeAbel RealInfimumPrimeBoundary FixedSupportIntegerActivationEnvelope

private def cubicSum (y z : ℝ) : ℝ :=
  ∑ p ∈ primeInterval y z, 1 / (p : ℝ) ^ 3

private theorem finite_cubic_abel {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    IntervalIntegrable (fun u => primeCount u / u ^ 4) volume y z ∧
    cubicSum y z = primeCount z / z ^ 3 - primeCount y / y ^ 3 +
      3 * (∫ u in y..z, primeCount u / u ^ 4) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  let f : ℝ → ℝ := fun u => 1 / u ^ 3
  have hy0 : 0 < y := by linarith
  have hc (u : ℝ) : (∑ p ∈ Icc 0 ⌊u⌋₊, c p) = primeCount u := by
    rw [primeCount, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
    simp only [c, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hd (u : ℝ) (hu : u ∈ Set.Icc y z) : HasDerivAt f (-3 / u ^ 4) u := by
    have hu0 := (hy0.trans_le hu.1).ne'
    change HasDerivAt (fun v : ℝ => 1 / v ^ 3) (-3 / u ^ 4) u
    convert (hasDerivAt_const u (1 : ℝ)).fun_div ((hasDerivAt_id u).pow 3)
      (pow_ne_zero 3 hu0) using 1
    all_goals dsimp [f]
    all_goals field_simp [hu0]
    all_goals ring
  have hf : IntegrableOn (deriv f) (Set.Icc y z) := by
    have hcont : ContinuousOn (fun u : ℝ => -3 / u ^ 4) (Set.Icc y z) :=
      continuousOn_const.div (continuousOn_id.pow 4)
        (fun u hu => pow_ne_zero _ (hy0.trans_le hu.1).ne')
    exact hcont.integrableOn_Icc.congr_fun (fun u hu => (hd u hu).deriv.symm)
      measurableSet_Icc
  have hs : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) = cubicSum y z := by
    simp only [cubicSum, primeInterval, sum_filter, c, f, mul_ite, mul_one, mul_zero]
  have ha := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun u hu => (hd u hu).differentiableAt) hf
  simp_rw [hc] at ha
  rw [hs, ← intervalIntegral.integral_of_le hyz] at ha
  have hprod : IntervalIntegrable (fun u => deriv f u * primeCount u) volume y z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr (by
      simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hf (m := 0))
  have heq (u : ℝ) (hu : u ∈ Set.Icc y z) :
      deriv f u * primeCount u = -3 * (primeCount u / u ^ 4) := by
    rw [(hd u hu).deriv]
    ring
  have hi : IntervalIntegrable (fun u => primeCount u / u ^ 4) volume y z := by
    refine (hprod.const_mul (-1 / 3 : ℝ)).congr ?_
    intro u hu
    rw [Set.uIoc_of_le hyz] at hu
    change (-1 / 3 : ℝ) * (deriv f u * primeCount u) = primeCount u / u ^ 4
    rw [heq u ⟨hu.1.le, hu.2⟩]
    ring
  have hI : (∫ u in y..z, deriv f u * primeCount u) =
      -3 * (∫ u in y..z, primeCount u / u ^ 4) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hyz]
    exact heq
  rw [hI] at ha
  refine ⟨hi, ?_⟩
  rw [ha]
  dsimp [f]
  ring

private def cubicPrimitive (u : ℝ) : ℝ := 1 / (u ^ 2 * log u)

private def cubicKernel (u : ℝ) : ℝ :=
  (2 + 1 / log u) / (u ^ 3 * log u)

private theorem cubic_primitive_integral {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    IntervalIntegrable cubicKernel volume y z ∧
    (∫ u in y..z, cubicKernel u) = cubicPrimitive y - cubicPrimitive z := by
  have hd (u : ℝ) (hu : u ∈ Set.Icc y z) :
      HasDerivAt cubicPrimitive (-cubicKernel u) u := by
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hlog := (log_pos (hy.trans_le hu.1)).ne'
    change HasDerivAt (fun v : ℝ => 1 / (v ^ 2 * log v)) (-cubicKernel u) u
    convert (hasDerivAt_const u (1 : ℝ)).fun_div
      (((hasDerivAt_id u).pow 2).mul (hasDerivAt_log hu0))
      (mul_ne_zero (pow_ne_zero 2 hu0) hlog) using 1
    all_goals dsimp [cubicKernel]
    all_goals field_simp [hu0, hlog]
    all_goals ring
  have hi : IntervalIntegrable cubicKernel volume y z := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hyz
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hlog := (log_pos (hy.trans_le hu.1)).ne'
    have hl := (hasDerivAt_log hu0).continuousAt
    exact ((continuousAt_const.add (continuousAt_const.div hl hlog)).div
      ((continuousAt_id.pow 3).mul hl) (mul_ne_zero (pow_ne_zero 3 hu0) hlog)
      ).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := cubicPrimitive) (f' := fun u => -cubicKernel u) (a := y) (b := z)
    (fun u hu => hd u (by simpa only [Set.uIcc_of_le hyz] using hu)) hi.neg
  rw [intervalIntegral.integral_neg] at h
  exact ⟨hi, by linarith only [h]⟩

/-- The comparison uses a single prime-counting tolerance throughout the
finite interval. The endpoint term retains the exact ratio of primitives. -/
private theorem finite_cubic_error {y z η : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4) (hlog : 1 / log y ≤ η)
    (hπ : ∀ u ∈ Set.Icc y z, |log u * primeCount u / u - 1| ≤ η) :
    |y ^ 2 * log y * cubicSum y z - 1 / 2| ≤
      4 * η + 2 * (y ^ 2 * log y / (z ^ 2 * log z)) := by
  let D : ℝ := y ^ 2 * log y
  let R : ℝ := D / (z ^ 2 * log z)
  let I : ℝ := ∫ u in y..z, primeCount u / u ^ 4
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := hy0.trans_le hyz
  have hLy := log_pos hy
  have hLz := log_pos (hy.trans_le hyz)
  have hD : 0 < D := mul_pos (pow_pos hy0 _) hLy
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (pow_pos hz0 2) hLz)).mpr
    rw [one_mul]
    exact mul_le_mul (pow_le_pow_left₀ hy0.le hyz _) (log_le_log hy0 hyz)
      hLy.le (sq_nonneg z)
  obtain ⟨hi, ha⟩ := finite_cubic_abel hy hyz
  obtain ⟨hki, hk⟩ := cubic_primitive_integral hy hyz
  have hnorm : D * (∫ u in y..z, cubicKernel u) = 1 - R := by
    rw [hk]
    dsimp [D, R, cubicPrimitive]
    field_simp [hy0.ne', hz0.ne', hLy.ne', hLz.ne']
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc y z) :
      (1 / 2 - η) * cubicKernel u ≤ primeCount u / u ^ 4 ∧
      primeCount u / u ^ 4 ≤ ((1 + η) / 2) * cubicKernel u := by
    have hu0 := hy0.trans_le hu.1
    have hLu := log_pos (hy.trans_le hu.1)
    have hδ : 1 / log u ≤ η :=
      (one_div_le_one_div_of_le hLy (log_le_log hy0 hu.1)).trans hlog
    have hδ0 : 0 ≤ 1 / log u := by positivity
    obtain ⟨hl, hh⟩ := abs_le.mp (hπ u hu)
    have hid : primeCount u / u ^ 4 =
        (log u * primeCount u / u) / (u ^ 3 * log u) := by
      field_simp [hu0.ne', hLu.ne']
    have hden : 0 < u ^ 3 * log u := mul_pos (pow_pos hu0 _) hLu
    rw [hid]
    constructor
    · rw [cubicKernel, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hden.le
      have hb : (1 / 2 - η) * (2 + 1 / log u) ≤ (1 / 2 - η) * (2 + η) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hδ 2) (by linarith)
      nlinarith only [hb, hl, hη, sq_nonneg η]
    · rw [cubicKernel, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hden.le
      have hb : ((1 + η) / 2) * 2 ≤ ((1 + η) / 2) * (2 + 1 / log u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith only [hh, hb]
  have hIlo : (1 / 2 - η) * (1 - R) ≤ D * I := by
    have h := intervalIntegral.integral_mono_on hyz (hki.const_mul (1 / 2 - η)) hi
      (fun u hu => (hpoint u hu).1)
    rw [intervalIntegral.integral_const_mul] at h
    calc
      _ = D * ((1 / 2 - η) * (∫ u in y..z, cubicKernel u)) := by rw [← hnorm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hD.le
  have hIhi : D * I ≤ ((1 + η) / 2) * (1 - R) := by
    have h := intervalIntegral.integral_mono_on hyz hi (hki.const_mul ((1 + η) / 2))
      (fun u hu => (hpoint u hu).2)
    rw [intervalIntegral.integral_const_mul] at h
    calc
      _ ≤ D * (((1 + η) / 2) * (∫ u in y..z, cubicKernel u)) :=
        mul_le_mul_of_nonneg_left h hD.le
      _ = _ := by rw [← hnorm]; ring
  have hbot : D * (primeCount y / y ^ 3) = log y * primeCount y / y := by
    dsimp [D]
    field_simp [hy0.ne']
  have htop : D * (primeCount z / z ^ 3) = R * (log z * primeCount z / z) := by
    dsimp [R]
    field_simp [hz0.ne', hLz.ne']
  obtain ⟨hylo, hyhi⟩ := abs_le.mp (hπ y ⟨le_rfl, hyz⟩)
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp (hπ z ⟨hyz, le_rfl⟩)
  have htop0 : 0 ≤ R * (log z * primeCount z / z) :=
    mul_nonneg hR (by linarith)
  have htop2 : R * (log z * primeCount z / z) ≤ 2 * R := by
    simpa only [mul_comm R (2 : ℝ)] using
      mul_le_mul_of_nonneg_left (show log z * primeCount z / z ≤ 2 by linarith) hR
  have hsplit : D * cubicSum y z = R * (log z * primeCount z / z) -
      log y * primeCount y / y + 3 * (D * I) := by
    rw [ha, mul_add, mul_sub, hbot, htop]
    dsimp only [I]
    ring
  change |D * cubicSum y z - 1 / 2| ≤ 4 * η + 2 * R
  rw [hsplit]
  have hηR := mul_nonneg hη hR
  exact abs_le.mpr ⟨by nlinarith only [hIlo, hyhi, htop0, hηR, hR],
    by nlinarith only [hIhi, hylo, htop2, hηR, hR, hη]⟩

/-- The strict lower and inclusive upper cutoff are both real. -/
private theorem prime_cubic_tail_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 < C ∧ ∃ Y : ℝ, 1 < Y ∧ ∀ y z : ℝ, Y ≤ y → C * y ≤ z →
      |y ^ 2 * log y * cubicSum y z - 1 / 2| < ε := by
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
  have hR : y ^ 2 * log y / (z ^ 2 * log z) ≤ η := by
    have hy_le : y ≤ η * z := by
      have hh := mul_le_mul_of_nonneg_left hz hη.le
      have heq : η * (C * y) = y := by dsimp [C]; field_simp [hη.ne']
      rwa [heq] at hh
    apply (div_le_iff₀ (mul_pos (pow_pos hz0 _) (log_pos (hy1.trans_le hyz)))).mpr
    calc
      _ = y * (y * log y) := by ring
      _ ≤ (η * z) * (z * log z) :=
        mul_le_mul hy_le (mul_le_mul hyz (log_le_log hy0 hyz)
          (log_pos hy1).le hz0.le) (mul_nonneg hy0.le (log_pos hy1).le)
          (mul_nonneg hη.le hz0.le)
      _ = _ := by ring
  exact (finite_cubic_error hy1 hyz hη.le (by linarith) hlog hπ).trans_lt
    (by linarith only [hR, hηε, hε])

/-- Finite cubic tail along moving endpoints with diverging endpoint ratio. -/
private theorem prime_cubic_tail_tendsto {ι : Type*} {l : Filter ι} {y z : ι → ℝ}
    (hy : Tendsto y l atTop) (hz : Tendsto (fun i => z i / y i) l atTop) :
    Tendsto (fun i => y i ^ 2 * log (y i) * cubicSum (y i) (z i)) l (𝓝 (1 / 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, _, Y, hY, h⟩ := prime_cubic_tail_uniform ε hε
  filter_upwards [hy.eventually_ge_atTop Y, hz.eventually_ge_atTop C] with i hi hj
  have hy0 : 0 < y i := by linarith
  simpa only [Real.dist_eq] using h (y i) (z i) hi ((le_div_iff₀ hy0).mp hj)

private theorem prefix_price_eq (P : ℕ) :
    prefixPrice P = 1 / (prefixH P * prefixEll P) := rfl

private theorem prefix_ell_atTop : Tendsto prefixEll atTop atTop :=
  tendsto_log_atTop.comp prefixH_atTop

private theorem eventually_prefix_large :
    ∀ᶠ P : ℕ in atTop, exp 1 < prefixH P ∧ 1 < prefixEll P := by
  filter_upwards [prefixH_atTop.eventually_gt_atTop (exp 1),
    prefix_ell_atTop.eventually_gt_atTop 1] with P hH hL
  exact ⟨hH, hL⟩

private theorem prefix_P_div_H :
    Tendsto (fun P : ℕ => (P : ℝ) / prefixH P) atTop (𝓝 1) := by
  simpa only [Pi.inv_apply, inv_div, inv_one] using prefix_H_ratio.inv₀ one_ne_zero

private theorem prefix_partition {P : ℕ} {y : ℝ} (hy : 0 ≤ y) (hyP : y ≤ (P : ℝ)) :
    Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE P ∧
    Nat.primesLE P \ Nat.primesLE ⌊y⌋₊ = primeInterval y (P : ℝ) := by
  classical
  have hfloor : ⌊y⌋₊ ≤ P := by exact_mod_cast (Nat.floor_le hy).trans hyP
  refine ⟨Nat.primesLE_mono hfloor, ?_⟩
  ext p
  by_cases hp : p.Prime <;>
    simp [primeInterval, Nat.mem_primesLE, hp, not_le, and_comm]

private theorem second_activation_split {P : ℕ} {y H : ℝ} (hy : 1 < y)
    (hyP : y ≤ (P : ℝ)) (hH : 0 < H)
    (hroot : y ^ 3 * log y = H) :
    secondActivationSum (Nat.primesLE P) (1 / H) =
      (1 / H) * Chebyshev.theta y + cubicSum y P := by
  classical
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨hsub, htail⟩ := prefix_partition hy0 hyP
  have hbranch (p : ℕ) (hp : p.Prime) :
      1 / H * log (p : ℝ) ≤ 1 / (p : ℝ) ^ 3 ↔ (p : ℝ) ≤ y := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hmono : StrictMonoOn (fun u : ℝ => u ^ 3 * log u) (Set.Ioi 1) := by
      intro a ha b _ hab
      have ha1 : 1 < a := ha
      have ha0 : 0 < a := by linarith
      calc
        a ^ 3 * log a < b ^ 3 * log a :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hab ha0.le (by norm_num)) (log_pos ha1)
        _ ≤ b ^ 3 * log b :=
          mul_le_mul_of_nonneg_left (log_le_log ha0 hab.le) (pow_pos (ha0.trans hab) 3).le
    calc
      _ ↔ (p : ℝ) ^ 3 * log (p : ℝ) ≤ H := by
        rw [one_div_mul_eq_div, div_le_div_iff₀ hH (pow_pos hp0 3), one_mul, mul_comm (log _)]
      _ ↔ _ := by
        rw [← hroot]
        exact hmono.le_iff_le hp1 hy
  unfold secondActivationSum
  rw [← sum_sdiff hsub, htail, add_comm]
  rw [Chebyshev.theta_eq_sum_primesLE, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro p hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
    rw [min_eq_left ((hbranch p hprime).mpr ((Nat.le_floor_iff hy0).mp hle))]
  · apply sum_congr rfl
    intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    have hpy := (Nat.floor_lt hy0).mp (mem_Ioc.mp hpI).1
    rw [min_eq_right (le_of_not_ge (fun hh => (not_le_of_gt hpy) ((hbranch p hprime).mp hh)))]

private theorem cube_rpow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← rpow_mul_natCast hx]
  norm_num

private theorem cubic_root_exists {H : ℝ} (hH : 1 < H) :
    ∃ t : ℝ, t ∈ Set.Icc (H ^ (1 / 3 : ℝ)) (2 * H ^ (1 / 3 : ℝ)) ∧
      t ^ 3 * log t = H * log H := by
  let b : ℝ := H ^ (1 / 3 : ℝ)
  have hH0 : 0 < H := by linarith
  have hb : 1 < b := one_lt_rpow hH (by norm_num)
  have hb0 : 0 < b := by linarith
  have hbb : b ≤ 2 * b := by linarith
  have hb3 : b ^ 3 = H := cube_rpow hH0.le
  have hLb : log b = (1 / 3 : ℝ) * log H := log_rpow hH0 _
  have hL := log_pos hH
  have hcont : ContinuousOn (fun u : ℝ => u ^ 3 * log u) (Set.Icc b (2 * b)) := by
    exact (continuousOn_id.pow 3).mul
      (continuousOn_log.mono (fun u hu => (hb0.trans_le hu.1).ne'))
  have hm : H * log H ∈ Set.Icc (b ^ 3 * log b) ((2 * b) ^ 3 * log (2 * b)) := by
    constructor
    · rw [hb3, hLb]
      nlinarith only [mul_pos hH0 hL]
    · have hL2 : log (2 * b) = log 2 + log b := log_mul (by norm_num) hb0.ne'
      rw [hL2, hLb, mul_pow, hb3]
      nlinarith only [mul_pos hH0 hL,
        mul_nonneg hH0.le (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  exact intermediate_value_Icc hbb hcont hm

private def cubicCutoff (P : ℕ) : ℝ :=
  if h : 1 < prefixH P then Classical.choose (cubic_root_exists h) else 1

private theorem cubicCutoff_spec {P : ℕ} (h : 1 < prefixH P) :
    cubicCutoff P ∈ Set.Icc ((prefixH P) ^ (1 / 3 : ℝ))
      (2 * (prefixH P) ^ (1 / 3 : ℝ)) ∧
    cubicCutoff P ^ 3 * log (cubicCutoff P) = prefixH P * prefixEll P := by
  simpa only [cubicCutoff, dite_eq_left h, prefixEll] using
    Classical.choose_spec (cubic_root_exists h)

private theorem eventually_H_gt_one : ∀ᶠ P : ℕ in atTop, 1 < prefixH P :=
  prefixH_atTop.eventually_gt_atTop 1

private theorem cubicCutoff_atTop : Tendsto cubicCutoff atTop atTop := by
  apply tendsto_atTop_mono' atTop _ ((tendsto_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 3)).comp prefixH_atTop)
  filter_upwards [eventually_H_gt_one] with P h
  exact (cubicCutoff_spec h).1.1

private theorem cubic_log_ratio :
    Tendsto (fun P : ℕ => log (cubicCutoff P) / prefixEll P) atTop (𝓝 (1 / 3)) := by
  have h := (prefix_ell_atTop.const_div_atTop (log 2)).const_add (1 / 3 : ℝ)
  simp only [add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards [eventually_H_gt_one] with P hH
    have h0 : 0 < prefixH P := by linarith
    have hb0 : 0 < prefixH P ^ (1 / 3 : ℝ) := rpow_pos_of_pos h0 _
    have hL : 0 < prefixEll P := log_pos hH
    have hl := log_le_log hb0 (cubicCutoff_spec hH).1.1
    rw [log_rpow h0] at hl
    exact (le_div_iff₀ hL).mpr hl
  · filter_upwards [eventually_H_gt_one] with P hH
    have h0 : 0 < prefixH P := by linarith
    have hb0 : 0 < prefixH P ^ (1 / 3 : ℝ) := rpow_pos_of_pos h0 _
    have ht0 := hb0.trans_le (cubicCutoff_spec hH).1.1
    have hL : 0 < prefixEll P := log_pos hH
    have hu := log_le_log ht0 (cubicCutoff_spec hH).1.2
    rw [log_mul (by norm_num) hb0.ne', log_rpow h0] at hu
    apply (div_le_iff₀ hL).mpr
    change log (cubicCutoff P) ≤ (1 / 3 + log 2 / prefixEll P) * prefixEll P
    rw [add_mul, div_mul_cancel₀ _ hL.ne']
    change log (cubicCutoff P) ≤ (1 / 3 : ℝ) * log (prefixH P) + log 2
    linarith only [hu]

private theorem cubic_cutoff_ratio :
    Tendsto (fun P : ℕ => cubicCutoff P / prefixH P ^ (1 / 3 : ℝ)) atTop
      (𝓝 ((3 : ℝ) ^ (1 / 3 : ℝ))) := by
  have h := cubic_log_ratio.inv₀ (by norm_num : (1 / 3 : ℝ) ≠ 0)
  have h3 : Tendsto (fun P : ℕ => prefixEll P / log (cubicCutoff P)) atTop (𝓝 3) := by
    simpa only [Pi.inv_apply, inv_div, one_div, inv_inv] using h
  have hcont := continuousAt_rpow_const (3 : ℝ) (1 / 3 : ℝ) (Or.inr (by norm_num))
  apply (hcont.tendsto.comp h3).congr'
  filter_upwards [eventually_H_gt_one] with P hH
  let b : ℝ := prefixH P ^ (1 / 3 : ℝ)
  let t : ℝ := cubicCutoff P
  have hH0 : 0 < prefixH P := by linarith
  have hb : 1 < b := one_lt_rpow hH (by norm_num)
  have ht : 1 < t := hb.trans_le (cubicCutoff_spec hH).1.1
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := by linarith
  have hLt := log_pos ht
  have he : (t / b) ^ 3 = prefixEll P / log t := by
    rw [div_pow, show b ^ 3 = prefixH P from cube_rpow hH0.le]
    apply (div_eq_div_iff hH0.ne' hLt.ne').mpr
    simpa only [mul_comm (prefixEll P)] using (cubicCutoff_spec hH).2
  change (prefixEll P / log t) ^ (1 / 3 : ℝ) = t / b
  rw [← he, ← rpow_natCast_mul (div_nonneg ht0.le hb0.le) 3 (1 / 3 : ℝ)]
  norm_num

private theorem cubic_endpoint_ratio :
    Tendsto (fun P : ℕ => (P : ℝ) / cubicCutoff P) atTop atTop := by
  have hc : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hquot := prefix_P_div_H.div cubic_cutoff_ratio hc.ne'
  have h := Tendsto.pos_mul_atTop (div_pos (by norm_num) hc) hquot
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp prefixH_atTop)
  apply h.congr'
  filter_upwards [eventually_H_gt_one] with P hH
  have hH0 : 0 < prefixH P := by linarith
  have ht : 1 < cubicCutoff P :=
    (one_lt_rpow hH (by norm_num : (0 : ℝ) < 1 / 3)).trans_le (cubicCutoff_spec hH).1.1
  have hmul : prefixH P ^ (1 / 3 : ℝ) * prefixH P ^ (2 / 3 : ℝ) = prefixH P := by
    rw [← rpow_add hH0]
    norm_num
  change ((P : ℝ) / prefixH P) / (cubicCutoff P / prefixH P ^ (1 / 3 : ℝ)) *
    prefixH P ^ (2 / 3 : ℝ) = (P : ℝ) / cubicCutoff P
  calc
    _ = ((P : ℝ) / cubicCutoff P) *
        ((prefixH P ^ (1 / 3 : ℝ) * prefixH P ^ (2 / 3 : ℝ)) / prefixH P) := by
      field_simp [hH0.ne', show cubicCutoff P ≠ 0 by linarith,
        (rpow_pos_of_pos hH0 (1 / 3 : ℝ)).ne']
    _ = _ := by rw [hmul, div_self hH0.ne', mul_one]

private def cubicScale (P : ℕ) : ℝ := prefixH P ^ (2 / 3 : ℝ) * prefixEll P

private theorem second_activation_cubic_limit :
    Tendsto (fun P : ℕ => cubicScale P * secondActivationSum (Nat.primesLE P) (prefixPrice P))
      atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ))) := by
  have htail := prime_cubic_tail_tendsto cubicCutoff_atTop cubic_endpoint_ratio
  have hhead := EulerLayerRootCorrection.prime_number_limits.2.comp cubicCutoff_atTop
  have h := cubic_cutoff_ratio.mul (hhead.add htail)
  have hc : (3 : ℝ) ^ (1 / 3 : ℝ) * (1 + 1 / 2) =
      (3 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_H_gt_one, cubic_endpoint_ratio.eventually_ge_atTop 1] with P hH hP
  let t := cubicCutoff P
  let H := prefixH P
  let L := prefixEll P
  have hH0 : 0 < H := by dsimp [H]; linarith
  have ht : 1 < t :=
    (one_lt_rpow hH (by norm_num : (0 : ℝ) < 1 / 3)).trans_le (cubicCutoff_spec hH).1.1
  have ht0 : 0 < t := by linarith
  have hL : 0 < L := log_pos hH
  have htP : t ≤ (P : ℝ) := by simpa only [one_mul] using (le_div_iff₀ ht0).mp hP
  have hroot : t ^ 3 * log t = H * L := (cubicCutoff_spec hH).2
  have hb : 0 < H ^ (1 / 3 : ℝ) := rpow_pos_of_pos hH0 _
  have hmul : H ^ (2 / 3 : ℝ) * H ^ (1 / 3 : ℝ) = H := by
    rw [← rpow_add hH0]
    norm_num
  have hscale : cubicScale P = t ^ 3 * log t / H ^ (1 / 3 : ℝ) := by
    rw [hroot, eq_div_iff hb.ne']
    change H ^ (2 / 3 : ℝ) * L * H ^ (1 / 3 : ℝ) = H * L
    rw [mul_right_comm, hmul]
  change t / H ^ (1 / 3 : ℝ) *
    (Chebyshev.theta t / t + t ^ 2 * log t * cubicSum t P) =
      cubicScale P * secondActivationSum (Nat.primesLE P) (prefixPrice P)
  rw [prefix_price_eq, second_activation_split ht htP (mul_pos hH0 hL) hroot]
  have hhead_eq : cubicScale P * (1 / (H * L) * Chebyshev.theta t) =
      Chebyshev.theta t / H ^ (1 / 3 : ℝ) := by
    change H ^ (2 / 3 : ℝ) * L * (1 / (H * L) * Chebyshev.theta t) = _
    calc
      _ = H ^ (2 / 3 : ℝ) * Chebyshev.theta t / H := by
        field_simp [hH0.ne', hL.ne']
      _ = _ := by
        apply (div_eq_div_iff hH0.ne' hb.ne').mpr
        rw [mul_right_comm, hmul, mul_comm H]
  rw [mul_add, mul_add, hhead_eq, hscale]
  field_simp [ht0.ne', hb.ne']

private def envelopeRadius (P : ℕ) : ℝ := 1 / sqrt (prefixH P)

private def envelopeCutoff (P : ℕ) : ℝ := prefixH P ^ (1 / 4 : ℝ)

private def lowerError (P : ℕ) : ℝ :=
  2 * prefixPrice P * log (1 / prefixPrice P) + 16 * prefixEll P * envelopeRadius P ^ 2

private def upperError (P : ℕ) : ℝ :=
  prefixPrice P * envelopeCutoff P * (log (1 / prefixPrice P) + 1) +
    4 / envelopeCutoff P ^ 3

private theorem infimum_lt_radius :
    ∀ᶠ P : ℕ in atTop, integerInfimum (Nat.primesLE P) < envelopeRadius P := by
  have h := IntegerInfimumSecondOrder.actual_integer_infimum_second_order.div_atTop
    prefix_ell_atTop
  have hfirst : Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixEll P *
      integerInfimum (Nat.primesLE P)) atTop (𝓝 (2 * sqrt 2)) := by
    have h' := h.add_const (2 * sqrt 2)
    rw [zero_add] at h'
    apply h'.congr'
    filter_upwards [prefix_ell_atTop.eventually_gt_atTop 0] with P hL
    rw [mul_div_cancel_left₀ _ hL.ne']
    ring
  have hsmall : Tendsto (fun P : ℕ => sqrt (prefixH P) *
      integerInfimum (Nat.primesLE P)) atTop (𝓝 0) := by
    apply (hfirst.div_atTop prefix_ell_atTop).congr'
    filter_upwards [prefix_ell_atTop.eventually_gt_atTop 0] with P hL
    field_simp [hL.ne']
  filter_upwards [hsmall.eventually_lt_const zero_lt_one, eventually_H_gt_one] with P hlt hH
  have hs : 0 < sqrt (prefixH P) := sqrt_pos.mpr (by linarith)
  exact (lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using hlt)

private theorem prefix_log_power_small {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun P : ℕ => prefixEll P ^ k / prefixH P ^ a) atTop (𝓝 0) := by
  simpa only [Function.comp_def, prefixEll, rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).tendsto_div_nhds_zero.comp prefixH_atTop)

private theorem radius_condition :
    ∀ᶠ P : ℕ in atTop, 2 * prefixEll P * envelopeRadius P ≤ 1 := by
  have h : Tendsto (fun P : ℕ => 2 * prefixEll P * envelopeRadius P) atTop (𝓝 0) := by
    have hsmall := (prefix_log_power_small (by norm_num : (0 : ℝ) < 1 / 2) 1).const_mul 2
    simpa only [pow_one, envelopeRadius, sqrt_eq_rpow, div_eq_mul_inv, one_mul,
      mul_zero, mul_assoc] using hsmall
  exact (h.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono (fun _ hi => hi.le)

private theorem price_log_eq {P : ℕ} (hH : 0 < prefixH P) (hL : 0 < prefixEll P) :
    log (1 / prefixPrice P) = prefixEll P + log (prefixEll P) := by
  change log (1 / prefixPrice P) = log (prefixH P) + log (prefixEll P)
  simp only [prefix_price_eq, one_div, inv_inv, log_mul hH.ne' hL.ne']

private theorem scaled_lower_error :
    Tendsto (fun P : ℕ => cubicScale P * lowerError P) atTop (𝓝 0) := by
  have hb := (prefix_log_power_small (by norm_num : (0 : ℝ) < 1 / 3) 2).const_mul 20
  rw [mul_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_prefix_large] with P hdom
    obtain ⟨hH, hL⟩ := hdom
    have hH0 := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < prefixEll P := by linarith
    rw [lowerError, price_log_eq hH0 hL0]
    have hh := log_nonneg hL.le
    have hprice : 0 ≤ prefixPrice P := by rw [prefix_price_eq]; positivity
    dsimp only [cubicScale]
    positivity
  · filter_upwards [eventually_prefix_large] with P hdom
    obtain ⟨hH, hL⟩ := hdom
    let H := prefixH P
    let L := prefixEll P
    have hH0 : 0 < H := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < L := lt_trans zero_lt_one hL
    have hpow : H ^ (2 / 3 : ℝ) = H / H ^ (1 / 3 : ℝ) := by
      calc
        H ^ (2 / 3 : ℝ) = H ^ ((1 : ℝ) - 1 / 3) := by norm_num
        _ = _ := by rw [rpow_sub hH0, rpow_one]
    have hr2 : envelopeRadius P ^ 2 = 1 / H := by
      rw [envelopeRadius, div_pow, one_pow, sq_sqrt hH0.le]
    have he : cubicScale P * lowerError P =
        (16 * L ^ 2 + 2 * L + 2 * log L) / H ^ (1 / 3 : ℝ) := by
      rw [lowerError, price_log_eq hH0 hL0, prefix_price_eq, hr2]
      change H ^ (2 / 3 : ℝ) * L *
        (2 * (1 / (H * L)) * (L + log L) + 16 * L * (1 / H)) = _
      rw [hpow]
      field_simp [hH0.ne', hL0.ne', (rpow_pos_of_pos hH0 (1 / 3 : ℝ)).ne']
      ring
    rw [he, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hlog := log_le_sub_one_of_pos hL0
    have hLsq : L ≤ L ^ 2 := by
      nlinarith only [mul_nonneg hL0.le (show 0 ≤ L - 1 by linarith)]
    linarith only [hlog, hLsq]

private theorem scaled_upper_error :
    Tendsto (fun P : ℕ => cubicScale P * upperError P) atTop (𝓝 0) := by
  have hb := (prefix_log_power_small (by norm_num : (0 : ℝ) < 1 / 12) 1).const_mul 6
  simp only [mul_zero, pow_one] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_prefix_large] with P hdom
    obtain ⟨hH, hL⟩ := hdom
    have hH0 := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < prefixEll P := by linarith
    rw [upperError, price_log_eq hH0 hL0]
    have hh := log_nonneg hL.le
    have hprice : 0 ≤ prefixPrice P := by rw [prefix_price_eq]; positivity
    dsimp only [cubicScale, envelopeCutoff]
    positivity
  · filter_upwards [eventually_prefix_large] with P hdom
    obtain ⟨hH, hL⟩ := hdom
    let H := prefixH P
    let L := prefixEll P
    have hH0 : 0 < H := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < L := lt_trans zero_lt_one hL
    have hq3 : envelopeCutoff P ^ 3 = H ^ (3 / 4 : ℝ) := by
      change (H ^ (1 / 4 : ℝ)) ^ 3 = _
      rw [← rpow_mul_natCast hH0.le]
      norm_num
    have hmul : H ^ (2 / 3 : ℝ) * H ^ (1 / 4 : ℝ) = H ^ (11 / 12 : ℝ) := by
      rw [← rpow_add hH0]
      norm_num
    have hfirst : H ^ (11 / 12 : ℝ) / H = 1 / H ^ (1 / 12 : ℝ) := by
      rw [← rpow_sub_one hH0.ne', one_div, ← rpow_neg hH0.le]
      norm_num
    have hsecond : H ^ (2 / 3 : ℝ) / H ^ (3 / 4 : ℝ) = 1 / H ^ (1 / 12 : ℝ) := by
      rw [← rpow_sub hH0, one_div, ← rpow_neg hH0.le]
      norm_num
    have he : cubicScale P * upperError P = (5 * L + log L + 1) / H ^ (1 / 12 : ℝ) := by
      rw [upperError, hq3, price_log_eq hH0 hL0, prefix_price_eq]
      change H ^ (2 / 3 : ℝ) * L *
        (1 / (H * L) * H ^ (1 / 4 : ℝ) * (L + log L + 1) + 4 / H ^ (3 / 4 : ℝ)) = _
      calc
        _ = (H ^ (2 / 3 : ℝ) * H ^ (1 / 4 : ℝ) / H) * (L + log L + 1) +
            4 * L * (H ^ (2 / 3 : ℝ) / H ^ (3 / 4 : ℝ)) := by
              field_simp [hH0.ne', hL0.ne', (rpow_pos_of_pos hH0 (3 / 4 : ℝ)).ne']
        _ = _ := by rw [hmul, hfirst, hsecond]; ring
    rw [he, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [log_le_sub_one_of_pos hL0]

private theorem residual_envelope :
    ∀ᶠ P : ℕ in atTop,
      secondActivationSum (Nat.primesLE P) (prefixPrice P) - lowerError P ≤
        integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P) ∧
      integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P) ≤
        secondActivationSum (Nat.primesLE P) (prefixPrice P) + upperError P := by
  filter_upwards [eventually_prefix_large, infimum_lt_radius, radius_condition,
      prefixH_atTop.eventually_ge_atTop (16 : ℝ)] with P hdom hA hrscale h16
  obtain ⟨hH, hL⟩ := hdom
  have hH0 := (exp_pos (1 : ℝ)).trans hH
  have hL0 : 0 < prefixEll P := by linarith
  have hsq : 1 ≤ sqrt (prefixH P) := by
    have hs := sqrt_le_sqrt (show (1 : ℝ) ≤ prefixH P by linarith)
    simpa only [sqrt_one] using hs
  have hr : 0 < envelopeRadius P := one_div_pos.mpr (sqrt_pos.mpr hH0)
  have hr1 : envelopeRadius P ≤ 1 := by
    unfold envelopeRadius
    exact (div_le_iff₀ (sqrt_pos.mpr hH0)).mpr (by rwa [one_mul])
  have hq : 2 ≤ envelopeCutoff P := by
    have hq16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
        ← rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 4 (1 / 4 : ℝ)]
      norm_num
    exact hq16.ge.trans (rpow_le_rpow (by norm_num) h16 (by norm_num))
  have hq4 : envelopeCutoff P ^ 4 = prefixH P := by
    unfold envelopeCutoff
    rw [← rpow_mul_natCast hH0.le]
    norm_num
  have hquartic : prefixPrice P * envelopeCutoff P ^ 4 ≤ 1 := by
    rw [hq4, prefix_price_eq]
    have he : 1 / (prefixH P * prefixEll P) * prefixH P = 1 / prefixEll P := by
      field_simp [hH0.ne', hL0.ne']
    rw [he]
    exact (div_le_iff₀ hL0).mpr (by simpa only [one_mul] using hL.le)
  let A₁ := activationSum (Nat.primesLE P) (prefixPrice P)
  let A₂ := secondActivationSum (Nat.primesLE P) (prefixPrice P)
  have hb := finite_integer_activation_envelope
    (S := Nat.primesLE P) (fun _ hp => (Nat.mem_primesLE.mp hp).2)
    hH hr hr1 hrscale hq hquartic
  have hb' : min (envelopeRadius P) (A₁ + A₂ - lowerError P) ≤
      integerInfimum (Nat.primesLE P) ∧
      integerInfimum (Nat.primesLE P) ≤ A₁ + A₂ + upperError P := by
    change min (envelopeRadius P) (A₁ + A₂ -
      2 * prefixPrice P * log (1 / prefixPrice P) -
      16 * prefixEll P * envelopeRadius P ^ 2) ≤ integerInfimum (Nat.primesLE P) ∧
      integerInfimum (Nat.primesLE P) ≤ A₁ + A₂ +
        prefixPrice P * envelopeCutoff P * (log (1 / prefixPrice P) + 1) +
        4 / envelopeCutoff P ^ 3 at hb
    simpa only [lowerError, upperError, sub_add_eq_sub_sub, add_assoc] using hb
  have hLower := (min_le_iff.mp hb'.1).resolve_left (not_le_of_gt hA)
  change A₂ - lowerError P ≤ integerInfimum (Nat.primesLE P) - A₁ ∧
    integerInfimum (Nat.primesLE P) - A₁ ≤ A₂ + upperError P
  exact ⟨by linarith only [hLower], by linarith only [hb'.2]⟩

/-- Cubic residual of the original fixed-support integer Robin infimum.
The first activation is the exact finite prime-prefix sum at the original price. -/
theorem integer_infimum_cubic_activation_residual :
    Tendsto (fun P : ℕ => prefixH P ^ ((2 : ℝ) / 3) * prefixEll P *
      (integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P)))
      atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3))) := by
  have hlo := second_activation_cubic_limit.sub scaled_lower_error
  have hhi := second_activation_cubic_limit.add scaled_upper_error
  simp only [sub_zero] at hlo
  simp only [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [residual_envelope, eventually_prefix_large] with P hb hdom
    obtain ⟨hH, hL⟩ := hdom
    have hH0 := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < prefixEll P := by linarith
    have hs : 0 ≤ cubicScale P := by unfold cubicScale; positivity
    calc
      _ = cubicScale P *
          (secondActivationSum (Nat.primesLE P) (prefixPrice P) - lowerError P) :=
        (mul_sub _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 hs
  · filter_upwards [residual_envelope, eventually_prefix_large] with P hb hdom
    obtain ⟨hH, hL⟩ := hdom
    have hH0 := (exp_pos (1 : ℝ)).trans hH
    have hL0 : 0 < prefixEll P := by linarith
    have hs : 0 ≤ cubicScale P := by unfold cubicScale; positivity
    calc
      _ ≤ cubicScale P *
          (secondActivationSum (Nat.primesLE P) (prefixPrice P) + upperError P) :=
        mul_le_mul_of_nonneg_left hb.2 hs
      _ = _ := mul_add _ _ _

end D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual
