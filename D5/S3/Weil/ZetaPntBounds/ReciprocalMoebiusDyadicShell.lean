/- GID: D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusDyadicShell
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/ReciprocalMoebiusDyadicShell
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Every critical-strip zeta zero forces a uniform lower bound for the dyadic reciprocal Möbius shell mass. -/

import D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The reciprocal Möbius dyadic shell at a zeta zero

The finite floor inverse gives a bounded double difference. The native
fractional-part Mellin formula annihilates the dyadic kernel at a zeta zero,
leaving the Mellin integral of the error on the short reciprocal interval.
-/

open MeasureTheory Set

noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse

open D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
  (fractionalMellin_eq_zeta fractionalMellin_integrableOn)
open D5.S3.Arith.MoebiusLogarithmic (reciprocalSum abs_reciprocalSum_le_one)

def shell (u : ℝ) : ℝ := reciprocalSum u - reciprocalSum (u / 2)

def kernel (y : ℝ) : ℝ := 2 * Int.fract (y / 2) - Int.fract y

def target (x : ℝ) : ℝ :=
  max (x - 1) 0 - 4 * max (x / 2 - 1) 0 + 4 * max (x / 4 - 1) 0

def response (P x : ℝ) : ℝ := ∫ u in (1 : ℝ)..P, shell u * kernel (x / u)

private theorem measurable_shell : Measurable shell :=
  measurable_reciprocalSum.sub
    (measurable_reciprocalSum.comp (measurable_id.div_const 2))

private theorem measurable_kernel : Measurable kernel :=
  (measurable_const.mul (measurable_id.div_const 2).fract).sub measurable_id.fract

private theorem abs_shell_le (u : ℝ) : |shell u| ≤ 2 := by
  unfold shell
  exact (abs_sub _ _).trans
    (by linarith [abs_reciprocalSum_le_one u, abs_reciprocalSum_le_one (u / 2)])

private theorem kernel_intFloor (y : ℝ) :
    kernel y = ((⌊y⌋ - 2 * ⌊y / 2⌋ : ℤ) : ℝ) := by
  simp only [kernel, Int.fract, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

private theorem kernel_zero_or_one (y : ℝ) : kernel y = 0 ∨ kernel y = 1 := by
  let n : ℤ := ⌊y⌋ - 2 * ⌊y / 2⌋
  have he : kernel y = (n : ℝ) := kernel_intFloor y
  have hlo : -1 < (n : ℝ) := by
    rw [← he, kernel]
    linarith [Int.fract_nonneg (y / 2), Int.fract_lt_one y]
  have hhi : (n : ℝ) < 2 := by
    rw [← he, kernel]
    linarith [Int.fract_lt_one (y / 2), Int.fract_nonneg y]
  have h₀ : (-1 : ℤ) < n := by exact_mod_cast hlo
  have h₂ : n < (2 : ℤ) := by exact_mod_cast hhi
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with h | h
  · left
    simpa only [h, Int.cast_zero] using he
  · right
    simpa only [h, Int.cast_one] using he

private theorem abs_kernel_le (y : ℝ) : |kernel y| ≤ 1 := by
  rcases kernel_zero_or_one y with h | h <;> simp [h]

private theorem kernel_natFloor {y : ℝ} (hy : 0 ≤ y) :
    kernel y = (Nat.floor y : ℝ) - 2 * (Nat.floor (y / 2) : ℝ) := by
  simp only [kernel_intFloor, natCast_floor_eq_intCast_floor hy,
    natCast_floor_eq_intCast_floor (show 0 ≤ y / 2 by positivity),
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat]

private theorem kernel_eq_zero {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) : kernel y = 0 := by
  rw [kernel_natFloor hy, Nat.floor_eq_zero.2 hy1,
    Nat.floor_eq_zero.2 (show y / 2 < 1 by linarith)]
  norm_num

private theorem reciprocalSum_eq_zero {u : ℝ} (hu : u < 1) : reciprocalSum u = 0 := by
  simp [reciprocalSum, Nat.floor_eq_zero.2 hu]

private theorem intervalIntegrable_bounded {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hC : ∀ t, |f t| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rcases le_total a b with hab | hba
  · exact bounded_intervalIntegrable hab hf (fun t _ => hC t)
  · exact (bounded_intervalIntegrable hba hf (fun t _ => hC t)).symm

private theorem abs_mul_kernel_le (a y : ℝ) : |a * kernel y| ≤ |a| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_kernel_le _)

private theorem intervalIntegrable_Q_floor {a P : ℝ} (hP : 1 ≤ P) (ha : 0 ≤ a) :
    IntervalIntegrable (fun u : ℝ => reciprocalSum u * (Nat.floor (a / u) : ℝ))
      volume 1 P := by
  refine bounded_intervalIntegrable (C := a) hP
    (measurable_reciprocalSum.mul (measurable_floorRatio a)) ?_
  intro u hu
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_reciprocalSum_le_one u)).trans
    (floorRatio_bound ha hu.1.le)

private theorem single_difference {P x : ℝ} (hP : 1 ≤ P) (hx : 0 ≤ x) (hxP : x ≤ P) :
    (∫ u in (1 : ℝ)..P, reciprocalSum u * kernel (x / u)) =
      max (x - 1) 0 - 2 * max (x / 2 - 1) 0 := by
  have hx2 : 0 ≤ x / 2 := by positivity
  have he (u : ℝ) : (x / u) / 2 = (x / 2) / u := by
    simp only [div_div, mul_comm u (2 : ℝ)]
  have hRewrite :
      (∫ u in (1 : ℝ)..P, reciprocalSum u * kernel (x / u)) =
        ∫ u in (1 : ℝ)..P, reciprocalSum u * (Nat.floor (x / u) : ℝ) -
          2 * (reciprocalSum u * (Nat.floor ((x / 2) / u) : ℝ)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hP
    intro u hu
    dsimp only
    rw [kernel_natFloor (div_nonneg hx (zero_lt_one.trans hu.1).le), he u]
    ring
  rw [hRewrite, intervalIntegral.integral_sub (intervalIntegrable_Q_floor hP hx)
    ((intervalIntegrable_Q_floor hP hx2).const_mul 2),
    intervalIntegral.integral_const_mul, floorIntegral_eq hP hx hxP,
    floorIntegral_eq hP hx2 (by linarith : x / 2 ≤ P)]

theorem dyadicShell_convolution {P x : ℝ} (hP : 1 ≤ P) (hx : 0 ≤ x) (hxP : x ≤ P) :
    response P x = target x := by
  let f : ℝ → ℝ := fun v => reciprocalSum v * kernel ((x / 2) / v)
  have hK (a : ℝ) : Measurable (fun v : ℝ => kernel (a / v)) :=
    measurable_kernel.comp (measurable_const.div measurable_id)
  have hf (a b : ℝ) : IntervalIntegrable f volume a b :=
    intervalIntegrable_bounded (measurable_reciprocalSum.mul (hK (x / 2)))
      (fun v => (abs_mul_kernel_le _ _).trans (abs_reciprocalSum_le_one v)) a b
  have hscale :
      (∫ u in (1 : ℝ)..P, reciprocalSum (u / 2) * kernel (x / u)) =
        2 * (∫ v in (1 / 2 : ℝ)..(P / 2), f v) := by
    have he (v : ℝ) : f v = reciprocalSum ((v * 2) / 2) * kernel (x / (v * 2)) := by
      simp only [f, mul_div_cancel_right₀ v (by norm_num : (2 : ℝ) ≠ 0), div_div,
        mul_comm (2 : ℝ) v]
    simp_rw [he]
    symm
    have h := intervalIntegral.smul_integral_comp_mul_right
      (a := (1 / 2 : ℝ)) (b := P / 2)
      (fun u : ℝ => reciprocalSum (u / 2) * kernel (x / u)) (2 : ℝ)
    simpa only [smul_eq_mul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hleft : (∫ v in (1 / 2 : ℝ)..1, f v) = 0 := by
    calc
      _ = ∫ _v in (1 / 2 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro v hv
        simp [f, reciprocalSum_eq_zero hv.2]
      _ = _ := intervalIntegral.integral_zero
  have hright : (∫ v in (P / 2)..P, f v) = 0 := by
    calc
      _ = ∫ _v in (P / 2)..P, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro v hv
        have hv0 : 0 < v := by linarith [hv.1]
        have hvx : x / 2 < v := by linarith [hv.1]
        simp [f, kernel_eq_zero (div_nonneg (show 0 ≤ x / 2 by positivity) hv0.le)
          ((div_lt_one hv0).2 hvx)]
      _ = _ := intervalIntegral.integral_zero
  -- Oriented additivity applies even when P / 2 lies below 1.
  have hext : (∫ v in (1 / 2 : ℝ)..(P / 2), f v) = ∫ v in (1 : ℝ)..P, f v := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (hf (1 / 2) (P / 2))
      (hf (P / 2) P)
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (hf (1 / 2) 1) (hf 1 P)
    rw [hright, add_zero] at h₁
    rw [hleft, zero_add] at h₂
    exact h₁.trans h₂.symm
  have hQ (a : ℝ) : IntervalIntegrable (fun u : ℝ => reciprocalSum u * kernel (a / u))
      volume 1 P :=
    intervalIntegrable_bounded (measurable_reciprocalSum.mul (hK a))
      (fun u => (abs_mul_kernel_le _ _).trans (abs_reciprocalSum_le_one u)) 1 P
  have hQ₂ : IntervalIntegrable (fun u : ℝ => reciprocalSum (u / 2) * kernel (x / u))
      volume 1 P :=
    intervalIntegrable_bounded
      ((measurable_reciprocalSum.comp (measurable_id.div_const 2)).mul (hK x))
      (fun u => (abs_mul_kernel_le _ _).trans (abs_reciprocalSum_le_one (u / 2))) 1 P
  unfold response shell
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hQ x) hQ₂, hscale, hext]
  change (∫ u in (1 : ℝ)..P, reciprocalSum u * kernel (x / u)) -
    2 * (∫ u in (1 : ℝ)..P, reciprocalSum u * kernel ((x / 2) / u)) = target x
  rw [single_difference hP hx hxP,
    single_difference hP (show 0 ≤ x / 2 by positivity) (show x / 2 ≤ P by linarith),
    show x / 2 / 2 = x / 4 by ring]
  unfold target
  ring

private theorem target_of_le_one {x : ℝ} (hx : x ≤ 1) : target x = 0 := by
  simp [target, max_eq_right (show x - 1 ≤ 0 by linarith),
    max_eq_right (show x / 2 - 1 ≤ 0 by linarith),
    max_eq_right (show x / 4 - 1 ≤ 0 by linarith)]

private theorem target_of_one_le_of_le_two {x : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ 2) :
    target x = x - 1 := by
  simp [target, max_eq_left (sub_nonneg.mpr h₁),
    max_eq_right (show x / 2 - 1 ≤ 0 by linarith),
    max_eq_right (show x / 4 - 1 ≤ 0 by linarith)]

private theorem target_of_two_le_of_le_four {x : ℝ} (h₂ : 2 ≤ x) (h₄ : x ≤ 4) :
    target x = 3 - x := by
  simp only [target, max_eq_left (show 0 ≤ x - 1 by linarith),
    max_eq_left (show 0 ≤ x / 2 - 1 by linarith),
    max_eq_right (show x / 4 - 1 ≤ 0 by linarith)]
  ring

private theorem target_of_four_le {x : ℝ} (hx : 4 ≤ x) : target x = -1 := by
  simp only [target, max_eq_left (show 0 ≤ x - 1 by linarith),
    max_eq_left (show 0 ≤ x / 2 - 1 by linarith),
    max_eq_left (show 0 ≤ x / 4 - 1 by linarith)]
  ring

private theorem abs_target_le (x : ℝ) : |target x| ≤ 1 := by
  rcases le_or_gt x 1 with h₁ | h₁
  · rw [target_of_le_one h₁, abs_zero]
    norm_num
  rcases le_or_gt x 2 with h₂ | h₂
  · rw [target_of_one_le_of_le_two h₁.le h₂, abs_le]
    constructor <;> linarith
  rcases le_or_gt x 4 with h₄ | h₄
  · rw [target_of_two_le_of_le_four h₂.le h₄, abs_le]
    constructor <;> linarith
  · simp only [target_of_four_le h₄.le, abs_neg, abs_one, le_refl]

private theorem abs_response_le {P : ℝ} (hP : 1 ≤ P) (x : ℝ) :
    |response P x| ≤ ∫ u in (1 : ℝ)..P, |shell u| := by
  unfold response
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hP ?_
    (intervalIntegrable_bounded measurable_shell.abs
      (fun u => by simpa only [abs_abs] using abs_shell_le u) 1 P)
  filter_upwards with u
  intro _
  exact (Real.norm_eq_abs _).trans_le (abs_mul_kernel_le _ _)

private def weight (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1)

private theorem weight_intervalIntegrable {s : ℂ} (hs : 0 < s.re) (a b : ℝ) :
    IntervalIntegrable (weight s) volume a b := by
  unfold weight
  apply intervalIntegral.intervalIntegrable_cpow'
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private theorem target_intervalIntegrable {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (target (1 / t) : ℂ) * weight s t) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
  have hp : Integrable (weight s) (volume.restrict (Ioc a b)) :=
    (weight_intervalIntegrable hs a b).1
  have hm : Continuous target := by
    unfold target
    fun_prop
  have hrec : Measurable (fun t : ℝ => (1 : ℝ) / t) := measurable_const.div measurable_id
  have htarget : Measurable (fun t : ℝ => (target (1 / t) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hm.measurable.comp hrec)
  refine hp.mono (htarget.aestronglyMeasurable.mul hp.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_target_le _)

private theorem kernel_mellin_zero {rho : ℂ} (h₀ : 0 < rho.re) (h₁ : rho.re < 1)
    (hz : riemannZeta rho = 0) {u : ℝ} (hu : 1 ≤ u) :
    (∫ t in Ioo (0 : ℝ) 1, (kernel (1 / t / u) : ℂ) * weight rho t) = 0 := by
  let θ : ℝ := 1 / u
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hθ : 0 < θ := one_div_pos.mpr hu₀
  have hθ₁ : θ ≤ 1 := (div_le_one hu₀).2 hu
  have hθ₂ : 0 < θ / 2 := div_pos hθ (by norm_num)
  have hpoint (t : ℝ) :
      (kernel (1 / t / u) : ℂ) * weight rho t =
        2 * (((Int.fract ((θ / 2) / t) : ℝ) : ℂ) * weight rho t) -
          ((Int.fract (θ / t) : ℝ) : ℂ) * weight rho t := by
    have he : 1 / t / u = θ / t := by simp only [θ, div_div, mul_comm t u]
    have he₂ : (θ / t) / 2 = (θ / 2) / t := by simp only [div_div, mul_comm t (2 : ℝ)]
    rw [he, kernel, he₂]
    push_cast
    ring
  simp_rw [hpoint]
  unfold weight
  rw [integral_sub ((fractionalMellin_integrableOn (θ / 2) rho h₀).const_mul 2)
    (fractionalMellin_integrableOn θ rho h₀), integral_const_mul]
  rw [fractionalMellin_eq_zeta (θ / 2) hθ₂ (by linarith) rho h₀ h₁,
    fractionalMellin_eq_zeta θ hθ hθ₁ rho h₀ h₁, hz]
  simp only [mul_zero, zero_div, sub_zero, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

private theorem response_mellin_zero {P : ℝ} (hP : 1 ≤ P)
    {rho : ℂ} (h₀ : 0 < rho.re) (h₁ : rho.re < 1) (hz : riemannZeta rho = 0) :
    IntegrableOn (fun t : ℝ => (response P (1 / t) : ℂ) * weight rho t) (Ioo 0 1) ∧
      (∫ t in Ioo (0 : ℝ) 1, (response P (1 / t) : ℂ) * weight rho t) = 0 := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let ν := volume.restrict (Ioc (1 : ℝ) P)
  let f (t u : ℝ) : ℂ := ((shell u * kernel (1 / t / u) : ℝ) : ℂ) * weight rho t
  have hw : Integrable (weight rho) μ := by
    exact ((weight_intervalIntegrable h₀ 0 1).1).mono_set Ioo_subset_Ioc_self
  have h₂ : Integrable (fun _ : ℝ => (2 : ℝ)) ν :=
    (intervalIntegrable_const (a := (1 : ℝ)) (b := P) (μ := volume) (c := (2 : ℝ))).1
  have hmeas : Measurable (fun p : ℝ × ℝ => shell p.2 * kernel (1 / p.1 / p.2)) :=
    (measurable_shell.comp measurable_snd).mul
      (measurable_kernel.comp ((measurable_const.div measurable_fst).div measurable_snd))
  have hf : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine (hw.norm.mul_prod h₂).mono'
      ((Complex.continuous_ofReal.measurable.comp hmeas).aestronglyMeasurable.mul
        hw.aestronglyMeasurable.comp_fst) ?_
    filter_upwards with p
    change ‖f p.1 p.2‖ ≤ ‖weight rho p.1‖ * 2
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm _ ‖weight rho p.1‖]
    exact mul_le_mul_of_nonneg_left
      ((abs_mul_kernel_le _ _).trans (abs_shell_le _)) (norm_nonneg _)
  have houter (t : ℝ) : (∫ u, f t u ∂ν) = (response P (1 / t) : ℂ) * weight rho t := by
    dsimp only [f]
    rw [integral_mul_const, integral_complex_ofReal, response, intervalIntegral.integral_of_le hP]
  have hinner (u : ℝ) (hu : u ∈ Ioc (1 : ℝ) P) : (∫ t, f t u ∂μ) = 0 := by
    change (∫ t in Ioo (0 : ℝ) 1, ((shell u * kernel (1 / t / u) : ℝ) : ℂ) *
      weight rho t) = 0
    simp only [Complex.ofReal_mul, mul_assoc, integral_const_mul,
      kernel_mellin_zero h₀ h₁ hz hu.1.le, mul_zero]
  constructor
  · change Integrable (fun t : ℝ => (response P (1 / t) : ℂ) * weight rho t) μ
    simpa only [Function.uncurry_apply_pair, houter] using hf.integral_prod_left
  · change (∫ t, (response P (1 / t) : ℂ) * weight rho t ∂μ) = 0
    calc
      _ = ∫ t, ∫ u, f t u ∂ν ∂μ := by simp only [houter]
      _ = ∫ u, ∫ t, f t u ∂μ ∂ν := integral_integral_swap hf
      _ = ∫ _u : ℝ, (0 : ℂ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact hinner u hu
      _ = 0 := integral_zero ℝ ℂ

private theorem target_mellin {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    (∫ t in Ioo (0 : ℝ) 1, (target (1 / t) : ℂ) * weight s t) =
      (1 - (2 : ℂ) ^ (1 - s)) ^ (2 : ℕ) / (s * (s - 1)) := by
  let a : ℝ := 1 / 4
  let b : ℝ := 1 / 2
  have ha : 0 < a := by norm_num [a]
  have hab : a ≤ b := by norm_num [a, b]
  have hb : b ≤ 1 := by norm_num [b]
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  let j (t : ℝ) : ℂ := (target (1 / t) : ℂ) * weight s t
  let v (t : ℝ) : ℂ := (t : ℂ) ^ (s - 2)
  have hw (c d : ℝ) : IntervalIntegrable (weight s) volume c d :=
    weight_intervalIntegrable hs c d
  have hzero {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) : (0 : ℝ) ∉ uIcc c d := by
    rw [uIcc_of_le hcd]
    exact fun h => hc.not_ge h.1
  have hv {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
      IntervalIntegrable v volume c d := by
    dsimp only [v]
    exact intervalIntegral.intervalIntegrable_cpow (Or.inr (hzero hc hcd))
  have iw (c d : ℝ) : (∫ t in c..d, weight s t) =
      ((d : ℂ) ^ s - (c : ℂ) ^ s) / s := by
    unfold weight
    rw [integral_cpow (Or.inl (show -1 < (s - 1).re by
      simp only [Complex.sub_re, Complex.one_re]; linarith)),
      show s - 1 + 1 = s by ring]
  have iv {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) : (∫ t in c..d, v t) =
      ((d : ℂ) ^ (s - 1) - (c : ℂ) ^ (s - 1)) / (s - 1) := by
    dsimp only [v]
    have hn : s - 2 ≠ -1 := by
      intro h
      apply hs1
      linear_combination h
    rw [integral_cpow (Or.inr ⟨hn, hzero hc hcd⟩), show s - 2 + 1 = s - 1 by ring]
  have hrec {t : ℝ} (ht : 0 < t) : ((1 / t : ℝ) : ℂ) * weight s t = v t := by
    unfold weight
    dsimp only [v]
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div,
      ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  have hlow : (∫ t in (0 : ℝ)..a, j t) = -((a : ℂ) ^ s / s) := by
    calc
      _ = ∫ t in (0 : ℝ)..a, -weight s t := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha.le
        intro t ht
        have ht' : 4 ≤ 1 / t :=
          (le_div_iff₀ ht.1).2 (by linarith [show t < 1 / 4 from ht.2])
        simp only [j, target_of_four_le ht', Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
      _ = _ := by
        rw [intervalIntegral.integral_neg, iw, Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]
  have hmid : (∫ t in a..b, j t) =
      3 * (((b : ℂ) ^ s - (a : ℂ) ^ s) / s) -
        (((b : ℂ) ^ (s - 1) - (a : ℂ) ^ (s - 1)) / (s - 1)) := by
    calc
      _ = ∫ t in a..b, 3 * weight s t - v t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        have ht₀ : 0 < t := ha.trans ht.1
        have ht₂ : 2 ≤ 1 / t :=
          (le_div_iff₀ ht₀).2 (by linarith [show t < 1 / 2 from ht.2])
        have ht₄ : 1 / t ≤ 4 :=
          (div_le_iff₀ ht₀).2 (by linarith [show 1 / 4 < t from ht.1])
        simp only [j, target_of_two_le_of_le_four ht₂ ht₄, Complex.ofReal_sub,
          Complex.ofReal_ofNat, sub_mul, hrec ht₀]
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hw a b).const_mul 3) (hv ha hab),
          intervalIntegral.integral_const_mul, iw, iv ha hab]
  have hb₀ : 0 < b := ha.trans_le hab
  have hhigh : (∫ t in b..(1 : ℝ), j t) =
      (1 - (b : ℂ) ^ (s - 1)) / (s - 1) - (1 - (b : ℂ) ^ s) / s := by
    calc
      _ = ∫ t in b..(1 : ℝ), v t - weight s t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb
        intro t ht
        have ht₀ : 0 < t := hb₀.trans ht.1
        have ht₁ : 1 ≤ 1 / t := (one_le_div ht₀).2 ht.2.le
        have ht₂ : 1 / t ≤ 2 :=
          (div_le_iff₀ ht₀).2 (by linarith [show 1 / 2 < t from ht.1])
        simp only [j, target_of_one_le_of_le_two ht₁ ht₂, Complex.ofReal_sub,
          Complex.ofReal_one, sub_mul, one_mul, hrec ht₀]
      _ = _ := by
        rw [intervalIntegral.integral_sub (hv hb₀ hb) (hw b 1), iw b 1, iv hb₀ hb]
        simp only [Complex.ofReal_one, Complex.one_cpow]
  have hbPow (z : ℂ) : (b : ℂ) ^ z = (2 : ℂ) ^ (-z) := by
    dsimp only [b]
    rw [one_div, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2), Complex.cpow_neg,
      Complex.ofReal_ofNat]
  have haPow (z : ℂ) : (a : ℂ) ^ z = ((b : ℂ) ^ z) ^ (2 : ℕ) := by
    have he : a = b * b := by norm_num [a, b]
    rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hb₀.le hb₀.le, pow_two]
  have hbShift₁ : (b : ℂ) ^ (s - 1) = (2 : ℂ) ^ (1 - s) := by
    rw [hbPow]
    congr 1
    ring
  have hbShift₀ : (b : ℂ) ^ s = (2 : ℂ) ^ (1 - s) / 2 := by
    rw [hbPow, show -s = (1 - s) + (-1) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_neg_one, div_eq_mul_inv]
  change (∫ t in Ioo (0 : ℝ) 1, j t) = _
  have hJa : IntervalIntegrable j volume 0 a := target_intervalIntegrable hs ha.le
  have hJb : IntervalIntegrable j volume a b := target_intervalIntegrable hs hab
  have hJc : IntervalIntegrable j volume b 1 := target_intervalIntegrable hs hb
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (hJa.trans hJb) hJc,
    ← intervalIntegral.integral_add_adjacent_intervals hJa hJb,
    hlow, hmid, hhigh, haPow s, haPow (s - 1), hbShift₀, hbShift₁]
  field_simp [hs0, hs1]
  ring

def shellError (P x : ℝ) : ℝ := target x - response P x

theorem shellError_eq_zero {P x : ℝ} (hP : 1 ≤ P) (hx : 0 ≤ x) (hPx : x ≤ P) :
    shellError P x = 0 := by
  simp [shellError, dyadicShell_convolution hP hx hPx]

theorem abs_shellError_le {P : ℝ} (hP : 1 ≤ P) (x : ℝ) :
    |shellError P x| ≤ 1 + ∫ u in (1 : ℝ)..P, |shell u| := by
  unfold shellError
  exact (abs_sub _ _).trans (add_le_add (abs_target_le x) (abs_response_le hP x))

/-- The dyadic reciprocal Möbius shell mass bounds the obstruction from every zeta
zero in the critical strip, at every real cutoff at least one. -/
theorem dyadicReciprocalMoebiusShell_lower {P : ℝ} (hP : 1 ≤ P)
    {rho : ℂ} (h₀ : 0 < rho.re) (h₁ : rho.re < 1) (hz : riemannZeta rho = 0) :
    rho.re * ‖1 - (2 : ℂ) ^ (1 - rho)‖ ^ (2 : ℕ) / ‖rho * (rho - 1)‖ * P ^ rho.re ≤
      1 + ∫ u in (1 : ℝ)..P, |reciprocalSum u - reciprocalSum (u / 2)| := by
  let N : ℝ := 1 + ∫ u in (1 : ℝ)..P, |shell u|
  let e (t : ℝ) : ℂ := (shellError P (1 / t) : ℂ) * weight rho t
  let c : ℝ := 1 / P
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hc₀ : 0 < c := one_div_pos.mpr hP₀
  have hc₁ : c ≤ 1 := (div_le_one hP₀).2 hP
  have hJ : IntegrableOn (fun t : ℝ => (target (1 / t) : ℂ) * weight rho t) (Ioo 0 1) :=
    (target_intervalIntegrable h₀ (show (0 : ℝ) ≤ 1 by norm_num)).1.mono_set Ioo_subset_Ioc_self
  obtain ⟨hV, hVzero⟩ := response_mellin_zero hP h₀ h₁ hz
  have hE : (∫ t in Ioo (0 : ℝ) 1, e t) =
      (1 - (2 : ℂ) ^ (1 - rho)) ^ (2 : ℕ) / (rho * (rho - 1)) := by
    simp only [e, shellError, Complex.ofReal_sub, sub_mul]
    rw [integral_sub hJ hV, hVzero, sub_zero, target_mellin h₀ h₁]
  have hcut : (∫ t in Ioo (0 : ℝ) 1, e t) = ∫ t in Ioo (0 : ℝ) c, e t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_right hc₁)
    intro t ht
    have ht₀ : 0 < t := ht.1.1
    have hct : c ≤ t := le_of_not_gt (fun h => ht.2 ⟨ht₀, h⟩)
    have hmul : 1 ≤ t * P := (div_le_iff₀ hP₀).1 hct
    have hxP : 1 / t ≤ P := (div_le_iff₀ ht₀).2 (by simpa only [mul_comm] using hmul)
    simp only [e, shellError_eq_zero hP (div_nonneg zero_le_one ht₀.le) hxP,
      Complex.ofReal_zero, zero_mul]
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (rho.re - 1)) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hg : IntegrableOn (fun t : ℝ => N * t ^ (rho.re - 1)) (Ioo 0 c) :=
    (show IntegrableOn (fun t : ℝ => N * t ^ (rho.re - 1)) (Ioc 0 c) volume from
      hp.1.const_mul N).mono_set Ioo_subset_Ioc_self
  have hnorm : ‖∫ t in Ioo (0 : ℝ) c, e t‖ ≤ ∫ t in Ioo (0 : ℝ) c, N * t ^ (rho.re - 1) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp only [e]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, weight,
      Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (abs_shellError_le hP _) (Real.rpow_nonneg ht.1.le _)
  have hpower :
      (∫ t in Ioo (0 : ℝ) c, N * t ^ (rho.re - 1)) = N / (P ^ rho.re * rho.re) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc₀.le,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (show -1 < rho.re - 1 by linarith)),
      show rho.re - 1 + 1 = rho.re by ring, Real.zero_rpow h₀.ne', sub_zero]
    dsimp only [c]
    rw [one_div, Real.inv_rpow hP₀.le]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
  rw [← hcut, hE, norm_div, norm_pow, hpower] at hnorm
  have hpos : 0 < P ^ rho.re * rho.re := mul_pos (Real.rpow_pos_of_pos hP₀ _) h₀
  have hresult := (le_div_iff₀ hpos).1 hnorm
  change _ ≤ N
  convert hresult using 1
  ring

end D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
