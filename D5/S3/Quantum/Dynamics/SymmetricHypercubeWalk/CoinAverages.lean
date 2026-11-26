/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The character coin orbit and its continuous and discrete pair averages. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic

compile_only_with_mathlib

/-! The coin block of the shift-after-reflection walk on a character. -/

section

open scoped BigOperators Matrix

set_option autoImplicit false

namespace HypercubeWalsh

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] private theorem sign_false : sign false = 1 := rfl
@[simp] private theorem sign_true : sign true = -1 := rfl

@[simp] private theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num

theorem sign_mul (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

structure Kernel (ι : Type*) [Fintype ι] where
  p : ι → ℝ
  nonneg : ∀ y, 0 ≤ p y
  total : ∑ y, p y = 1

namespace Kernel

variable {ι : Type*} [Fintype ι] (K : Kernel ι)

noncomputable def coin : ι → ℝ := fun y => Real.sqrt (K.p y)

noncomputable def signed (a : ι → Bool) : ι → ℝ :=
  fun y => sign (a y) * K.coin y

noncomputable def eigenvalue (a : ι → Bool) : ℝ :=
  ∑ y, K.p y * sign (a y)

noncomputable def reflection (f : ι → ℝ) : ι → ℝ :=
  fun y => 2 * (K.coin ⬝ᵥ f) * K.coin y - f y

noncomputable def step (a : ι → Bool) (f : ι → ℝ) : ι → ℝ :=
  fun y => sign (a y) * K.reflection f y

noncomputable def orbit (a : ι → Bool) (n : ℕ) : ι → ℝ :=
  (K.step a)^[n] K.coin

private theorem coin_sq (y : ι) : K.coin y ^ 2 = K.p y :=
  Real.sq_sqrt (K.nonneg y)

@[simp] private theorem coin_gram : K.coin ⬝ᵥ K.coin = 1 := by
  simpa only [dotProduct, ← pow_two, K.coin_sq] using K.total

private theorem signed_gram (a b : ι → Bool) :
    K.signed a ⬝ᵥ K.signed b = K.eigenvalue (fun y => a y ^^ b y) := by
  unfold dotProduct eigenvalue
  apply Finset.sum_congr rfl
  intro y _
  rw [sign_mul, ← K.coin_sq]
  simp only [signed]
  ring

@[simp] private theorem coin_signed_gram (a : ι → Bool) :
    K.coin ⬝ᵥ K.signed a = K.eigenvalue a := by
  unfold dotProduct eigenvalue
  apply Finset.sum_congr rfl
  intro y _
  rw [← K.coin_sq]
  simp only [signed]
  ring

@[simp] private theorem signed_coin_gram (a : ι → Bool) :
    K.signed a ⬝ᵥ K.coin = K.eigenvalue a := by rw [dotProduct_comm, coin_signed_gram]

@[simp] private theorem signed_self_gram (a : ι → Bool) :
    K.signed a ⬝ᵥ K.signed a = 1 := by
  rw [K.signed_gram]
  simpa [eigenvalue] using K.total

private theorem eigenvalue_bounds (a : ι → Bool) : -1 ≤ K.eigenvalue a ∧ K.eigenvalue a ≤ 1 := by
  constructor
  · calc
      -1 = ∑ y, K.p y * (-1) := by rw [← Finset.sum_mul, K.total, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (K.nonneg y)
        cases a y <;> norm_num
  · rw [← K.total]
    apply Finset.sum_le_sum
    intro y _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show sign (a y) ≤ 1 by cases a y <;> norm_num) (K.nonneg y)

private theorem step_add (a : ι → Bool) (f g : ι → ℝ) :
    K.step a (f + g) = K.step a f + K.step a g := by
  ext y
  simp only [step, reflection, dotProduct_add, Pi.add_apply]
  ring

private theorem step_smul (a : ι → Bool) (r : ℝ) (f : ι → ℝ) :
    K.step a (r • f) = r • K.step a f := by
  ext y
  simp only [step, reflection, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem step_sub (a : ι → Bool) (f g : ι → ℝ) :
    K.step a (f - g) = K.step a f - K.step a g := by
  ext y
  simp only [step, reflection, dotProduct_sub, Pi.sub_apply]
  ring

theorem step_coin (a : ι → Bool) : K.step a K.coin = K.signed a := by
  ext y
  simp only [step, signed, reflection, coin_gram]
  ring

theorem step_signed (a : ι → Bool) :
    K.step a (K.signed a) = (2 * K.eigenvalue a) • K.signed a - K.coin := by
  ext y
  simp only [step, reflection, coin_signed_gram, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, signed]
  calc
    _ = 2 * K.eigenvalue a * (sign (a y) * K.coin y) - sign (a y) ^ 2 * K.coin y := by ring
    _ = _ := by rw [sign_sq, one_mul]

noncomputable def centered (a : ι → Bool) : ι → ℝ :=
  K.signed a - K.eigenvalue a • K.coin

noncomputable def sigma (a : ι → Bool) : ℝ :=
  Real.sqrt (1 - K.eigenvalue a ^ 2)

noncomputable def direction (a : ι → Bool) : ι → ℝ :=
  (K.sigma a)⁻¹ • K.centered a

noncomputable def angle (a : ι → Bool) : ℝ := Real.arccos (K.eigenvalue a)

private theorem sigma_sq (a : ι → Bool) : K.sigma a ^ 2 = 1 - K.eigenvalue a ^ 2 := by
  rcases K.eigenvalue_bounds a with ⟨h₁, h₂⟩
  exact Real.sq_sqrt
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h₂) (by linarith : 0 ≤ 1 + K.eigenvalue a)])

private theorem sigma_pos (a : ι → Bool) (h : |K.eigenvalue a| < 1) : 0 < K.sigma a := by
  rw [abs_lt] at h
  apply Real.sqrt_pos.2
  nlinarith [mul_pos (sub_pos.2 h.2) (by linarith [h.1] : 0 < 1 + K.eigenvalue a)]

@[simp] private theorem cos_angle (a : ι → Bool) : Real.cos (K.angle a) = K.eigenvalue a :=
  Real.cos_arccos (K.eigenvalue_bounds a).1 (K.eigenvalue_bounds a).2

@[simp] private theorem sin_angle (a : ι → Bool) : Real.sin (K.angle a) = K.sigma a :=
  Real.sin_arccos _

@[simp] private theorem coin_centered_gram (a : ι → Bool) :
    K.coin ⬝ᵥ K.centered a = 0 := by
  simp [centered, dotProduct_sub, dotProduct_smul]

@[simp] private theorem coin_direction_gram (a : ι → Bool) :
    K.coin ⬝ᵥ K.direction a = 0 := by simp [direction, dotProduct_smul]

@[simp] private theorem direction_coin_gram (a : ι → Bool) :
    K.direction a ⬝ᵥ K.coin = 0 := by rw [dotProduct_comm, coin_direction_gram]

private theorem centered_gram (a b : ι → Bool) :
    K.centered a ⬝ᵥ K.centered b =
      K.eigenvalue (fun y => a y ^^ b y) - K.eigenvalue a * K.eigenvalue b := by
  simp only [centered, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    signed_gram, signed_coin_gram, coin_signed_gram, coin_gram, smul_eq_mul]
  ring

private theorem centered_self_gram (a : ι → Bool) :
    K.centered a ⬝ᵥ K.centered a = 1 - K.eigenvalue a ^ 2 := by
  rw [K.centered_gram]
  simp [eigenvalue, K.total, pow_two]

theorem direction_gram (a b : ι → Bool) :
    K.direction a ⬝ᵥ K.direction b =
      (K.eigenvalue (fun y => a y ^^ b y) - K.eigenvalue a * K.eigenvalue b) /
        (K.sigma a * K.sigma b) := by
  rw [direction, direction, smul_dotProduct, dotProduct_smul, K.centered_gram]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem direction_self_gram (a : ι → Bool) (h : |K.eigenvalue a| < 1) :
    K.direction a ⬝ᵥ K.direction a = 1 := by
  rw [direction, smul_dotProduct, dotProduct_smul, K.centered_self_gram, ← K.sigma_sq]
  simp only [smul_eq_mul]
  field_simp [(K.sigma_pos a h).ne']

private theorem centered_eq_zero_of_endpoint (a : ι → Bool) (h : K.eigenvalue a ^ 2 = 1) :
    K.centered a = 0 := by
  have hs := K.centered_self_gram a
  rw [h, sub_self, dotProduct] at hs
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg (K.centered a y))).mp hs
  ext y
  simpa using hz y (Finset.mem_univ y)

theorem direction_gram_of_equal (a b : ι → Bool)
    (hab : K.eigenvalue a = K.eigenvalue b) :
    K.direction a ⬝ᵥ K.direction b =
      (K.eigenvalue (fun y => a y ^^ b y) - K.eigenvalue a ^ 2) /
        (1 - K.eigenvalue a ^ 2) := by
  have hs : K.sigma b = K.sigma a := by rw [sigma, sigma, ← hab]
  rw [K.direction_gram, hs, ← pow_two, K.sigma_sq, ← hab, ← pow_two]

theorem step_rotation_coin (a : ι → Bool) :
    K.step a K.coin = K.eigenvalue a • K.coin + K.sigma a • K.direction a := by
  by_cases hs : K.sigma a = 0
  · have he := K.sigma_sq a
    rw [hs, zero_pow (by decide : 2 ≠ 0)] at he
    have hc : K.signed a = K.eigenvalue a • K.coin :=
      sub_eq_zero.mp (K.centered_eq_zero_of_endpoint a (by linarith))
    simpa [K.step_coin, hs] using hc
  · rw [K.step_coin, direction, smul_smul, mul_inv_cancel₀ hs, one_smul, centered]
    abel

private theorem step_centered (a : ι → Bool) :
    K.step a (K.centered a) =
      -(1 - K.eigenvalue a ^ 2) • K.coin + K.eigenvalue a • K.centered a := by
  rw [centered, K.step_sub, K.step_smul, K.step_signed, K.step_coin]
  ext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem step_rotation_direction (a : ι → Bool) :
    K.step a (K.direction a) = (-K.sigma a) • K.coin + K.eigenvalue a • K.direction a := by
  by_cases hs : K.sigma a = 0
  · rw [direction, K.step_smul]
    simp [hs]
  · simp only [direction, K.step_smul, K.step_centered, ← K.sigma_sq, smul_add, smul_smul]
    ext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

theorem orbit_endpoint (a : ι → Bool) (h : K.eigenvalue a ^ 2 = 1) (n : ℕ) :
    K.orbit a n = (K.eigenvalue a ^ n) • K.coin := by
  have ha : K.signed a = K.eigenvalue a • K.coin :=
    sub_eq_zero.mp (K.centered_eq_zero_of_endpoint a h)
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit, Function.iterate_succ_apply', ← orbit, ih, K.step_smul, K.step_coin, ha,
      smul_smul, pow_succ]

theorem orbit_rotation (a : ι → Bool) (n : ℕ) :
    K.orbit a n = Real.cos (n * K.angle a) • K.coin +
      Real.sin (n * K.angle a) • K.direction a := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit, Function.iterate_succ_apply', ← orbit, ih, K.step_add, K.step_smul,
      K.step_smul, K.step_rotation_coin, K.step_rotation_direction]
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add, K.cos_angle, K.sin_angle]
    ext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

end Kernel
end HypercubeWalsh

end

section

/-! Time averages of the actual continuous and discrete block orbits. -/

open Filter
open scoped BigOperators Matrix Topology Interval

set_option autoImplicit false

namespace HypercubeWalsh

noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] private theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] private theorem phase_re (t : ℝ) : (phase t).re = Real.cos t :=
  Complex.exp_ofReal_mul_I_re t

@[simp] private theorem phase_im (t : ℝ) : (phase t).im = Real.sin t :=
  Complex.exp_ofReal_mul_I_im t

@[simp] private theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_neg (t : ℝ) : phase (-t) = (starRingEnd ℂ) (phase t) := by
  apply Complex.ext
  · simp [Real.cos_neg]
  · simp [Real.sin_neg]

private theorem phase_sub_eq_one_iff (s t : ℝ) : phase (s - t) = 1 ↔ phase s = phase t := by
  simp only [phase, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
    div_eq_iff (Complex.exp_ne_zero _), one_mul]

private theorem phase_nat_mul (n : ℕ) (t : ℝ) : phase (n * t) = phase t ^ n := by
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul]

noncomputable def discreteMean (f : ℕ → ℝ) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, f n

noncomputable def continuousMean (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  T⁻¹ • ∫ t in (0 : ℝ)..T, f t

private theorem tendsto_geometric_mean (z : ℂ) (hz : ‖z‖ = 1) :
    Tendsto (fun T : ℕ => (∑ n ∈ Finset.range T, z ^ n) / (T : ℂ)) atTop
      (𝓝 (if z = 1 then 1 else 0)) := by
  split_ifs with h
  · rw [h]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hn']
  · apply squeeze_zero_norm (a := fun T : ℕ => (2 / ‖z - 1‖) / T) _
      (tendsto_const_div_atTop_nhds_zero_nat _)
    intro T
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr h
    have hs : (∑ n ∈ Finset.range T, z ^ n) = (z ^ T - 1) / (z - 1) :=
      (eq_div_iff hne).2 (geom_sum_mul z T)
    rw [hs, norm_div, norm_div, Complex.norm_natCast]
    gcongr
    calc
      ‖z ^ T - 1‖ ≤ ‖z ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hz, one_add_one_eq_two]

private theorem tendsto_cosine_mean (θ : ℝ) :
    Tendsto (discreteMean (fun n => Real.cos (n * θ))) atTop
      (𝓝 (if phase θ = 1 then 1 else 0)) := by
  have h := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_geometric_mean (phase θ) (norm_phase θ))
  have he (T : ℕ) :
      ((∑ n ∈ Finset.range T, phase θ ^ n) / (T : ℂ)).re =
        discreteMean (fun n => Real.cos (n * θ)) T := by
    rw [div_eq_inv_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    congr 1
    simp only [Complex.re_sum, ← phase_nat_mul, phase_re]
  simp only [Function.comp_def, he] at h
  by_cases hp : phase θ = 1 <;> simpa [hp] using h

private theorem tendsto_continuous_phase_mean (ω : ℝ) :
    Tendsto (continuousMean (fun t => phase (ω * t))) atTop
      (𝓝 (if ω = 0 then 1 else 0)) := by
  split_ifs with h
  · subst ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp [continuousMean, intervalIntegral.integral_const, hT.ne']
  · let c : ℂ := (ω : ℂ) * Complex.I
    have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr h) Complex.I_ne_zero
    have hint (T : ℝ) : (∫ t in (0 : ℝ)..T, phase (ω * t)) = (phase (ω * T) - 1) / c := by
      have he (t : ℝ) : phase (ω * t) = Complex.exp (c * t) := by
        unfold phase c
        push_cast
        ring_nf
      simpa only [← he, mul_zero, Complex.ofReal_zero, Complex.exp_zero] using
        (integral_exp_mul_complex (a := 0) (b := T) hc)
    have hlim : Tendsto (fun T : ℝ => (2 / ‖c‖) * T⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.const_mul (2 / ‖c‖))
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [continuousMean, hint, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT),
      norm_div, mul_comm ((T : ℝ)⁻¹)]
    gcongr
    calc
      ‖phase (ω * T) - 1‖ ≤ ‖phase (ω * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [one_add_one_eq_two]

noncomputable def continuousBlock (α t : ℝ) : ℂ := phase ((α - 1) * t)

noncomputable def continuousPair (α β t : ℝ) : ℂ :=
  (starRingEnd ℂ) (continuousBlock α t) * continuousBlock β t

theorem continuousPair_eq (α β t : ℝ) :
    continuousPair α β t = phase ((β - α) * t) := by
  rw [continuousPair, continuousBlock, continuousBlock, ← phase_neg, ← phase_add]
  congr 1
  ring

theorem tendsto_continuousPair (α β : ℝ) :
    Tendsto (continuousMean (continuousPair α β)) atTop (𝓝 (if α = β then 1 else 0)) := by
  rw [show continuousPair α β = (fun t => phase ((β - α) * t)) from funext (continuousPair_eq α β)]
  simpa [sub_eq_zero, eq_comm] using tendsto_continuous_phase_mean (β - α)

namespace Kernel

variable {ι : Type*} [Fintype ι] (K : Kernel ι)

noncomputable def discretePair (a b : ι → Bool) (n : ℕ) : ℝ :=
  K.orbit a n ⬝ᵥ K.orbit b n

noncomputable def pairGram (a b : ι → Bool) : ℝ := K.direction a ⬝ᵥ K.direction b

noncomputable def continuousLimit (a b : ι → Bool) : ℝ :=
  if K.eigenvalue a = K.eigenvalue b then 1 else 0

noncomputable def discreteLimit (a b : ι → Bool) : ℝ :=
  if K.eigenvalue a = K.eigenvalue b then
    if |K.eigenvalue a| < 1 then (1 + K.pairGram a b) / 2 else 1
  else 0

noncomputable def pairGap (a b : ι → Bool) : ℝ :=
  if K.eigenvalue a = K.eigenvalue b ∧ |K.eigenvalue a| < 1 then
    (1 - K.eigenvalue (fun y => a y ^^ b y)) / (2 * (1 - K.eigenvalue a ^ 2))
  else 0

private theorem discretePair_eq (a b : ι → Bool) (n : ℕ) :
    K.discretePair a b n =
      (1 + K.pairGram a b) / 2 * Real.cos (n * (K.angle a - K.angle b)) +
      (1 - K.pairGram a b) / 2 * Real.cos (n * (K.angle a + K.angle b)) := by
  rw [discretePair, K.orbit_rotation, K.orbit_rotation]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, coin_gram,
    coin_direction_gram, direction_coin_gram, smul_eq_mul, mul_one, mul_zero, zero_add,
    add_zero, pairGram, mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  ring

private theorem phase_angle_sub (a b : ι → Bool) :
    phase (K.angle a - K.angle b) = 1 ↔ K.eigenvalue a = K.eigenvalue b := by
  rw [phase_sub_eq_one_iff]
  constructor
  · intro h
    simpa using congrArg Complex.re h
  · intro h
    simp [angle, h]

private theorem phase_angle_add_eq (a b : ι → Bool) (h : phase (K.angle a + K.angle b) = 1) :
    K.eigenvalue a = K.eigenvalue b ∧ K.sigma a = -K.sigma b := by
  rw [← sub_neg_eq_add, phase_sub_eq_one_iff] at h
  exact ⟨by simpa [Real.cos_neg] using congrArg Complex.re h,
    by simpa [Real.sin_neg] using congrArg Complex.im h⟩

theorem tendsto_discretePair (a b : ι → Bool) :
    Tendsto (discreteMean (K.discretePair a b)) atTop (𝓝 (K.discreteLimit a b)) := by
  have hminus := tendsto_cosine_mean (K.angle a - K.angle b)
  have hplus := tendsto_cosine_mean (K.angle a + K.angle b)
  have hmain := (hminus.const_mul ((1 + K.pairGram a b) / 2)).add
    (hplus.const_mul ((1 - K.pairGram a b) / 2))
  have hmean (T : ℕ) :
      discreteMean (K.discretePair a b) T =
        (1 + K.pairGram a b) / 2 *
        discreteMean (fun n => Real.cos (n * (K.angle a - K.angle b))) T +
        (1 - K.pairGram a b) / 2 *
        discreteMean (fun n => Real.cos (n * (K.angle a + K.angle b))) T := by
    simp only [discreteMean, K.discretePair_eq, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  by_cases he : K.eigenvalue a = K.eigenvalue b
  · by_cases hi : |K.eigenvalue a| < 1
    · have hp : phase (K.angle a + K.angle b) ≠ 1 := by
        intro h
        have hs := (K.phase_angle_add_eq a b h).2
        have hσ : K.sigma a = K.sigma b := by simp [sigma, he]
        linarith [K.sigma_pos a hi]
      rw [discreteLimit, ite_eq_left he, ite_eq_left hi]
      simpa only [K.phase_angle_sub, ite_eq_left he, ite_eq_right hp, mul_one, mul_zero, add_zero,
        ← hmean] using hmain
    · have hend : K.eigenvalue a ^ 2 = 1 := by
        rcases K.eigenvalue_bounds a with ⟨h₁, h₂⟩
        have ha : |K.eigenvalue a| = 1 := le_antisymm (abs_le.2 ⟨h₁,h₂⟩) (le_of_not_gt hi)
        calc
          K.eigenvalue a ^ 2 = |K.eigenvalue a| ^ 2 := (sq_abs _).symm
          _ = 1 := by rw [ha, one_pow]
      have hend' : K.eigenvalue b ^ 2 = 1 := he ▸ hend
      have hpair (n : ℕ) : K.discretePair a b n = 1 := by
        rw [discretePair, K.orbit_endpoint a hend, K.orbit_endpoint b hend', ← he,
          smul_dotProduct, dotProduct_smul, K.coin_gram, smul_eq_mul, smul_eq_mul, mul_one,
          ← pow_two, ← pow_mul, mul_comm n, pow_mul, hend, one_pow]
      rw [discreteLimit, ite_eq_left he, ite_eq_right hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
      have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      simp [discreteMean, hpair, hT']
  · have hp : phase (K.angle a + K.angle b) ≠ 1 := fun h => he (K.phase_angle_add_eq a b h).1
    simpa [K.phase_angle_sub, he, hp, discreteLimit, ← hmean] using hmain

theorem pair_limit_sub (a b : ι → Bool) :
    K.continuousLimit a b - K.discreteLimit a b = K.pairGap a b := by
  by_cases he : K.eigenvalue a = K.eigenvalue b
  · by_cases hi : |K.eigenvalue a| < 1
    · have hd : 1 - K.eigenvalue a ^ 2 ≠ 0 := by
        rw [← K.sigma_sq]
        exact pow_ne_zero 2 (K.sigma_pos a hi).ne'
      rw [continuousLimit, ite_eq_left he, discreteLimit, ite_eq_left he, ite_eq_left hi,
        pairGap, ite_eq_left ⟨he, hi⟩]
      rw [pairGram, K.direction_gram_of_equal a b he]
      field_simp
      ring
    · rw [continuousLimit, ite_eq_left he, discreteLimit, ite_eq_left he, ite_eq_right hi,
        pairGap, ite_eq_right (fun h => hi h.2), sub_self]
  · simp [continuousLimit, discreteLimit, pairGap, he]

theorem pairGap_mem_Icc (a b : ι → Bool) : K.pairGap a b ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : K.eigenvalue a = K.eigenvalue b ∧ |K.eigenvalue a| < 1
  · have hb : |K.eigenvalue b| < 1 := h.1 ▸ h.2
    have hsq (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
      Finset.sum_nonneg (fun y _ => mul_self_nonneg (v y))
    have hminus := hsq (K.direction a - K.direction b)
    have hplus := hsq (K.direction a + K.direction b)
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, K.direction_self_gram a h.2,
      K.direction_self_gram b hb, dotProduct_comm (K.direction b) (K.direction a)] at hminus
    rw [add_dotProduct, dotProduct_add, dotProduct_add, K.direction_self_gram a h.2,
      K.direction_self_gram b hb, dotProduct_comm (K.direction b) (K.direction a)] at hplus
    rw [← K.pair_limit_sub, continuousLimit, ite_eq_left h.1, discreteLimit, ite_eq_left h.1,
      ite_eq_left h.2, pairGram]
    constructor <;> linarith
  · simp [pairGap, h]

end Kernel
end HypercubeWalsh

end
