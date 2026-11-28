import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

Exponential radial coordinates and exact one-dimensional comparison estimates.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set Filter
open scoped Topology

namespace OmegaMath.ExponentialRadialCoordinates

def profile (M r : ℝ) : ℝ := (1 - r / (2 * M)) * exp (r / (2 * M))

def coefficient (M r : ℝ) : ℝ := (32 * M ^ 3 / r) * exp (-r / (2 * M))

def leftCoordinate (M t r : ℝ) : ℝ :=
  -sqrt (r / (2 * M) - 1) * exp ((r - t) / (4 * M))

def rightCoordinate (M t r : ℝ) : ℝ :=
  sqrt (r / (2 * M) - 1) * exp ((r + t) / (4 * M))

theorem hasDerivAt_profile {M : ℝ} (hM : M ≠ 0) (r : ℝ) :
    HasDerivAt (profile M) (-r / (4 * M ^ 2) * exp (r / (2 * M))) r := by
  have h := (hasDerivAt_id r).div_const (2 * M)
  convert! (h.const_sub 1).mul h.exp using 1
  simp only [id_eq]
  field_simp
  ring

theorem analyticAt_profile (M r : ℝ) : AnalyticAt ℝ (profile M) r := by
  unfold profile
  fun_prop

theorem profile_zero (M : ℝ) : profile M 0 = 1 := by simp [profile]

theorem profile_boundary {M : ℝ} (hM : M ≠ 0) : profile M (2 * M) = 0 := by
  simp [profile, hM]

theorem strictAntiOn_profile {M : ℝ} (hM : 0 < M) :
    StrictAntiOn (profile M) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun r _ => (hasDerivAt_profile hM.ne' r).continuousAt.continuousWithinAt)
  intro r hr
  rw [interior_Ici] at hr
  rw [(hasDerivAt_profile hM.ne' r).deriv]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos hr) (by positivity))
    (exp_pos _)

theorem profile_lt_one {M r : ℝ} (hM : 0 < M) (hr : 0 < r) : profile M r < 1 := by
  simpa [profile_zero] using strictAntiOn_profile hM (by simp) hr.le hr

theorem profile_sign {M r : ℝ} (hM : 0 < M) :
    (0 < profile M r ↔ r < 2 * M) ∧
      (profile M r = 0 ↔ r = 2 * M) ∧ (profile M r < 0 ↔ 2 * M < r) := by
  have hp : 0 < exp (r / (2 * M)) := exp_pos _
  have hm : 0 < 2 * M := by positivity
  constructor
  · rw [profile, mul_pos_iff_of_pos_right hp, sub_pos, div_lt_one hm]
  constructor
  · rw [profile, mul_eq_zero, or_iff_left (ne_of_gt hp), sub_eq_zero,
      eq_comm, div_eq_one_iff_eq (ne_of_gt hm)]
  · simp only [profile, mul_neg_iff, hp, not_lt.mpr hp.le, and_false, false_or,
      and_true, sub_neg, one_lt_div hm]

theorem tendsto_profile {M : ℝ} (hM : 0 < M) :
    Tendsto (profile M) atTop atBot := by
  have ht : Tendsto (fun r : ℝ => r / (2 * M)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hn : Tendsto (fun r : ℝ => r / (2 * M) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) ht
  have he := tendsto_exp_atTop.comp ht
  have hh := hn.atTop_mul_atTop₀ he
  convert tendsto_neg_atTop_atBot.comp hh using 1
  ext r
  simp [profile]
  ring

theorem existsUnique_radius {M q : ℝ} (hM : 0 < M) (hq : q < 1) :
    ∃! r : ℝ, 0 < r ∧ profile M r = q := by
  have hs := intermediate_value_Ici' (a := (0 : ℝ))
    (f := profile M) (fun r _ => (analyticAt_profile M r).continuousAt.continuousWithinAt)
    (tendsto_profile hM)
  obtain ⟨r, hr, he⟩ := hs (show q ∈ Iic (profile M 0) by simpa [profile_zero] using hq.le)
  have hrp : 0 < r := by
    have : r ≠ 0 := by intro h; subst r; simpa [profile_zero] using he.trans_lt hq
    exact lt_of_le_of_ne hr (Ne.symm this)
  refine ⟨r, ⟨hrp, he⟩, ?_⟩
  intro s hs
  exact (strictAntiOn_profile hM).injOn hs.1.le hr (hs.2.trans he.symm)

theorem bijOn_profile {M : ℝ} (hM : 0 < M) :
    BijOn (profile M) (Ioi 0) (Iio 1) := by
  refine ⟨fun r hr => profile_lt_one hM hr,
    (strictAntiOn_profile hM).injOn.mono Ioi_subset_Ici_self, ?_⟩
  intro q hq
  obtain ⟨r, hr, _⟩ := existsUnique_radius hM hq
  exact ⟨r, hr⟩

theorem exists_analytic_inverse {M r : ℝ} (hM : M ≠ 0) (hr : r ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g (profile M r) ∧
      (∀ᶠ s in 𝓝 r, g (profile M s) = s) ∧
      (∀ᶠ q in 𝓝 (profile M r), profile M (g q) = q) ∧
      HasDerivAt g (-r / (4 * M ^ 2) * exp (r / (2 * M)))⁻¹ (profile M r) := by
  have ha := analyticAt_profile M r
  have hn : deriv (profile M) r ≠ 0 := by
    rw [(hasDerivAt_profile hM r).deriv]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hr) (by positivity)) (exp_ne_zero _)
  refine ⟨_, ha.analyticAt_localInverse hn, ha.hasStrictDerivAt.eventually_left_inverse hn,
    ha.hasStrictDerivAt.eventually_right_inverse hn, ?_⟩
  simpa [(hasDerivAt_profile hM r).deriv] using
    (ha.hasStrictDerivAt.to_localInverse hn).hasDerivAt

theorem coefficient_pos {M r : ℝ} (hM : 0 < M) (hr : 0 < r) :
    0 < coefficient M r := by unfold coefficient; positivity

theorem coefficient_boundary {M : ℝ} (hM : M ≠ 0) :
    coefficient M (2 * M) = 16 * M ^ 2 * exp (-1) := by
  unfold coefficient
  rw [show -(2 * M) / (2 * M) = -1 by field_simp]
  field_simp
  ring

private theorem exterior_factor_pos {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    0 < r / (2 * M) - 1 := by
  exact sub_pos.mpr ((one_lt_div (by positivity)).mpr hr)

theorem exterior_signs {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) (t : ℝ) :
    leftCoordinate M t r < 0 ∧ 0 < rightCoordinate M t r := by
  have hs := sqrt_pos.mpr (exterior_factor_pos hM hr)
  constructor
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (exp_pos _)
  · exact mul_pos hs (exp_pos _)

theorem exterior_product {M r : ℝ} (hM : 0 < M) (hr : 2 * M ≤ r) (t : ℝ) :
    leftCoordinate M t r * rightCoordinate M t r = profile M r := by
  have ha : 0 ≤ r / (2 * M) - 1 := by
    exact sub_nonneg.mpr ((one_le_div (by positivity)).mpr hr)
  have he : (r - t) / (4 * M) + (r + t) / (4 * M) = r / (2 * M) := by ring
  calc
    _ = -(sqrt (r / (2 * M) - 1) ^ 2) *
        exp ((r - t) / (4 * M) + (r + t) / (4 * M)) := by
      unfold leftCoordinate rightCoordinate
      rw [exp_add]
      ring
    _ = _ := by rw [sq_sqrt ha, he]; unfold profile; ring

theorem exterior_ratio {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) (t : ℝ) :
    rightCoordinate M t r / (-leftCoordinate M t r) = exp (t / (2 * M)) := by
  have hs := (sqrt_pos.mpr (exterior_factor_pos hM hr)).ne'
  have he : t / (2 * M) = (r + t) / (4 * M) - (r - t) / (4 * M) := by ring
  rw [he, exp_sub]
  unfold rightCoordinate leftCoordinate
  simp only [neg_mul, neg_neg]
  field_simp

/-- A logarithmic radial coordinate gives exponential expressions for both coordinates. -/
def logarithmicRadius (M r : ℝ) : ℝ := r + 2 * M * log (r / (2 * M) - 1)

theorem exterior_exponential_coordinates {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) (t : ℝ) :
    leftCoordinate M t r = -exp ((logarithmicRadius M r - t) / (4 * M)) ∧
    rightCoordinate M t r = exp ((logarithmicRadius M r + t) / (4 * M)) := by
  have ha := exterior_factor_pos hM hr
  have hs : sqrt (r / (2 * M) - 1) = exp (log (r / (2 * M) - 1) / 2) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos ha]
    congr 1
    ring
  have he (v : ℝ) : (logarithmicRadius M r + v) / (4 * M) =
      log (r / (2 * M) - 1) / 2 + (r + v) / (4 * M) := by
    unfold logarithmicRadius
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg (logarithmicRadius M r), he, exp_add, ← hs]
    simp [leftCoordinate, sub_eq_add_neg]
  · rw [he, exp_add, ← hs]
    rfl

theorem hasDerivAt_leftCoordinate {M s dt dr : ℝ} {t r : ℝ → ℝ}
    (hM : 0 < M) (hR : 2 * M < r s) (ht : HasDerivAt t dt s)
    (hr : HasDerivAt r dr s) :
    HasDerivAt (fun x => leftCoordinate M (t x) (r x))
      (leftCoordinate M (t s) (r s) *
        (r s * dr / (4 * M * (r s - 2 * M)) - dt / (4 * M))) s := by
  have ha := exterior_factor_pos hM hR
  have hs := (sqrt_pos.mpr ha).ne'
  have hd := (((hr.div_const (2 * M)).sub_const 1).sqrt ha.ne').neg.mul
    (((hr.sub ht).div_const (4 * M)).exp)
  convert! hd using 1
  dsimp [leftCoordinate]
  have hne : r s - 2 * M ≠ 0 := (sub_pos.mpr hR).ne'
  simp only [div_eq_mul_inv, mul_inv_rev, ← sqrt_div_self]
  have hne' : r s - M * 2 ≠ 0 := by simpa only [mul_comm M 2] using hne
  field_simp [hM.ne', ha.ne', hne]
  ring_nf

theorem hasDerivAt_rightCoordinate {M s dt dr : ℝ} {t r : ℝ → ℝ}
    (hM : 0 < M) (hR : 2 * M < r s) (ht : HasDerivAt t dt s)
    (hr : HasDerivAt r dr s) :
    HasDerivAt (fun x => rightCoordinate M (t x) (r x))
      (rightCoordinate M (t s) (r s) *
        (r s * dr / (4 * M * (r s - 2 * M)) + dt / (4 * M))) s := by
  have ha := exterior_factor_pos hM hR
  have hs := (sqrt_pos.mpr ha).ne'
  have hd := (((hr.div_const (2 * M)).sub_const 1).sqrt ha.ne').mul
    (((hr.add ht).div_const (4 * M)).exp)
  convert! hd using 1
  dsimp [rightCoordinate]
  have hne : r s - 2 * M ≠ 0 := (sub_pos.mpr hR).ne'
  simp only [div_eq_mul_inv, mul_inv_rev, ← sqrt_div_self]
  have hne' : r s - M * 2 ≠ 0 := by simpa only [mul_comm M 2] using hne
  field_simp [hM.ne', ha.ne', hne]
  ring_nf

theorem exterior_curve_identity {M s dt dr : ℝ} {t r : ℝ → ℝ}
    (hM : 0 < M) (hR : 2 * M < r s) (ht : HasDerivAt t dt s)
    (hr : HasDerivAt r dr s) :
    -coefficient M (r s) * deriv (fun x => leftCoordinate M (t x) (r x)) s *
        deriv (fun x => rightCoordinate M (t x) (r x)) s =
      -(1 - 2 * M / r s) * dt ^ 2 + (1 - 2 * M / r s)⁻¹ * dr ^ 2 := by
  rw [(hasDerivAt_leftCoordinate hM hR ht hr).deriv,
    (hasDerivAt_rightCoordinate hM hR ht hr).deriv]
  have hp := exterior_product hM hR.le (t s)
  have hm : M ≠ 0 := hM.ne'
  have hr0 : r s ≠ 0 := (lt_trans (by positivity : 0 < 2 * M) hR).ne'
  have hn : r s - 2 * M ≠ 0 := (sub_pos.mpr hR).ne'
  calc
    _ = -coefficient M (r s) * (leftCoordinate M (t s) (r s) *
        rightCoordinate M (t s) (r s)) *
        ((r s * dr / (4 * M * (r s - 2 * M))) ^ 2 - (dt / (4 * M)) ^ 2) := by ring
    _ = _ := by
      rw [hp]
      have ha : 1 - 2 * M / r s = (r s - 2 * M) / r s := by
        field_simp
        <;> ring
      rw [ha]
      unfold coefficient profile
      rw [show -r s / (2 * M) = -(r s / (2 * M)) by ring, exp_neg]
      have hn' : -(M * 2) + r s ≠ 0 := by simpa only [sub_eq_neg_add, mul_comm M 2] using hn
      have hn2 : -(M * r s * 4) + M ^ 2 * 4 + r s ^ 2 ≠ 0 := by
        convert pow_ne_zero 2 hn using 1 <;> ring
      field_simp [hm, hr0, hn]
      ring_nf
      field_simp [hn', hn2]
      ring_nf
      linear_combination 32 * r s ^ 2 * dr ^ 2 * (mul_inv_cancel₀ hn2)

theorem radius_derivative_of_equation {M s dr du dv : ℝ} {r u v : ℝ → ℝ}
    (hM : M ≠ 0) (hr : 0 < r s) (hd : HasDerivAt r dr s)
    (hu : HasDerivAt u du s) (hv : HasDerivAt v dv s)
    (he : ∀ᶠ x in 𝓝 s, profile M (r x) = u x * v x) :
    dr = -(4 * M ^ 2 / r s) * exp (-r s / (2 * M)) * (du * v s + u s * dv) := by
  have hh := (((hasDerivAt_profile hM (r s)).comp s hd).congr_of_eventuallyEq
    (he.mono fun _ h => h.symm)).unique (hu.mul hv)
  have hn : -r s / (4 * M ^ 2) * exp (r s / (2 * M)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hr.ne') (by positivity)) (exp_ne_zero _)
  calc
    dr = (du * v s + u s * dv) / (-r s / (4 * M ^ 2) * exp (r s / (2 * M))) := by
      apply (eq_div_iff hn).mpr
      nlinarith only [hh]
    _ = _ := by
      rw [show -r s / (2 * M) = -(r s / (2 * M)) by ring, exp_neg]
      field_simp

theorem radius_derivative_negative {M s dr du dv : ℝ} {r u v : ℝ → ℝ}
    (hM : 0 < M) (hr : 0 < r s) (hu0 : 0 < u s) (hv0 : 0 < v s)
    (hdu : 0 < du) (hdv : 0 < dv) (hd : HasDerivAt r dr s)
    (hu : HasDerivAt u du s) (hv : HasDerivAt v dv s)
    (he : ∀ᶠ x in 𝓝 s, profile M (r x) = u x * v x) : dr < 0 := by
  rw [radius_derivative_of_equation hM.ne' hr hd hu hv he]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity))
    (exp_pos _)) (by positivity)

theorem hyperbola_tangent_positive {a x y dx dy : ℝ} (ha : 0 < a)
    (he : x ^ 2 - y ^ 2 = a) (ht : x * dx - y * dy = 0) (hdy : dy ≠ 0) :
    0 < dy ^ 2 - dx ^ 2 := by
  have hi : x ^ 2 * (dy ^ 2 - dx ^ 2) = a * dy ^ 2 := by
    linear_combination dy ^ 2 * he - (x * dx + y * dy) * ht
  have hp : 0 < a * dy ^ 2 := mul_pos ha (sq_pos_of_ne_zero hdy)
  exact pos_of_mul_pos_right (hi.symm ▸ hp) (sq_nonneg x)

theorem radius_minimum {M r x : ℝ} (hM : 0 < M) (he : profile M r = -x ^ 2) :
    2 * M ≤ r ∧ (r = 2 * M ↔ x = 0) := by
  have hn : profile M r ≤ 0 := by rw [he]; nlinarith [sq_nonneg x]
  have hl : 2 * M ≤ r := by
    by_contra hh
    exact (not_lt_of_ge hn) ((profile_sign hM).1.mpr (lt_of_not_ge hh))
  refine ⟨hl, ?_⟩
  constructor
  · intro h; rw [h, profile_boundary hM.ne'] at he; nlinarith [sq_nonneg x]
  · intro h; apply (profile_sign hM).2.1.mp; simpa [h] using he

def cycloidalRadius (M η : ℝ) : ℝ := M * (1 + cos η)

def cycloidalTime (M η : ℝ) : ℝ := M * (η + sin η)

theorem hasDerivAt_cycloidalRadius (M η : ℝ) :
    HasDerivAt (cycloidalRadius M) (-M * sin η) η := by
  simpa [cycloidalRadius, mul_neg] using! ((hasDerivAt_cos η).const_add 1).const_mul M

theorem hasDerivAt_cycloidalTime (M η : ℝ) :
    HasDerivAt (cycloidalTime M) (M * (1 + cos η)) η := by
  simpa [cycloidalTime] using! ((hasDerivAt_id η).add (hasDerivAt_sin η)).const_mul M

theorem cycloidal_endpoints (M : ℝ) :
    cycloidalRadius M 0 = 2 * M ∧ cycloidalRadius M π = 0 ∧
      cycloidalTime M 0 = 0 ∧ cycloidalTime M π = π * M := by
  norm_num [cycloidalRadius, cycloidalTime, mul_comm, mul_two]

theorem cycloidal_interior {M η : ℝ} (hM : 0 < M) (hη : η ∈ Ioo 0 π) :
    0 < cycloidalRadius M η ∧ cycloidalRadius M η < 2 * M := by
  have hc : -1 < cos η := by
    simpa using cos_lt_cos_of_nonneg_of_le_pi hη.1.le le_rfl hη.2
  have hd : cos η < 1 := by
    simpa using cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by rfl) hη.2.le hη.1
  unfold cycloidalRadius
  constructor <;> nlinarith

theorem cycloidal_squared_ratio {M η : ℝ} (hM : 0 < M) (hη : η ∈ Ioo 0 π) :
    ((-M * sin η) / (M * (1 + cos η))) ^ 2 =
      2 * M / cycloidalRadius M η - 1 := by
  have hr := (cycloidal_interior hM hη).1.ne'
  unfold cycloidalRadius at *
  have hc : 1 + cos η ≠ 0 := (mul_ne_zero_iff.mp hr).2
  field_simp
  nlinarith [sin_sq_add_cos_sq η]

theorem normalized_derivative_bound {M r dt dr : ℝ}
    (hr : r ∈ Ioo 0 (2 * M)) (hd : dr ≤ 0)
    (hn : dr ^ 2 / (2 * M / r - 1) - (2 * M / r - 1) * dt ^ 2 = 1) :
    dr ≤ -sqrt (2 * M / r - 1) := by
  have ha : 0 < 2 * M / r - 1 := sub_pos.mpr ((one_lt_div hr.1).mpr hr.2)
  have he : dr ^ 2 = (1 + (2 * M / r - 1) * dt ^ 2) * (2 * M / r - 1) := by
    apply (div_eq_iff ha.ne').mp
    linarith only [hn]
  have hs := sq_sqrt ha.le
  have hp := sqrt_pos.mpr ha
  nlinarith only [he, hs, hp, hd, mul_nonneg ha.le (sq_nonneg dt), sq_nonneg (2 * M / r - 1)]

theorem weighted_inverse_derivative_bound {M r dt dr : ℝ}
    (hr : r ∈ Ioo 0 (2 * M)) (hd : dr ≤ 0)
    (hn : dr ^ 2 / (2 * M / r - 1) - (2 * M / r - 1) * dt ^ 2 = 1) :
    (-dr)⁻¹ ≤ sqrt (r / (2 * M - r)) := by
  have hb := normalized_derivative_bound hr hd hn
  have ha : 0 < 2 * M / r - 1 := sub_pos.mpr ((one_lt_div hr.1).mpr hr.2)
  have hs := sqrt_pos.mpr ha
  have hr0 : r ≠ 0 := hr.1.ne'
  have hh : sqrt (r / (2 * M - r)) = (sqrt (2 * M / r - 1))⁻¹ := by
    rw [← sqrt_inv]
    congr 1
    rw [show 2 * M / r - 1 = (2 * M - r) / r by field_simp]
    simp only [inv_div]
  rw [hh]
  exact (inv_le_inv₀ (by linarith : 0 < -dr) hs).mpr (by linarith)

theorem cycloidal_normalized_bound {M η dt dτ : ℝ} (hM : 0 < M)
    (hη : η ∈ Ioo 0 π)
    (hn : (-M * sin η) ^ 2 / (2 * M / cycloidalRadius M η - 1) -
      (2 * M / cycloidalRadius M η - 1) * dt ^ 2 = dτ ^ 2) :
    dτ ≤ cycloidalRadius M η := by
  have hr := cycloidal_interior hM hη
  have ha : 0 < 2 * M / cycloidalRadius M η - 1 :=
    sub_pos.mpr ((one_lt_div hr.1).mpr hr.2)
  have hi := cycloidal_squared_ratio hM hη
  rw [div_pow] at hi
  have he := (div_eq_iff (pow_ne_zero 2 hr.1.ne')).mp hi
  have hh : (-M * sin η) ^ 2 / (2 * M / cycloidalRadius M η - 1) =
      cycloidalRadius M η ^ 2 := by
    apply (div_eq_iff ha.ne').mpr
    nlinarith only [he]
  rw [hh] at hn
  nlinarith only [hn, hr.1, mul_nonneg ha.le (sq_nonneg dt)]

theorem cycloidal_time_bound {M : ℝ} {τ dτ : ℝ → ℝ}
    (hτ : ContinuousOn τ (Icc 0 π))
    (hd : ∀ η ∈ Ioo 0 π, HasDerivAt τ (dτ η) η)
    (hb : ∀ η ∈ Ioo 0 π, dτ η ≤ cycloidalRadius M η) :
    τ π - τ 0 ≤ π * M := by
  have hc : Continuous (cycloidalTime M) := by unfold cycloidalTime; fun_prop
  have hh (η : ℝ) (hη : η ∈ Ioo 0 π) :
      HasDerivAt (fun x => τ x - cycloidalTime M x)
        (dτ η - cycloidalRadius M η) η := by
    exact (hd η hη).sub (hasDerivAt_cycloidalTime M η)
  have ha : AntitoneOn (fun x => τ x - cycloidalTime M x) (Icc 0 π) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 π) (hτ.sub hc.continuousOn)
    · intro η hη
      rw [interior_Icc] at hη
      exact (hh η hη).differentiableAt.differentiableWithinAt
    · intro η hη
      rw [interior_Icc] at hη
      change deriv (fun x => τ x - cycloidalTime M x) η ≤ 0
      rw [(hh η hη).deriv]
      exact sub_nonpos.mpr (hb η hη)
  have h := ha (show 0 ∈ Icc (0 : ℝ) π by simp [pi_pos.le])
    (show π ∈ Icc (0 : ℝ) π by simp [pi_pos.le]) pi_pos.le
  obtain ⟨_, _, h0, hπ⟩ := cycloidal_endpoints M
  change τ π - cycloidalTime M π ≤ τ 0 - cycloidalTime M 0 at h
  rw [h0, hπ] at h
  linarith only [h]

theorem normalized_time_bound {M : ℝ} {τ dτ dt : ℝ → ℝ} (hM : 0 < M)
    (hτ : ContinuousOn τ (Icc 0 π))
    (hd : ∀ η ∈ Ioo 0 π, HasDerivAt τ (dτ η) η)
    (hn : ∀ η ∈ Ioo 0 π,
      (-M * sin η) ^ 2 / (2 * M / cycloidalRadius M η - 1) -
        (2 * M / cycloidalRadius M η - 1) * dt η ^ 2 = dτ η ^ 2) :
    τ π - τ 0 ≤ π * M :=
  cycloidal_time_bound hτ hd fun η hη => cycloidal_normalized_bound hM hη (hn η hη)

end OmegaMath.ExponentialRadialCoordinates
