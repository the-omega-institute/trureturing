/- GID: D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant
   generality: G
   mirror-B: D5/B/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: The optimal scalar hyperbolic comparison constant is one over square root two. -/

import D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import D5.S3.Weil.Budget.LinearCayleyScaleFlow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! The sharp scalar hyperbolic estimate, including all real signs and optimality. -/

open Set Filter
open scoped Topology
noncomputable section
namespace D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant

noncomputable def cothR (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
noncomputable def lhs (a b : ℝ) : ℝ :=
  |cothR ((a - b) / 2) * (a * cothR (a / 2) - b * cothR (b / 2))|
noncomputable def radicand (a b : ℝ) : ℝ :=
  a * b * (a - b) * cothR (a / 2) * cothR (b / 2) * cothR ((a - b) / 2)
def claim : Prop :=
  (∀ a b : ℝ, a ≠ 0 → b ≠ 0 → a ≠ b →
      lhs a b ≤ (1 / Real.sqrt 2) * Real.sqrt (radicand a b)) ∧
  ∀ C : ℝ, C < 1 / Real.sqrt 2 →
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ C * Real.sqrt (radicand a b) < lhs a b

open D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic

private def u (x : ℝ) : ℝ := if x = 0 then 1 else x * cothR x
private lemma u_eq {x : ℝ} (hx : x ≠ 0) : u x = x * cothR x := by simp [u, hx]
private lemma u_zero : u 0 = 1 := by simp [u]
private lemma u_even (x : ℝ) : u (-x) = u x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [u, hx, cothR, Real.cosh_neg, Real.sinh_neg, div_neg]
private lemma u_continuous : Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hs := (Real.hasDerivAt_sinh 0).continuousAt_div
    have hs' : ContinuousAt (fun x : ℝ => if x = 0 then 1 else Real.sinh x / x) 0 := by
      convert hs using 1
      ext y
      by_cases hy : y = 0
      · simp [hy, Function.update]
      · simp [hy, Function.update]
    have hi := Real.continuous_cosh.continuousAt.mul (hs'.inv₀ (by simp))
    convert hi using 1
    ext y
    by_cases hy : y = 0
    · simp [hy, u]
    · simp [u, hy, cothR, div_eq_mul_inv]
      ring
  · have he : u =ᶠ[𝓝 x] (fun y => y * cothR y) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact u_eq hy
    exact ContinuousAt.congr ((continuousAt_id.mul
      (Real.continuous_cosh.continuousAt.div Real.continuous_sinh.continuousAt
        (Real.sinh_ne_zero.mpr hx)))) he.symm
private lemma u_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt u ((Real.sinh x * Real.cosh x - x) / Real.sinh x ^ 2) x := by
  have hd := f_hasDerivAt (s := 1) (r := x) (by norm_num) hx
  have he : u =ᶠ[𝓝 x] f 1 := by
    filter_upwards [eventually_ne_nhds hx.ne'] with y hy
    simp [u_eq hy, cothR, f, mul_div_assoc]
  simpa using hd.congr_of_eventuallyEq he
private lemma u_mono : MonotoneOn u (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _) u_continuous.continuousOn
  · intro x hx
    have hx' : 0 < x := by simpa using hx
    exact (u_hasDerivAt hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa using hx
    rw [(u_hasDerivAt hx').deriv]
    exact div_nonneg (sinh_cosh_sub_pos hx').le (sq_nonneg _)
private lemma u_one_le (x : ℝ) : 1 ≤ u x := by
  by_cases hx : x = 0
  · simp [hx, u_zero]
  have hpos : 0 < |x| := abs_pos.mpr hx
  have h : 1 ≤ u |x| := by
    simpa [u_eq hpos.ne', cothR,
      D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.coth] using
      D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.one_le_self_mul_coth hpos
  rcases le_total 0 x with hx | hx
  · simpa [abs_of_nonneg hx] using h
  · simpa [abs_of_nonpos hx, u_even] using h
private lemma u_pos (x : ℝ) : 0 < u x := lt_of_lt_of_le zero_lt_one (u_one_le x)
private lemma u_deriv_le_one {x : ℝ} (hx : 0 < x) : deriv u x ≤ 1 := by
  rw [(u_hasDerivAt hx).deriv]
  apply (div_le_iff₀ (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx))).mpr
  have he := Real.add_one_le_exp (-2*x)
  have hid : 2 * (Real.sinh x * Real.cosh x - Real.sinh x ^ 2) = 1 - Real.exp (-2*x) := by
    calc
      _ = (Real.cosh x - Real.sinh x) * (Real.cosh x + Real.sinh x) -
          (Real.cosh x - Real.sinh x)^2 := by ring
      _ = 1 - Real.exp (-2*x) := by
        rw [Real.cosh_sub_sinh, Real.cosh_add_sinh, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, ← Real.exp_nat_mul]
        congr 1
        congr 1
        ring
  nlinarith
private lemma u_lipschitz {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    u A - u B ≤ A - B := by
  have h := (convex_Ici (0:ℝ)).image_sub_le_mul_sub_of_deriv_le
    u_continuous.continuousOn
    (show DifferentiableOn ℝ u (interior (Ici 0)) from fun x hx =>
      (u_hasDerivAt (by simpa using hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => u_deriv_le_one (by simpa using hx)) B hB A (le_trans hB hBA) hBA
  simpa using h
private lemma psi_mono : MonotoneOn (fun x : ℝ => x * Real.tanh x) (Ici 0) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x * Real.tanh x)
      (Real.tanh x + x * (1 - Real.tanh x ^ 2)) x := by
    convert (hasDerivAt_id x).mul
      (D5.S3.Weil.Budget.LinearCayleyScaleFlow.real_tanh_hasDerivAt x) using 1 <;> (first | rfl | simp)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
  · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 ≤ x := interior_subset hx
    rw [(hd x).deriv]
    have ht : 0 ≤ Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hx') (Real.cosh_pos x).le
    have ht' := Real.tanh_sq_lt_one x
    exact add_nonneg ht (mul_nonneg hx' (sub_nonneg.mpr ht'.le))

/-- The completed cotangent profile and its reciprocal profile multiply to a square. -/
private lemma u_psi (x : ℝ) : u x * (x * Real.tanh x) = x^2 := by
  by_cases hx : x=0
  · simp [hx]
  rw [u_eq hx, cothR, Real.tanh_eq_sinh_div_cosh]
  field_simp [Real.sinh_ne_zero.mpr hx, (Real.cosh_pos x).ne']

private lemma u_abs (x : ℝ) : u |x| = u x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, u_even]

private lemma comparison_ordered {A B D : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A)
    (hD : A - B ≤ D) :
    (u A-u B)^2 ≤ (D * Real.tanh D) * u A * u B := by
  have hA : 0 ≤ A := hB.trans hBA
  have hδ : 0 ≤ A-B := sub_nonneg.mpr hBA
  have hDn : 0 ≤ D := hδ.trans hD
  have hv : 0 ≤ u A-u B := sub_nonneg.mpr (u_mono hB hA hBA)
  have hv' := u_lipschitz hB hBA
  have hsmall : u (A-B) ≤ u A := u_mono hδ hA (by linarith)
  have hprod : u (A-B) ≤ u A*u B := by
    nlinarith [u_pos A, u_one_le B]
  have hψ : 0 ≤ (A-B) * Real.tanh (A-B) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact mul_nonneg hδ (div_nonneg (Real.sinh_nonneg_iff.mpr hδ) (Real.cosh_pos _).le)
  calc
    (u A-u B)^2 ≤ (A-B)^2 := by nlinarith
    _ = ((A-B) * Real.tanh (A-B)) * u (A-B) := by
      rw [mul_comm]; exact (u_psi (A-B)).symm
    _ ≤ ((A-B) * Real.tanh (A-B)) * (u A*u B) := mul_le_mul_of_nonneg_left hprod hψ
    _ ≤ (D * Real.tanh D) * (u A*u B) :=
      mul_le_mul_of_nonneg_right (psi_mono hδ hDn hD) (mul_pos (u_pos A) (u_pos B)).le
    _ = _ := by ring

/-- Absolute values reduce both signs to the ordered nonnegative comparison. -/
private lemma comparison (a b : ℝ) :
    (u a-u b)^2 ≤ ((a-b)*Real.tanh (a-b)) * u a * u b := by
  have hd : |a-b| * Real.tanh |a-b| = (a-b)*Real.tanh (a-b) := by
    rcases le_or_gt 0 (a-b) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.tanh_neg]; ring
  have ha := u_abs a
  have hb := u_abs b
  rcases le_total |b| |a| with h | h
  · have hh := comparison_ordered
      (abs_nonneg b) h (le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub a b))
    simpa only [ha, hb, hd] using hh
  · have hh := comparison_ordered
      (abs_nonneg a) h (le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub b a))
    rw [abs_sub_comm b a, ha, hb, hd] at hh
    nlinarith

/-- Half-argument substitution transfers the comparison to the original square roots. -/
private lemma upper (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    lhs a b ≤ (1/Real.sqrt 2)*Real.sqrt (radicand a b) := by
  let x := a/2
  let y := b/2
  let z := (a-b)/2
  have hux := u_pos x
  have huy := u_pos y
  have huz := u_pos z
  have hx : x≠0 := div_ne_zero ha (by norm_num)
  have hy : y≠0 := div_ne_zero hb (by norm_num)
  have hz : z≠0 := div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
  have hzxy : x-y=z := by dsimp [x,y,z]; ring
  have hr : radicand a b = 8*u x*u y*u z := by
    rw [u_eq hx,u_eq hy,u_eq hz]
    dsimp [x,y,z,radicand]
    ring
  have hl : lhs a b = 2*|u z*(u x-u y)/z| := by
    have hc : cothR z=u z/z := by rw [u_eq hz]; field_simp
    unfold lhs
    change |cothR z*(a*cothR x-b*cothR y)| = _
    rw [hc]
    have he : u z/z*(a*cothR x-b*cothR y) = 2*(u z*(u x-u y)/z) := by
      rw [u_eq hx,u_eq hy]; dsimp [x,y]; ring
    rw [he,abs_mul]; norm_num
  have hc := comparison x y
  rw [hzxy] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (u_pos z).le
  have hp := u_psi z
  have hmain : u z*(u x-u y)^2 ≤ z^2*u x*u y := by
    calc
      _ ≤ u z*((z*Real.tanh z)*u x*u y) := hc'
      _ = (u z*(z*Real.tanh z))*u x*u y := by ring
      _ = _ := by rw [hp]
  have hmain' := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 4*u z by positivity)
  have hlsq : (lhs a b)^2*z^2 = 4*(u z)^2*(u x-u y)^2 := by
    rw [hl]
    rw [mul_pow, sq_abs, div_pow]
    field_simp
    ring
  have hsquare : (lhs a b)^2 ≤ radicand a b/2 := by
    rw [hr]
    apply (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero hz)).mp
    nlinarith [hlsq]
  have hrpos : 0 < radicand a b := by rw [hr]; positivity
  have h2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hv : ((1/Real.sqrt 2)*Real.sqrt (radicand a b))^2=radicand a b/2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hrpos.le, h2]
    ring
  have hvp : 0 ≤ (1/Real.sqrt 2)*Real.sqrt (radicand a b) := by positivity
  nlinarith [abs_nonneg (cothR ((a-b)/2)*(a*cothR (a/2)-b*cothR (b/2)))]

private lemma self_le_u_pos (t : ℝ) (ht : 0 < t) : t ≤ u t := by
  rw [u_eq (x := t) ht.ne', cothR]
  have hs := Real.sinh_pos_iff.mpr ht
  have hc : Real.sinh t ≤ Real.cosh t := (Real.sinh_lt_cosh (x := t)).le
  have hh : 1 ≤ Real.cosh t / Real.sinh t := (le_div_iff₀ hs).mpr (by simpa using hc)
  nlinarith

/-- Continuity near zero and an explicit large argument give strict witnesses. -/
private lemma sharpness (hcont : Continuous u) (C : ℝ) (hC : C < 1 / Real.sqrt 2) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      C * Real.sqrt (radicand a b) < lhs a b := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hCs : C * Real.sqrt 2 < 1 := (lt_div_iff₀ hs).mp hC
  let t : ℝ := 2 / (1 - C * Real.sqrt 2)
  have ht : 0 < t := div_pos (by norm_num) (by linarith)
  have ht_eq : (1 - C * Real.sqrt 2) * t = 2 := by dsimp [t]; field_simp
  have hu : t ≤ u t := self_le_u_pos t ht
  have hup : 0 < u t := lt_of_lt_of_le ht hu
  let F : ℝ → ℝ := fun y =>
    u (t-y) * (u t-u y) - C*(t-y)*Real.sqrt (2*u t*u y*u (t-y))
  have hsqrt : Real.sqrt (2*u t*1*u t) = Real.sqrt 2*u t := by
    rw [show 2*u t*1*u t = 2*(u t)^2 by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hup.le]
  have hF0 : 0 < F 0 := by
    dsimp [F]
    simp only [sub_zero, show u 0 = 1 by simp [u]]
    rw [hsqrt]
    have hh : 0 < u t - 1 - C*t*Real.sqrt 2 := by nlinarith
    nlinarith [mul_pos hup hh]
  have hFc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop
  obtain ⟨δ,hδ,hδF⟩ := Metric.continuousAt_iff.mp hFc (F 0) hF0
  let y : ℝ := min δ t / 2
  have hy : 0 < y := div_pos (lt_min hδ ht) (by norm_num)
  have hyδ : y < δ := by dsimp [y]; linarith [min_le_left δ t]
  have hyt : y < t := by dsimp [y]; linarith [min_le_right δ t]
  have hFy : 0 < F y := by
    have hh := hδF (x := y) (by simpa [Real.dist_eq, abs_of_pos hy] using hyδ)
    rw [Real.dist_eq, abs_lt] at hh
    linarith [hh.1]
  have hz : 0 < t-y := sub_pos.mpr hyt
  have hcoth : cothR (t-y) = u (t-y)/(t-y) := by
    rw [u_eq (x := (t-y)) hz.ne']; field_simp
  have hleft : lhs (2*t) (2*y) =
      2*|u (t-y)*(u t-u y)/(t-y)| := by
    unfold lhs
    rw [show (2*t-2*y)/2=t-y by ring,
      show 2*t/2=t by ring, show 2*y/2=y by ring, hcoth]
    have hh : u (t-y)/(t-y)*(2*t*cothR t-2*y*cothR y) =
        2*(u (t-y)*(u t-u y)/(t-y)) := by
      rw [u_eq (x := t) ht.ne', u_eq (x := y) hy.ne']; ring
    rw [hh, abs_mul]; norm_num
  have hrad : radicand (2*t) (2*y) = 4*(2*u t*u y*u (t-y)) := by
    unfold radicand
    rw [show (2*t-2*y)/2=t-y by ring,
      show 2*t/2=t by ring, show 2*y/2=y by ring,
      u_eq (x := t) ht.ne', u_eq (x := y) hy.ne', u_eq (x := (t-y)) hz.ne']
    ring
  refine ⟨2*t,2*y,by positivity,by positivity,by linarith,?_⟩
  rw [hrad, Real.sqrt_mul (by norm_num), hleft]
  norm_num
  have hh : C * Real.sqrt (2*u t*u y*u (t-y)) <
      u (t-y)*(u t-u y)/(t-y) := by
    apply (lt_div_iff₀ hz).mpr
    dsimp [F] at hFy
    nlinarith
  have ha := le_abs_self (u (t-y)*(u t-u y)/(t-y))
  nlinarith

theorem result : claim := ⟨upper, sharpness u_continuous⟩

end D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
