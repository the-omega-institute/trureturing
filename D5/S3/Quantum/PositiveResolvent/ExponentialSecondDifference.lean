/- GID: D5/S3/Quantum/PositiveResolvent/ExponentialSecondDifference
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact exponential second differences, their evaluation, and symmetric scaling laws. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Set intervalIntegral Real
open MeasureTheory (volume)
open scoped Topology

namespace D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference

noncomputable def Q (x y z : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
    s * Real.exp (-((1 - s) * Real.log x + s * (1 - t) * Real.log y + s * t * Real.log z))

private noncomputable def rawQ (a b c : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
    s * Real.exp (-((1 - s) * a + s * (1 - t) * b + s * t * c))

private lemma rawQ_continuous : Continuous (fun p : ℝ × ℝ × ℝ => rawQ p.1 p.2.1 p.2.2) := by
  unfold rawQ
  apply continuous_parametric_intervalIntegral_of_continuous'
  apply continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

private lemma inner_integral (a b c s : ℝ) (hbc : b ≠ c) :
    (∫ t in (0 : ℝ)..1, s * Real.exp (-((1 - s) * a + s * (1 - t) * b + s * t * c))) =
      (Real.exp (-((1 - s) * a + s * c)) - Real.exp (-((1 - s) * a + s * b))) / (b - c) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hsc : s * (b - c) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr hbc)
  have hcomp := intervalIntegral.integral_comp_add_mul Real.exp hsc
      (-((1 - s) * a + s * b)) (a := (0 : ℝ)) (b := 1)
  have hrewrite :
      (fun t : ℝ => s * Real.exp (-((1 - s) * a + s * (1 - t) * b + s * t * c))) =
        (fun t => s * Real.exp (-((1 - s) * a + s * b) + (s * (b - c)) * t)) := by
    funext t
    congr 2
    ring
  rw [hrewrite]
  rw [integral_const_mul, hcomp, integral_exp]
  simp only [smul_eq_mul, mul_sub, mul_zero, add_zero, sub_zero, mul_one]
  field_simp [hsc, sub_ne_zero.mpr hbc]
  ring

private lemma affine_exp_integral (a b : ℝ) (hab : a ≠ b) :
    (∫ s in (0 : ℝ)..1, Real.exp (-((1-s)*a+s*b))) =
      (Real.exp (-b) - Real.exp (-a)) / (a-b) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hcomp := intervalIntegral.integral_comp_add_mul Real.exp hab'
      (-a) (a := (0 : ℝ)) (b := 1)
  have hrewrite :
      (fun s : ℝ => Real.exp (-((1-s)*a+s*b))) =
        (fun s => Real.exp (-a + (a - b) * s)) := by
    funext s
    congr 1
    ring
  rw [hrewrite, hcomp, integral_exp]
  simp only [smul_eq_mul, mul_sub, mul_zero, add_zero, sub_zero, mul_one]
  field_simp [hab']
  ring

private lemma rawQ_eq_of_ne (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rawQ a b c =
      ((b-c)*Real.exp (-a) - (a-c)*Real.exp (-b) + (a-b)*Real.exp (-c)) /
        ((a-b)*(a-c)*(b-c)) := by
  unfold rawQ
  simp_rw [inner_integral a b c _ hbc]
  rw [integral_div]
  have hi (b : ℝ) : IntervalIntegrable (fun s : ℝ => Real.exp (-((1-s)*a+s*b))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_sub (hi c) (hi b), affine_exp_integral a c hac, affine_exp_integral a b hab]
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hac, sub_ne_zero.mpr hbc]
  ring

/-- The positive diagonal has the simplex mass one half. -/
theorem Q_self {r : ℝ} (hr : 0 < r) : Q r r r = 1 / (2 * r) := by
  have he : Real.exp (-Real.log r) = 1 / r := by simp [Real.exp_neg, Real.exp_log hr]
  unfold Q
  have hw (s t : ℝ) : (1-s)*Real.log r + s*(1-t)*Real.log r + s*t*Real.log r = Real.log r := by ring
  simp_rw [hw, he, integral_const, sub_zero, one_smul]
  rw [integral_mul_const, integral_id]
  norm_num
  ring

/-- Positive simultaneous rescaling gives degree minus one. -/
theorem Q_homog {c x y z : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Q (c*x) (c*y) (c*z) = c⁻¹ * Q x y z := by
  unfold Q
  simp_rw [Real.log_mul hc.ne' hx.ne', Real.log_mul hc.ne' hy.ne', Real.log_mul hc.ne' hz.ne']
  have hw (s t : ℝ) :
      -((1-s)*(Real.log c+Real.log x)+s*(1-t)*(Real.log c+Real.log y)+s*t*(Real.log c+Real.log z)) =
      -Real.log c + -((1-s)*Real.log x+s*(1-t)*Real.log y+s*t*Real.log z) := by ring
  simp_rw [hw, Real.exp_add, Real.exp_neg (Real.log c), Real.exp_log hc]
  have hm (s t : ℝ) : s * (c⁻¹ * Real.exp (-((1-s)*Real.log x+s*(1-t)*Real.log y+s*t*Real.log z))) =
      c⁻¹ * (s * Real.exp (-((1-s)*Real.log x+s*(1-t)*Real.log y+s*t*Real.log z))) := by ring
  simp_rw [hm, integral_const_mul]

/-- The distinct-node Hermite–Genocchi evaluation in logarithmic coordinates. -/
theorem Q_eq_of_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Q x y z =
      ((Real.log y-Real.log z)/x - (Real.log x-Real.log z)/y + (Real.log x-Real.log y)/z) /
        ((Real.log x-Real.log y)*(Real.log x-Real.log z)*(Real.log y-Real.log z)) := by
  have hn {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) : Real.log x ≠ Real.log y := by
    exact fun h => hxy (Real.log_injOn_pos hx hy h)
  change rawQ (Real.log x) (Real.log y) (Real.log z) = _
  rw [rawQ_eq_of_ne _ _ _ (hn hx hy hxy) (hn hx hz hxz) (hn hy hz hyz)]
  simp only [Real.exp_neg, Real.exp_log hx, Real.exp_log hy, Real.exp_log hz, div_eq_mul_inv]

private lemma rawQ_symm (a b c : ℝ) : rawQ a b c = rawQ b a c := by
  have houter : (fun b : ℝ => rawQ a b c) = (fun b : ℝ => rawQ b a c) := by
    apply Continuous.ext_on (dense_univ.sdiff_finite (Set.finite_singleton c))
      (rawQ_continuous.comp (show Continuous (fun b : ℝ => (a,b,c)) by fun_prop))
      (rawQ_continuous.comp (show Continuous (fun b : ℝ => (b,a,c)) by fun_prop))
    intro b hb
    have hbc : b ≠ c := by simpa using hb.2
    have hinner : (fun a : ℝ => rawQ a b c) = (fun a : ℝ => rawQ b a c) := by
      apply Continuous.ext_on (dense_univ.sdiff_finite (Set.toFinite ({b, c} : Set ℝ)))
        (rawQ_continuous.comp (show Continuous (fun a : ℝ => (a,b,c)) by fun_prop))
        (rawQ_continuous.comp (show Continuous (fun a : ℝ => (b,a,c)) by fun_prop))
      intro a ha
      have hne : a ≠ b ∧ a ≠ c := by simpa using ha.2
      have hab := hne.1
      have hac := hne.2
      change rawQ a b c = rawQ b a c
      rw [rawQ_eq_of_ne a b c hab hac hbc, rawQ_eq_of_ne b a c hab.symm hbc hac]
      field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hac, sub_ne_zero.mpr hbc,
        sub_ne_zero.mpr hab.symm]
      ring
    exact congrFun hinner a
  exact congrFun houter b

/-- Swapping the first two coordinates preserves the compact integral. -/
theorem Q_symm (x y z : ℝ) : Q x y z = Q y x z :=
  rawQ_symm (Real.log x) (Real.log y) (Real.log z)

/-- Swapping the last two coordinates preserves the compact integral. -/
theorem Q_symm_right (x y z : ℝ) : Q x y z = Q x z y := by
  unfold Q
  apply integral_congr
  intro s hs
  dsimp only
  have h := integral_comp_sub_left
    (fun t : ℝ => s * Real.exp (-((1-s)*Real.log x+s*(1-t)*Real.log y+s*t*Real.log z)))
    (a := (0 : ℝ)) (b := 1) 1
  norm_num only [sub_self, sub_zero] at h
  rw [← h]
  apply integral_congr
  intro t ht
  ring

/-- Joint continuity includes all positive coincidences. -/
theorem Q_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => Q p.1 p.2.1 p.2.2) (x,y,z) := by
  change ContinuousAt (fun p : ℝ × ℝ × ℝ => rawQ (Real.log p.1) (Real.log p.2.1) (Real.log p.2.2)) (x,y,z)
  apply rawQ_continuous.continuousAt.comp (f := fun p : ℝ × ℝ × ℝ =>
    (Real.log p.1, Real.log p.2.1, Real.log p.2.2))
  have hid : ContinuousAt (fun p : ℝ × ℝ × ℝ => p) (x,y,z) := continuousAt_id
  have h1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.log p.1) (x,y,z) :=
    hid.fst.log hx.ne'
  have h2 : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.log p.2.1) (x,y,z) :=
    hid.snd.fst.log hy.ne'
  have h3 : ContinuousAt (fun p : ℝ × ℝ × ℝ => Real.log p.2.2) (x,y,z) :=
    hid.snd.snd.log hz.ne'
  exact h1.prodMk (h2.prodMk h3)

end D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference
