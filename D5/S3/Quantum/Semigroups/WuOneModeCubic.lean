/- GID: D5/S3/Quantum/Semigroups/WuOneModeCubic
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuOneModeCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact one-mode premise of Wu's repeated-middle cubic inequality. -/

import D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The one-mode cubic deficit reduces to a scalar minimum at the Gibbs ratio.
Its derivative has the sign of a strictly increasing secant slope in the log ratio. -/

noncomputable section

open Set
open D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private gamma h c e bias gibbsLow gibbsHigh cutA cutB entropyPair from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

namespace D5.S3.Quantum.Semigroups.WuOneModeCubic

private def N (r t : ℝ) : ℝ :=
  (bias r + 2 * e r) * t^2 + (bias r - 4 * e r) * t + (bias r + 2 * e r)

private def Q (t : ℝ) : ℝ :=
  Real.log ((1 + t^3) / 2) - 3 * t^3 * Real.log t / (1 + t^3)

private def G (r t : ℝ) : ℝ :=
  h r / 2 + alpha r * Q t + cutA r 1 t / (2 * (1 + t^3)) -
    N r t ^ 2 / (8 * c r * (t + 1) * (1 + t^3))

private def P (r : ℝ) : ℝ :=
  (bias r ^ 2 - 8 * bias r * e r + 4 * c r ^ 2 - 20 * e r ^ 2) / (8 * c r)

private def R (r : ℝ) : ℝ :=
  (bias r ^ 2 + 4 * bias r * e r + 2 * c r ^ 2 + 22 * e r ^ 2) / (2 * c r)

private def S (r : ℝ) : ℝ := 3 * (bias r + 8 * e r)^2 / (8 * c r)

private theorem c_pos {r : ℝ} (hr : 1 ≤ r) : 0 < c r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  unfold c gamma
  positivity

private theorem coefficient_signs {r : ℝ} (hr : 1 ≤ r) :
    0 < P r ∧ 0 < R r ∧ 0 ≤ S r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hr1 : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hc := c_pos hr
  have he : 0 ≤ e r := by unfold e gamma; positivity
  have hb : 0 ≤ bias r := by unfold bias gamma; positivity
  have hce : 0 < c r - 3 * e r := by
    rw [show c r - 3 * e r = gamma r * r by unfold c e; ring]
    unfold gamma
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold P
    rw [show bias r ^ 2 - 8 * bias r * e r + 4 * c r ^ 2 - 20 * e r ^ 2 =
      (bias r - 4 * e r)^2 + 4 * (c r - 3 * e r) * (c r + 3 * e r) by ring]
    positivity
  · unfold R
    positivity
  · unfold S
    positivity

private theorem cutB_factor (r t : ℝ) : cutB r 1 t = (t - 1) * N r t := by
  unfold cutB N
  ring

private theorem entropy_scale {v w t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (hw : w = v * t) : entropyPair v w = (v^3 + w^3) * Q t := by
  subst w
  have hv3 : v^3 ≠ 0 := pow_ne_zero _ hv.ne'
  have ht3 : t^3 ≠ 0 := pow_ne_zero _ ht.ne'
  have hT : 1 + t^3 ≠ 0 := by positivity
  have hsum : (v^3 + (v * t)^3) / 2 = v^3 * ((1 + t^3) / 2) := by ring
  unfold entropyPair Q
  rw [hsum, Real.log_mul hv3 (by positivity), mul_pow, Real.log_mul hv3 ht3,
    Real.log_pow t 3]
  push_cast
  field_simp [hT]
  ring

private theorem complete_square {r v t : ℝ} (hr : 1 ≤ r) (hv : 0 < v) (ht : 1 < t)
    (z : ℝ) :
    oneModeDeficit r v (v * t) z =
      (v^3 + (v * t)^3) *
        (G r t + cutA r 1 t / (2 * (1 + t^3)) *
          (z + N r t / (2 * c r * (t - 1) * (t + 1)))^2) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht.ne'
  have htp : t + 1 ≠ 0 := by positivity
  have hT : 1 + t^3 ≠ 0 := by positivity
  unfold oneModeDeficit
  rw [entropy_scale hv ht0 rfl]
  have hA : cutA r v (v * t) = v^3 * cutA r 1 t := by unfold cutA; ring
  have hB : cutB r v (v * t) = v^3 * cutB r 1 t := by unfold cutB; ring
  rw [hA, hB, cutB_factor]
  unfold G cutA
  field_simp [(c_pos hr).ne', ht1, htp, hT]
  ring

private def laurent (r t : ℝ) : ℝ :=
  P r * (t^2 - t⁻¹ ^ 2) + R r * (t - t⁻¹) - S r * (t - 1) / (t + 1)

private theorem hasDerivAt_Q {t : ℝ} (ht : 0 < t) :
    HasDerivAt Q (-9 * t^2 * Real.log t / (1 + t^3)^2) t := by
  have hp : HasDerivAt (fun x : ℝ => x^3) (3 * t^2) t := by
    simpa using hasDerivAt_pow 3 t
  have hT : 1 + t^3 ≠ 0 := by positivity
  have hsum := hp.const_add 1
  have hlog := (Real.hasDerivAt_log (x := (1 + t^3) / 2) (by positivity)).comp t
    (hsum.div_const 2)
  have hlast := ((hp.const_mul 3).mul (Real.hasDerivAt_log ht.ne')).div hsum hT
  convert hlog.sub hlast using 1
  · rfl
  · simp only [Pi.mul_apply]
    field_simp [hT, ht.ne']
    ring

set_option maxHeartbeats 1800000 in
-- Clearing the quotient-rule denominators before collecting Laurent terms costs extra heartbeats.
private theorem hasDerivAt_G {r t : ℝ} (hr : 1 ≤ r) (ht : 0 < t) :
    HasDerivAt (G r) (t^2 / (1 + t^3)^2 * (laurent r t - 9 * alpha r * Real.log t)) t := by
  have hc := (c_pos hr).ne'
  have hp : HasDerivAt (fun x : ℝ => x^3) (3 * t^2) t := by
    simpa using hasDerivAt_pow 3 t
  have hT : 1 + t^3 ≠ 0 := by positivity
  have htp : t + 1 ≠ 0 := by positivity
  have hsum := hp.const_add 1
  have hi := hasDerivAt_id t
  have ha := (((hi.sub_const 1).pow 2).const_mul (c r)).mul (hi.add_const 1)
  have hn := (((hi.pow 2).const_mul (bias r + 2 * e r)).add
      (hi.const_mul (bias r - 4 * e r))).add_const (bias r + 2 * e r)
  have hden := ((hi.add_const 1).const_mul (8 * c r)).mul hsum
  have hrat := (hn.pow 2).div hden (by exact mul_ne_zero (mul_ne_zero (by positivity) htp) hT)
  have hcut := ha.div (hsum.const_mul 2) (mul_ne_zero (by norm_num) hT)
  convert (((hasDerivAt_Q ht).const_mul (alpha r)).const_add (h r / 2)).add hcut |>.sub hrat using 1
  · rfl
  · simp only [laurent, P, R, S, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, id_eq]
    field_simp [hc, hT, htp, ht.ne']
    ring

private theorem continuousOn_G {r : ℝ} (hr : 1 ≤ r) :
    ContinuousOn (G r) (Ioi 0) :=
  fun _ ht => (hasDerivAt_G hr ht).continuousAt.continuousWithinAt

-- The last quotient is tanh(x/2) in exponential coordinates.
private def D (r x : ℝ) : ℝ :=
  2 * P r * Real.sinh (2 * x) + 2 * R r * Real.sinh x -
    S r * ((Real.exp x - 1) / (Real.exp x + 1))

private def Dprime (r x : ℝ) : ℝ :=
  4 * P r * Real.cosh (2 * x) + 2 * R r * Real.cosh x -
    S r * (2 * Real.exp x / (Real.exp x + 1)^2)

private theorem hasDerivAt_D (r x : ℝ) : HasDerivAt (D r) (Dprime r x) x := by
  have hs := (Real.hasDerivAt_sinh (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
  have he := Real.hasDerivAt_exp x
  have hd := (he.sub_const 1).div (he.add_const 1) (by positivity)
  convert ((hs.const_mul (2 * P r)).add
    ((Real.hasDerivAt_sinh x).const_mul (2 * R r))).sub (hd.const_mul (S r)) using 1
  · rfl
  · simp only [Dprime]
    ring

private theorem hasDerivAt_Dprime (r x : ℝ) :
    HasDerivAt (Dprime r)
      (8 * P r * Real.sinh (2 * x) + 2 * R r * Real.sinh x +
        S r * (2 * Real.exp x * (Real.exp x - 1) / (Real.exp x + 1)^3)) x := by
  have hs := (Real.hasDerivAt_cosh (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
  have he := Real.hasDerivAt_exp x
  have hden : Real.exp x + 1 ≠ 0 := by positivity
  have hd := (he.const_mul 2).div ((he.add_const 1).pow 2) (pow_ne_zero _ hden)
  convert ((hs.const_mul (4 * P r)).add
    ((Real.hasDerivAt_cosh x).const_mul (2 * R r))).sub (hd.const_mul (S r)) using 1
  · rfl
  · simp only [Pi.pow_apply]
    field_simp [hden]
    ring

private theorem strictly_convex_D {r : ℝ} (hr : 1 ≤ r) :
    StrictConvexOn ℝ (Ici 0) (D r) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_D r x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    have hd : deriv (D r) = Dprime r := funext fun x => (hasDerivAt_D r x).deriv
    change 0 < deriv (deriv (D r)) x
    rw [hd, (hasDerivAt_Dprime r x).deriv]
    obtain ⟨hp, hR, hS⟩ := coefficient_signs hr
    have h₁ := Real.sinh_pos_iff.mpr hx
    have h₂ : 0 < Real.sinh (2 * x) := Real.sinh_pos_iff.mpr (by positivity)
    have h₃ : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
    positivity

private theorem D_zero (r : ℝ) : D r 0 = 0 := by simp [D]

private theorem D_log (r : ℝ) {t : ℝ} (ht : 0 < t) :
    D r (Real.log t) = laurent r t := by
  unfold D laurent
  simp only [Real.sinh_eq, Real.exp_neg, two_mul (Real.log t), Real.exp_add, Real.exp_log ht]
  rw [mul_inv]
  ring

private theorem alpha_log {r : ℝ} (hr : 1 < r) :
    alpha r * Real.log r = 3 * (r^2 - 1) / (4 * (r^2 + r + 1)) := by
  have hlog := (Real.log_pos hr).ne'
  rw [alpha, ite_eq_right hr.ne']
  field_simp [hlog]

set_option maxHeartbeats 1800000 in
-- Substitution of all three Laurent coefficients produces a high-degree polynomial identity.
private theorem laurent_gibbs {r : ℝ} (hr : 1 < r) :
    laurent r r = 9 * (alpha r * Real.log r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hT : 1 + r^3 ≠ 0 := by positivity
  have hU : r^2 + r + 1 ≠ 0 := by positivity
  have hplus : r + 1 ≠ 0 := by positivity
  rw [alpha_log hr]
  unfold laurent P R S bias e c gamma
  field_simp [hT, hU, hplus, hr0.ne']
  ring

private theorem cutB_gibbs {r : ℝ} (hr : 1 < r) : cutB r 1 r = 2 * cutA r 1 r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hU : r^2 + r + 1 ≠ 0 := by positivity
  unfold cutB cutA bias e c
  field_simp [hU]
  ring

private theorem G_gibbs {r : ℝ} (hr : 1 < r) : G r r = 0 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hT : 1 + r^3 ≠ 0 := by positivity
  have hU : r^2 + r + 1 ≠ 0 := by positivity
  have hplus : r + 1 ≠ 0 := by positivity
  have hc := (c_pos hr.le).ne'
  have hn : N r r = 2 * c r * (r - 1) * (r + 1) := by
    have hb := cutB_gibbs hr
    rw [cutB_factor, cutA] at hb
    apply mul_left_cancel₀ (sub_ne_zero.mpr hr.ne')
    linear_combination hb
  have hg : 4 * gibbsLow r * gibbsHigh r = r^3 / (((1 + r^3) / 2)^2) := by
    unfold gibbsHigh gibbsLow
    field_simp [hT]
    norm_num
  unfold G Q h
  rw [hg, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, hn]
  push_cast
  have hA : (gamma r * (r - 1)^2 * (r + 1) + alpha r *
      (3 * Real.log r - 2 * Real.log ((1 + r^3) / 2))) / 2 +
        alpha r * (Real.log ((1 + r^3) / 2) - 3 * r^3 * Real.log r / (1 + r^3)) =
      gamma r * (r - 1)^2 * (r + 1) / 2 +
        (alpha r * Real.log r) * (3 / 2 - 3 * r^3 / (1 + r^3)) := by ring
  rw [hA, alpha_log hr]
  unfold cutA gamma
  field_simp [hc, hT, hU, hplus]
  ring

private theorem G_one : G 1 1 = 0 := by
  norm_num [G, Q, N, h, alpha, gibbsLow, gibbsHigh, c, e, bias, gamma, cutA]

private theorem Dprime_one_zero : Dprime 1 0 = 9 * alpha 1 := by
  norm_num [Dprime, P, R, S, c, e, bias, gamma, alpha]

private theorem slope_lt_gibbs {r t : ℝ} (ht : 1 < t) (htr : t < r) :
    laurent r t - 9 * alpha r * Real.log t < 0 := by
  have hr := ht.trans htr
  have htlog := Real.log_pos ht
  have hrlog := Real.log_pos hr
  have hs := (strictly_convex_D hr.le).secant_strict_mono (a := 0)
    (mem_Ici.mpr (le_refl (0 : ℝ))) htlog.le hrlog.le htlog.ne' hrlog.ne'
    (Real.log_lt_log (zero_lt_one.trans ht) htr)
  simp only [D_zero, sub_zero] at hs
  rw [D_log r (zero_lt_one.trans ht),
    D_log r (zero_lt_one.trans hr), laurent_gibbs hr] at hs
  have hdiv : (9 * (alpha r * Real.log r)) / Real.log r = 9 * alpha r := by
    field_simp [hrlog.ne']
  rw [hdiv] at hs
  linarith only [(div_lt_iff₀ htlog).mp hs]

private theorem slope_gt_gibbs {r t : ℝ} (hr : 1 ≤ r) (hrt : r < t) :
    0 < laurent r t - 9 * alpha r * Real.log t := by
  have ht := hr.trans_lt hrt
  have htlog := Real.log_pos ht
  have hzero : 0 ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  rcases hr.eq_or_lt with hr | hr
  · subst r
    have hs := (strictly_convex_D le_rfl).lt_slope_of_hasDerivAt
      hzero htlog.le htlog (hasDerivAt_D 1 0)
    simp only [Dprime_one_zero, slope_def_field, D_zero, sub_zero] at hs
    rw [D_log 1 (zero_lt_one.trans ht)] at hs
    linarith only [(lt_div_iff₀ htlog).mp hs]
  · have hrlog := Real.log_pos hr
    have hs := (strictly_convex_D hr.le).secant_strict_mono
      hzero hrlog.le htlog.le hrlog.ne' htlog.ne'
      (Real.log_lt_log (zero_lt_one.trans hr) hrt)
    simp only [D_zero, sub_zero] at hs
    rw [D_log r (zero_lt_one.trans hr),
      D_log r (zero_lt_one.trans ht), laurent_gibbs hr] at hs
    have hdiv : (9 * (alpha r * Real.log r)) / Real.log r = 9 * alpha r := by
      field_simp [hrlog.ne']
    rw [hdiv] at hs
    linarith only [(lt_div_iff₀ htlog).mp hs]

private theorem G_minimum {r t : ℝ} (hr : 1 ≤ r) (ht : 1 < t) : 0 ≤ G r t := by
  have hG : G r r = 0 := by
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact G_one
    · exact G_gibbs hr
  have hcont {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn (G r) (Icc a b) :=
    (continuousOn_G hr).mono fun x hx => zero_lt_one.trans_le (ha.trans hx.1)
  rcases lt_trichotomy t r with htr | rfl | hrt
  · have hanti : StrictAntiOn (G r) (Icc t r) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc t r) (hcont ht.le)
      intro x hx
      rw [interior_Icc] at hx
      have hx1 := ht.trans hx.1
      have hx0 := zero_lt_one.trans hx1
      rw [(hasDerivAt_G hr hx0).deriv]
      exact mul_neg_of_pos_of_neg (by positivity) (slope_lt_gibbs hx1 hx.2)
    exact hG ▸ (hanti ⟨le_rfl, htr.le⟩ ⟨htr.le, le_rfl⟩ htr).le
  · exact hG.ge
  · have hmono : StrictMonoOn (G r) (Icc r t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc r t) (hcont hr)
      intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := zero_lt_one.trans (hr.trans_lt hx.1)
      rw [(hasDerivAt_G hr hx0).deriv]
      exact mul_pos (by positivity) (slope_gt_gibbs hr hx.1)
    exact hG ▸ (hmono ⟨le_rfl, hrt.le⟩ ⟨hrt.le, le_rfl⟩ hrt).le

private theorem deficit_pos_levels {r v w z : ℝ} (hr : 1 ≤ r) (hv : 0 < v) (hvw : v < w) :
    0 ≤ oneModeDeficit r v w z := by
  let t := w / v
  have ht : 1 < t := (lt_div_iff₀ hv).mpr (by simpa using hvw)
  have ht0 := zero_lt_one.trans ht
  have hw : v * t = w := by dsimp [t]; field_simp [hv.ne']
  rw [← hw, complete_square hr hv ht]
  have hG := G_minimum hr ht
  have hA : 0 ≤ cutA r 1 t := by unfold cutA; have := c_pos hr; positivity
  positivity

private theorem continuous_deficit (r w z : ℝ) :
    Continuous fun v => oneModeDeficit r v w z := by
  have hmass : (fun v : ℝ => (v^3 + w^3) * Real.log ((v^3 + w^3) / 2)) =
      fun v => 2 * (((v^3 + w^3) / 2) * Real.log ((v^3 + w^3) / 2)) := by
    funext v
    ring
  have hsum : Continuous fun v : ℝ => (v^3 + w^3) / 2 := by fun_prop
  have hcube : Continuous fun v : ℝ => v^3 := by fun_prop
  have hentropy : Continuous fun v => entropyPair v w := by
    unfold entropyPair
    simp_rw [congrFun hmass]
    exact (((Real.continuous_mul_log.comp hsum).const_mul 2).sub
      (Real.continuous_mul_log.comp hcube)).sub continuous_const
  unfold oneModeDeficit cutA cutB
  fun_prop

/-- Wu's exact one-mode premise holds at every temperature parameter `r ≥ 1`. -/
theorem one_mode_bound {r : ℝ} (hr : 1 ≤ r) : OneModeBound r := by
  intro v w z hv hvw _ _
  have hw := hv.trans hvw
  rcases hw.eq_or_lt with hw | hw
  · have hv0 : v = 0 := le_antisymm (hvw.trans hw.ge) hv
    simp [← hw, hv0, oneModeDeficit, entropyPair, cutA, cutB]
  · have hmem : v ∈ closure (Ioo 0 w) := by rw [closure_Ioo hw.ne]; exact ⟨hv, hvw⟩
    exact le_on_closure (f := fun _ : ℝ => 0) (g := fun x => oneModeDeficit r x w z)
      (fun _ hx => deficit_pos_levels hr hx.1 hx.2) continuousOn_const
      (continuous_deficit r w z).continuousOn hmem

#print axioms one_mode_bound

end D5.S3.Quantum.Semigroups.WuOneModeCubic
