/- GID: D5/S3/Analytic/GhoshWeightedShiftRootUniqueness
   generality: I
   mirror-B: D5/B/S3/Analytic/GhoshWeightedShiftRootUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Unique interior root of the Ghosh-Birbonshi-Ojha weighted-shift polynomial. -/

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.GhoshWeightedShiftRootUniqueness

open Set Filter
open scoped Topology

/-- The degree-eight polynomial in Section 2 of Ghosh, Birbonshi and Ojha. -/
def g (s t q z : ℝ) : ℝ :=
  t*q^7*z^8 + q^6*(t*q-1)*z^7 + 3*q^5*(q-s)*z^6 + 5*q^4*(s*q-1)*z^5 +
  q^3*(7*q-9*t)*z^4 + 7*q^2*(t*q-1)*z^3 + 5*q*(q-s)*z^2 + 3*(s*q-1)*z + 1

/-- The full real-parameter root assertion of Open question 1. -/
theorem result (s t q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃! z : ℝ, (1 / 3 : ℝ) < z ∧ z < 1 ∧ g s t q z = 0 := by
  let dg : ℝ → ℝ := fun z =>
    8*t*q^7*z^7 + 7*q^6*(t*q-1)*z^6 + 18*q^5*(q-s)*z^5 +
    25*q^4*(s*q-1)*z^4 + 4*q^3*(7*q-9*t)*z^3 +
    21*q^2*(t*q-1)*z^2 + 10*q*(q-s)*z + 3*(s*q-1)
  have hderiv (z : ℝ) : HasDerivAt (g s t q) (dg z) z := by
    have hid := hasDerivAt_id z
    have hd := (((((((((hid.pow 8).const_mul (t*q^7)).add
      ((hid.pow 7).const_mul (q^6*(t*q-1)))).add
      ((hid.pow 6).const_mul (3*q^5*(q-s)))).add
      ((hid.pow 5).const_mul (5*q^4*(s*q-1)))).add
      ((hid.pow 4).const_mul (q^3*(7*q-9*t)))).add
      ((hid.pow 3).const_mul (7*q^2*(t*q-1)))).add
      ((hid.pow 2).const_mul (5*q*(q-s)))).add
      (hid.const_mul (3*(s*q-1)))).add_const 1
    exact hd.congr_deriv (by dsimp [dg]; norm_num; ring)
  have hcont : Continuous (g s t q) :=
    continuous_iff_continuousAt.mpr (fun z => (hderiv z).continuousAt)
  have hlo : g s t q (1/3) =
      4*q*s/9 + 8*q^2/27 + 4*q^3*t/27 + 16*q^4/243 +
      4*q^5*s/243 + 8*q^6/2187 + 4*q^7*t/6561 := by
    dsimp [g]
    ring
  have hlo_pos : 0 < g s t q (1/3) := by
    rw [hlo]
    positivity
  have hhi : g s t q 1 = 2*(q^4-1)*(t*q^3+q^2+s*q+1) := by
    dsimp [g]
    ring
  have hq4 : q^4 < 1 := pow_lt_one₀ hq.le hq1 (by norm_num)
  have hhi_neg : g s t q 1 < 0 := by
    rw [hhi]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hq4)) (by positivity)
  have hroot (z : ℝ) (hz : (1/3 : ℝ) < z) (hz1 : z < 1)
      (hgz : g s t q z = 0) : dg z < 0 := by
    have hz0 : 0 < z := by linarith only [hz]
    have h1z : 0 < 1-z := sub_pos.mpr hz1
    let b : ℝ := z^2
    let c : ℝ := q^2*z^2
    let A : ℝ := s*q*z
    let B : ℝ := t*q^3*z^3
    let P : ℝ := 1+A+c+B
    let a3 : ℝ := z^2-6*z-3
    let a2 : ℝ := 15*z^2-18*z-21
    let J : ℝ → ℝ := fun x =>
      (z^2-6*z-3)*x^3 + (15*z^2-18*z-21)*x^2 +
      (63*z^2-90*z+35)*x + 81*z^2-78*z+21
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hb1 : b < 1 := pow_lt_one₀ hz0.le hz1 (by norm_num)
    have hq2 : q^2 < 1 := pow_lt_one₀ hq.le hq1 (by norm_num)
    have hc0 : 0 < c := by dsimp [c]; positivity
    have hcb : c < b := by
      have hp := mul_pos (sub_pos.mpr hq2) hb0
      dsimp [c, b] at *
      nlinarith only [hp]
    have hc1 : c < 1 := lt_trans hcb hb1
    have hbc : 0 < b-c := sub_pos.mpr hcb
    have ha3 : a3 < 0 := by
      dsimp [a3]
      change z^2 < 1 at hb1
      nlinarith only [hb1, hz0]
    have ha2 : a2 < 0 := by
      dsimp [a2]
      change z^2 < 1 at hb1
      nlinarith only [hb1, hz0]
    have hj0 : J 0 = 81*(z-13/27)^2 + 20/9 := by
      dsimp [J]
      ring
    have hjb : J b = (1-z)^3*(6+15*(1-z)+8*z^2+z^4*(3-z)) := by
      dsimp [J, b]
      ring
    have hchord : b*J c = (b-c)*J 0 + c*J b +
        b*c*(b-c)*(-a2-a3*(b+c)) := by
      dsimp [b, J, a2, a3]
      ring
    have hj0_pos : 0 < J 0 := by rw [hj0]; positivity
    have h3z : 0 < 3-z := by linarith only [hz1]
    have hjb_pos : 0 < J b := by rw [hjb]; positivity
    have hcoef : 0 < -a2-a3*(b+c) := by
      have hp : a3*(b+c) < 0 := mul_neg_of_neg_of_pos ha3 (by positivity)
      linarith only [ha2, hp]
    have hbj : 0 < b*J c := by rw [hchord]; positivity
    have hj_pos : 0 < J c := by
      by_contra hn
      have hp := mul_nonpos_of_nonneg_of_nonpos hb0.le (le_of_not_gt hn)
      linarith only [hbj, hp]
    have hA : 0 < A := by dsimp [A]; positivity
    have hB : 0 < B := by dsimp [B]; positivity
    have hP : 0 < P := by dsimp [P]; positivity
    have hc2 : c^2 < 1 := pow_lt_one₀ hc0.le hc1 (by norm_num)
    have h1c : 0 < 1-c^2 := sub_pos.mpr hc2
    have h3c : 0 < 3-c := by linarith only [hc1]
    have hcert : 2*z*(1-z)*(3+c)*dg z + P*J c +
        8*A*(1-z)^2*(1-c^2)*(3-c) =
        ((7-11*z)*(3+c)+4*c*(1-z))*g s t q z := by
      dsimp [A, c, B, P, J, dg, g]
      ring
    rw [hgz, mul_zero] at hcert
    have hm : 0 < 2*z*(1-z)*(3+c) := by positivity
    have hpj : 0 < P*J c := mul_pos hP hj_pos
    have hcor : 0 < 8*A*(1-z)^2*(1-c^2)*(3-c) := by positivity
    by_contra hn
    have hp := mul_nonneg hm.le (le_of_not_gt hn)
    linarith only [hcert, hpj, hcor, hp]
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc'
    (show (1/3 : ℝ) ≤ 1 by norm_num) hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (g s t q 1) (g s t q (1/3)) from
      ⟨hhi_neg.le, hlo_pos.le⟩)
  have hzlo : (1/3 : ℝ) < z := by
    rcases eq_or_lt_of_le hz.1 with heq | hlt
    · have hzneq : g s t q (1/3) ≠ 0 := ne_of_gt hlo_pos
      exact False.elim (hzneq (heq ▸ hgz))
    · exact hlt
  have hzhi : z < 1 := by
    rcases lt_or_eq_of_le hz.2 with hlt | heq
    · exact hlt
    · have hzneq : g s t q 1 ≠ 0 := ne_of_lt hhi_neg
      exact False.elim (hzneq (heq ▸ hgz))
  have hpair (u v : ℝ)
      (hu : (1/3 : ℝ) < u ∧ u < 1 ∧ g s t q u = 0)
      (hv : (1/3 : ℝ) < v ∧ v < 1 ∧ g s t q v = 0)
      (huv : u < v) : False := by
    have hfence : ∀ ⦃x : ℝ⦄, x ∈ Icc u v → g s t q x ≤ 0 :=
      image_le_of_deriv_right_lt_deriv_boundary hcont.continuousOn
        (fun x _ => (hderiv x).hasDerivWithinAt)
        (B := fun _ : ℝ => 0) (B' := fun _ : ℝ => 0)
        (by rw [hu.2.2]) (fun x => hasDerivAt_const x (0 : ℝ))
        (fun x hx hxg => hroot x (lt_of_lt_of_le hu.1 hx.1)
          (lt_trans hx.2 hv.2.1) hxg)
    have hdv : deriv (g s t q) v < 0 := by
      rw [(hderiv v).deriv]
      exact hroot v hv.1 hv.2.1 hv.2.2
    obtain ⟨l, r, hvI, hsign⟩ :=
      (eventually_nhdsWithin_sign_eq_of_deriv_neg hdv hv.2.2).exists_Ioo_subset
    let x : ℝ := (max u l + v)/2
    have hm : max u l < v := max_lt huv hvI.1
    have hmx : max u l < x := by dsimp [x]; linarith only [hm]
    have hxv : x < v := by dsimp [x]; linarith only [hm]
    have hux : u < x := lt_of_le_of_lt (le_max_left u l) hmx
    have hlx : l < x := lt_of_le_of_lt (le_max_right u l) hmx
    have hxpos : 0 < g s t q x := sign_eq_one_iff.mp
      ((hsign ⟨hlx, lt_trans hxv hvI.2⟩).trans (sign_pos (sub_pos.mpr hxv)))
    exact (not_lt_of_ge (hfence ⟨hux.le, hxv.le⟩)) hxpos
  refine ⟨z, ⟨hzlo, hzhi, hgz⟩, ?_⟩
  intro y hy
  rcases lt_trichotomy y z with hyz | heq | hzy
  · exact False.elim (hpair y z hy ⟨hzlo, hzhi, hgz⟩ hyz)
  · exact heq
  · exact False.elim (hpair z y ⟨hzlo, hzhi, hgz⟩ hy hzy)

end D5.S3.Analytic.GhoshWeightedShiftRootUniqueness

#print axioms D5.S3.Analytic.GhoshWeightedShiftRootUniqueness.result
