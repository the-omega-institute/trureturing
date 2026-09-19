/- GID: D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Enclose the smooth transition through one scaled positive exponential. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic
import D5.S0.Certificates.BoxCover.RationalIntervalExpression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic

open scoped BigOperators

def taylorSum (q : Rat) (n : Nat) : Rat :=
  ∑ i ∈ Finset.range n, q ^ i / (Nat.factorial i : Rat)

def positiveTaylorUpper (q : Rat) (n : Nat) : Rat :=
  taylorSum q n + q ^ n * (n + 1) / ((Nat.factorial n : Rat) * n)

def scaledExpInterval (d : Rat) (scale depth : Nat) : Rat × Rat :=
  let x := d / scale
  ((taylorSum x depth) ^ scale, (positiveTaylorUpper x depth) ^ scale)

def logisticImage (box : Rat × Rat) : Rat × Rat :=
  (1 / box.2 / (1 + 1 / box.2), 1 / box.1 / (1 + 1 / box.1))

def logisticDifference (t : Rat) : Rat :=
  1 / t - 1 / (1 - t)

def logisticInterval (t : Rat) (scale depth : Nat) : Rat × Rat :=
  logisticImage (scaledExpInterval (logisticDifference t) scale depth)

def LogisticAccepted (t : Rat) (scale depth : Nat) : Prop :=
  0 < t ∧ t ≤ 1 / 2 ∧
  0 < scale ∧ 0 < depth ∧
  0 ≤ logisticDifference t ∧ logisticDifference t ≤ scale ∧
  0 < (scaledExpInterval (logisticDifference t) scale depth).1 ∧
  (logisticInterval t scale depth).1 ≤ (logisticInterval t scale depth).2

instance (t : Rat) (scale depth : Nat) : Decidable (LogisticAccepted t scale depth) := by
  unfold LogisticAccepted
  infer_instance

def checkLogistic (t : Rat) (scale depth : Nat) : Bool :=
  decide (LogisticAccepted t scale depth)

private theorem scaledExpInterval_sound (d : Rat) (scale depth : Nat)
    (hs : 0 < scale) (hn : 0 < depth) (hd0 : 0 ≤ d) (hds : d ≤ scale) :
    ((scaledExpInterval d scale depth).1 : Real) ≤ Real.exp (d : Real) ∧
    Real.exp (d : Real) ≤ ((scaledExpInterval d scale depth).2 : Real) := by
  have hx0 : 0 ≤ d / (scale : Rat) := div_nonneg hd0 (by exact_mod_cast hs.le)
  have hx1 : d / (scale : Rat) ≤ 1 := (div_le_one (by exact_mod_cast hs)).2 hds
  have taylor (q : Rat) (n : Nat) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hn : 0 < n) :
      ((taylorSum q n : Rat) : Real) ≤ Real.exp (q : Real) ∧
      Real.exp (q : Real) ≤ ((positiveTaylorUpper q n : Rat) : Real) := by
    constructor
    · simpa only [taylorSum, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
        Rat.cast_natCast] using Real.sum_le_exp_of_nonneg
          (show (0 : Real) ≤ (q : Real) by exact_mod_cast hq0) n
    · have h := Real.exp_bound'
        (show (0 : Real) ≤ (q : Real) by exact_mod_cast hq0)
        (show (q : Real) ≤ 1 by exact_mod_cast hq1) hn
      simpa only [positiveTaylorUpper, taylorSum, Rat.cast_add, Rat.cast_sum,
        Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
        Rat.cast_one, Nat.cast_add, Nat.cast_one] using h
  have hx := taylor (d / scale) depth hx0 hx1 hn
  have hl0 : (0 : Real) ≤ (taylorSum (d / scale) depth : Rat) := by
    exact_mod_cast (Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hx0 i) (by positivity))
  have hu0 : (0 : Real) ≤ (positiveTaylorUpper (d / scale) depth : Rat) :=
    hl0.trans (hx.1.trans hx.2)
  have hp := And.intro (pow_le_pow_left₀ hl0 hx.1 scale)
    (pow_le_pow_left₀ (Real.exp_pos _).le hx.2 scale)
  have he : Real.exp (d : Real) = (Real.exp ((d / scale : Rat) : Real)) ^ scale := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simpa only [scaledExpInterval, Rat.cast_pow, he] using hp

theorem checked_logistic_sound (t : Rat) (scale depth : Nat)
    (hcheck : checkLogistic t scale depth = true) :
    ((logisticInterval t scale depth).1 : Real) ≤ Real.smoothTransition (t : Real) ∧
    Real.smoothTransition (t : Real) ≤ ((logisticInterval t scale depth).2 : Real) := by
  have ha := of_decide_eq_true hcheck
  rcases ha with ⟨ht0, hth, hs, hn, hd0, hds, hl0, _⟩
  have ht0r : (0 : Real) < t := by exact_mod_cast ht0
  have ht1r : (t : Real) < 1 := by exact_mod_cast (hth.trans_lt (by norm_num))
  have smoothTransition_eq_logistic :
      Real.smoothTransition (t : Real) =
        1 / (1 + Real.exp (1 / (t : Real) - 1 / (1 - (t : Real)))) := by
    have ha : expNegInvGlue (t : Real) = Real.exp (-(t : Real)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr ht0r]
    have hb : expNegInvGlue (1 - (t : Real)) =
        Real.exp (-((1 - (t : Real))⁻¹)) := by
      simp [expNegInvGlue, not_le.mpr (sub_pos.mpr ht1r)]
    rw [Real.smoothTransition, ha, hb]
    calc
      Real.exp (-(t : Real)⁻¹) /
            (Real.exp (-(t : Real)⁻¹) + Real.exp (-(1 - (t : Real))⁻¹)) =
          1 / (1 + Real.exp (-(1 - (t : Real))⁻¹) /
            Real.exp (-(t : Real)⁻¹)) := by
            field_simp [Real.exp_ne_zero]
      _ = 1 / (1 + Real.exp (1 / (t : Real) - 1 / (1 - (t : Real)))) := by
        congr 2
        rw [← Real.exp_sub]
        congr 1
        field_simp
        ring
  have he := scaledExpInterval_sound (logisticDifference t) scale depth hs hn hd0 hds
  have hl0r : (0 : Real) < (scaledExpInterval (logisticDifference t) scale depth).1 := by
    exact_mod_cast hl0
  have hi :
      1 / ((scaledExpInterval (logisticDifference t) scale depth).2 : Real) /
          (1 + 1 / ((scaledExpInterval (logisticDifference t) scale depth).2 : Real)) ≤
        1 / Real.exp (logisticDifference t : Real) /
          (1 + 1 / Real.exp (logisticDifference t : Real)) ∧
      1 / Real.exp (logisticDifference t : Real) /
          (1 + 1 / Real.exp (logisticDifference t : Real)) ≤
        1 / ((scaledExpInterval (logisticDifference t) scale depth).1 : Real) /
          (1 + 1 / ((scaledExpInterval (logisticDifference t) scale depth).1 : Real)) := by
    have hz : 0 < Real.exp (logisticDifference t : Real) := Real.exp_pos _
    have hu : 0 < ((scaledExpInterval (logisticDifference t) scale depth).2 : Real) :=
      hz.trans_le he.2
    constructor <;> field_simp <;> nlinarith
  have hz : 0 < Real.exp (logisticDifference t : Real) := Real.exp_pos _
  have hlog :
      1 / Real.exp (logisticDifference t : Real) /
          (1 + 1 / Real.exp (logisticDifference t : Real)) =
        1 / (1 + Real.exp (logisticDifference t : Real)) := by
    field_simp
    ring
  rw [smoothTransition_eq_logistic]
  have hdcast : ((logisticDifference t : Rat) : Real) =
      1 / (t : Real) - 1 / (1 - (t : Real)) := by
    simp [logisticDifference]
  rw [← hdcast, ← hlog]
  simpa only [logisticInterval, logisticImage, Rat.cast_div, Rat.cast_one,
    Rat.cast_add] using hi

private theorem smoothTransition_far_bound (t : Rat) (m : Nat)
    (ht0 : 0 < t) (ht1 : t < 1) (hd : (m : Rat) ≤ logisticDifference t) :
    Real.smoothTransition (t : Real) ≤ (((1 / 2 : Rat) ^ m : Rat) : Real) := by
  have ht0r : (0 : Real) < t := by exact_mod_cast ht0
  have ht1r : (t : Real) < 1 := by exact_mod_cast ht1
  have smoothTransition_eq_logistic :
      Real.smoothTransition (t : Real) =
        1 / (1 + Real.exp (1 / (t : Real) - 1 / (1 - (t : Real)))) := by
    have ha : expNegInvGlue (t : Real) = Real.exp (-(t : Real)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr ht0r]
    have hb : expNegInvGlue (1 - (t : Real)) =
        Real.exp (-((1 - (t : Real))⁻¹)) := by
      simp [expNegInvGlue, not_le.mpr (sub_pos.mpr ht1r)]
    rw [Real.smoothTransition, ha, hb]
    calc
      Real.exp (-(t : Real)⁻¹) /
            (Real.exp (-(t : Real)⁻¹) + Real.exp (-(1 - (t : Real))⁻¹)) =
          1 / (1 + Real.exp (-(1 - (t : Real))⁻¹) /
            Real.exp (-(t : Real)⁻¹)) := by
            field_simp [Real.exp_ne_zero]
      _ = 1 / (1 + Real.exp (1 / (t : Real) - 1 / (1 - (t : Real)))) := by
        congr 2
        rw [← Real.exp_sub]
        congr 1
        field_simp
        ring
  rw [smoothTransition_eq_logistic]
  have he2 : (2 : Real) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : Real)]
  have hp : (2 : Real) ^ m ≤ Real.exp ((m : Nat) : Real) := by
    rw [show Real.exp ((m : Nat) : Real) = (Real.exp 1) ^ m by
      rw [show ((m : Nat) : Real) = m * 1 by simp, Real.exp_nat_mul]]
    exact pow_le_pow_left₀ (by norm_num) he2 m
  have hmd : ((m : Nat) : Real) ≤ (logisticDifference t : Rat) := by
    exact_mod_cast hd
  have he : (2 : Real) ^ m ≤ Real.exp (logisticDifference t : Rat) :=
    hp.trans (Real.exp_le_exp.mpr hmd)
  have hden : (2 : Real) ^ m ≤ 1 + Real.exp (logisticDifference t : Rat) :=
    he.trans (le_add_of_nonneg_left zero_le_one)
  have h := one_div_le_one_div_of_le (pow_pos (by norm_num) m) hden
  have hdcast : ((logisticDifference t : Rat) : Real) =
      1 / (t : Real) - 1 / (1 - (t : Real)) := by
    simp [logisticDifference]
  rw [← hdcast]
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    one_div_pow] using h

def cutoffLogisticInterval (t : Rat) (m depth : Nat) : Rat × Rat :=
  if t ≤ 0 then (0, 0) else if 1 ≤ t then (1, 1)
  else
    let reflected := 1 / 2 < t
    let u := if reflected then 1 - t else t
    let base := if (m : Rat) ≤ logisticDifference u then
      (0, (1 / 2 : Rat) ^ m)
    else logisticInterval u (m + 1) depth
    if reflected then (1 - base.2, 1 - base.1) else base

def CutoffLogisticAccepted (t : Rat) (m depth : Nat) : Prop :=
  if t ≤ 0 then True else if 1 ≤ t then True
  else
    let u := if 1 / 2 < t then 1 - t else t
    (if (m : Rat) ≤ logisticDifference u then True
      else LogisticAccepted u (m + 1) depth) ∧
    (cutoffLogisticInterval t m depth).1 ≤ (cutoffLogisticInterval t m depth).2 ∧
    (cutoffLogisticInterval t m depth).2 - (cutoffLogisticInterval t m depth).1 ≤
      (1 / 2 : Rat) ^ m

instance (t : Rat) (m depth : Nat) : Decidable (CutoffLogisticAccepted t m depth) := by
  unfold CutoffLogisticAccepted
  infer_instance

def checkCutoffLogistic (t : Rat) (m depth : Nat) : Bool :=
  decide (CutoffLogisticAccepted t m depth)

theorem checked_cutoff_logistic_sound (t : Rat) (m depth : Nat)
    (hcheck : checkCutoffLogistic t m depth = true) :
    let box := cutoffLogisticInterval t m depth
    box.1 ≤ box.2 ∧
    (box.1 : Real) ≤ Real.smoothTransition (t : Real) ∧
    Real.smoothTransition (t : Real) ≤ (box.2 : Real) ∧
    box.2 - box.1 ≤ (1 / 2 : Rat) ^ m := by
  have smoothTransition_reflect (t : Real) :
      Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
    unfold Real.smoothTransition
    have h := Real.smoothTransition.pos_denom t
    simp only [sub_sub_cancel]
    rw [add_comm (expNegInvGlue (1 - t)) (expNegInvGlue t)]
    apply (div_eq_iff h.ne').2
    field_simp [h.ne']
    ring
  dsimp only
  have ha := of_decide_eq_true hcheck
  by_cases h0 : t ≤ 0
  · have hs := Real.smoothTransition.zero_of_nonpos (show (t : Real) ≤ 0 by exact_mod_cast h0)
    simp [CutoffLogisticAccepted, cutoffLogisticInterval, h0, hs]
  · by_cases h1 : 1 ≤ t
    · have hs := Real.smoothTransition.one_of_one_le (show (1 : Real) ≤ t by exact_mod_cast h1)
      simp [CutoffLogisticAccepted, cutoffLogisticInterval, h0, h1, hs]
    · have ht0 : 0 < t := lt_of_not_ge h0
      have ht1 : t < 1 := lt_of_not_ge h1
      let reflected := 1 / 2 < t
      let u : Rat := if reflected then 1 - t else t
      have hu0 : 0 < u := by
        dsimp [u, reflected]
        split_ifs <;> linarith
      have huh : u ≤ 1 / 2 := by
        dsimp [u, reflected]
        split_ifs <;> linarith
      have hu1 : u < 1 := huh.trans_lt (by norm_num)
      simp only [CutoffLogisticAccepted, h0, h1, if_false, u, reflected] at ha
      rcases ha with ⟨hcore, horder, hwidth⟩
      change (if (m : Rat) ≤ logisticDifference u then True
        else LogisticAccepted u (m + 1) depth) at hcore
      let base : Rat × Rat := if (m : Rat) ≤ logisticDifference u then
        (0, (1 / 2 : Rat) ^ m) else logisticInterval u (m + 1) depth
      have hbase :
          (base.1 : Real) ≤ Real.smoothTransition (u : Real) ∧
          Real.smoothTransition (u : Real) ≤ (base.2 : Real) := by
        dsimp only [base]
        by_cases hfar : (m : Rat) ≤ logisticDifference u
        · simp only [hfar, if_true, Rat.cast_zero]
          exact ⟨Real.smoothTransition.nonneg _,
            smoothTransition_far_bound u m hu0 hu1 hfar⟩
        · simp only [hfar, if_false]
          exact checked_logistic_sound u (m + 1) depth (by
            apply decide_eq_true
            simpa [hfar] using hcore)
      have hsem :
          ((cutoffLogisticInterval t m depth).1 : Real) ≤
              Real.smoothTransition (t : Real) ∧
          Real.smoothTransition (t : Real) ≤
              ((cutoffLogisticInterval t m depth).2 : Real) := by
        by_cases hr : reflected
        · change 1 / 2 < t at hr
          have hr' : (2 : Rat)⁻¹ < t := by norm_num at hr ⊢; exact hr
          have hut : (u : Real) = 1 - (t : Real) := by simp [u, reflected, hr]
          rw [hut, smoothTransition_reflect (t : Real)] at hbase
          have hcut : cutoffLogisticInterval t m depth =
              (1 - base.2, 1 - base.1) := by
            simp [cutoffLogisticInterval, h0, h1, hr', u, reflected, hr, base]
          rw [hcut]
          simp only [Rat.cast_sub, Rat.cast_one]
          exact ⟨by linarith [hbase.2], by linarith [hbase.1]⟩
        · change ¬1 / 2 < t at hr
          have hr' : ¬(2 : Rat)⁻¹ < t := by norm_num at hr ⊢; exact hr
          have hut : u = t := by simp [u, reflected, hr]
          have hcut : cutoffLogisticInterval t m depth = base := by
            simp [cutoffLogisticInterval, h0, h1, hr', u, reflected, hr, base]
          rw [hut] at hbase
          rw [hcut]
          exact hbase
      exact ⟨horder, hsem.1, hsem.2, hwidth⟩

example : checkLogistic (1 / 4) 8 18 = true := by
  norm_num [checkLogistic, LogisticAccepted, logisticInterval, logisticImage,
    scaledExpInterval, logisticDifference, positiveTaylorUpper, taylorSum]

example : checkCutoffLogistic (1 / 4) 4 18 = true := by
  norm_num [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval,
    LogisticAccepted, logisticInterval, logisticImage, scaledExpInterval,
    logisticDifference, positiveTaylorUpper, taylorSum]

example : checkCutoffLogistic (1 / 4) 16 36 = true := by
  norm_num [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval,
    LogisticAccepted, logisticInterval, logisticImage, scaledExpInterval,
    logisticDifference, positiveTaylorUpper, taylorSum]

example : checkCutoffLogistic (3 / 4) 16 36 = true := by
  norm_num [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval,
    LogisticAccepted, logisticInterval, logisticImage, scaledExpInterval,
    logisticDifference, positiveTaylorUpper, taylorSum]

example : checkCutoffLogistic (1 / 1000) 16 36 = true := by
  norm_num [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval,
    LogisticAccepted, logisticInterval, logisticImage, scaledExpInterval,
    logisticDifference, positiveTaylorUpper, taylorSum]

#print axioms checked_logistic_sound
#print axioms checked_cutoff_logistic_sound

end D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
