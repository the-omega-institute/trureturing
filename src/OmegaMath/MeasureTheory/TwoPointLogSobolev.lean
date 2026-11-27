import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp two-point log-Sobolev inequality

We use natural logarithms and the continuous convention `0 log 0 = 0`.
The Dirichlet form is normalized as `(x - y)^2`. Multiplying the form by
`p * q` divides the optimal coefficient by `p * q`.

See P. Diaconis and L. Saloff-Coste,
*Logarithmic Sobolev inequalities for finite Markov chains*,
Ann. Appl. Probab. 6 (1996), 695–750. https://doi.org/10.1214/aoap/1034968224
-/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace Omega.MeasureTheory.TwoPointLogSobolev

open Set

/-- Entropy of the values `u, v` for the probability weights `p, q`. -/
def entropy (p q u v : ℝ) : ℝ :=
  Real.negMulLog (p * u + q * v) - (p * Real.negMulLog u + q * Real.negMulLog v)

/-- The optimal coefficient for the Dirichlet form `(x - y)^2`. -/
def sharpConstant (p q : ℝ) : ℝ :=
  if p = q then 1 / 2 else p * q * Real.log (q / p) / (q - p)

private theorem entropy_scale {p q : ℝ} (t u v : ℝ) :
    entropy p q (t * u) (t * v) = t * entropy p q u v := by
  unfold entropy
  rw [show p * (t * u) + q * (t * v) = t * (p * u + q * v) by ring]
  simp only [Real.negMulLog_mul]
  ring

private theorem entropy_swap (p q u v : ℝ) :
    entropy q p v u = entropy p q u v := by
  unfold entropy
  rw [add_comm (q * v), add_comm (q * Real.negMulLog v)]

private theorem constant_swap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    sharpConstant q p = sharpConstant p q := by
  by_cases h : p = q
  · subst q
    rfl
  · simp only [sharpConstant, if_neg h, if_neg (Ne.symm h),
      Real.log_div hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']
    rw [show p - q = -(q - p) by ring, div_neg]
    ring

private def mean (p q x : ℝ) : ℝ := p * x ^ 2 + q

private def logRatio (p q x : ℝ) : ℝ := Real.log (x ^ 2) - Real.log (mean p q x)

private def gap (p q c x : ℝ) : ℝ := c * (x - 1) ^ 2 - entropy p q (x ^ 2) 1

private def gapFirst (p q c x : ℝ) : ℝ :=
  2 * c * (x - 1) - 2 * p * x * logRatio p q x

private def gapSecond (p q c x : ℝ) : ℝ :=
  2 * c - 2 * p * logRatio p q x - 4 * p * q / mean p q x

private def gapThird (p q x : ℝ) : ℝ :=
  4 * p * q * (p * x ^ 2 - q) / (x * mean p q x ^ 2)

private theorem mean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : ℝ) :
    0 < mean p q x :=
  add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg x)) hq

private theorem deriv_sq (x : ℝ) :
    HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> simp

private theorem deriv_mean (p q x : ℝ) :
    HasDerivAt (mean p q) (2 * p * x) x := by
  unfold mean
  convert ((deriv_sq x).const_mul p).add_const q using 1 <;> ring

private theorem deriv_logRatio {p q x : ℝ} (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) :
    HasDerivAt (logRatio p q) (2 * q / (x * mean p q x)) x := by
  have hm := mean_pos hp hq x
  unfold logRatio
  convert ((deriv_sq x).log (pow_ne_zero 2 hx.ne')).sub
    ((deriv_mean p q x).log hm.ne') using 1
  field_simp [hx.ne', hm.ne'] <;> unfold mean <;> ring

private theorem continuous_gap (p q c : ℝ) : Continuous (gap p q c) := by
  unfold gap entropy
  fun_prop

private theorem deriv_gap {p q c x : ℝ} (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) :
    HasDerivAt (gap p q c) (gapFirst p q c x) x := by
  have hm := mean_pos hp hq x
  have hquad := (((hasDerivAt_id x).sub_const 1).pow 2).const_mul c
  have hmean := (Real.hasDerivAt_negMulLog hm.ne').comp x (deriv_mean p q x)
  have hsquare := (Real.hasDerivAt_negMulLog (pow_ne_zero 2 hx.ne')).comp x (deriv_sq x)
  unfold gap gapFirst entropy logRatio
  convert hquad.sub (hmean.sub ((hsquare.const_mul p).add_const (q * Real.negMulLog 1)))
    using 1 <;> simp [Function.comp_def, mean] <;> ring

private theorem deriv_gapFirst {p q c x : ℝ} (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) :
    HasDerivAt (gapFirst p q c) (gapSecond p q c x) x := by
  have hm := mean_pos hp hq x
  unfold gapFirst gapSecond
  convert (((hasDerivAt_id x).sub_const 1).const_mul (2 * c)).sub
    (((hasDerivAt_id x).const_mul (2 * p)).mul (deriv_logRatio hp hq hx)) using 1
  field_simp [hx.ne', hm.ne'] <;> ring

private theorem deriv_gapSecond {p q c x : ℝ} (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) :
    HasDerivAt (gapSecond p q c) (gapThird p q x) x := by
  have hm := mean_pos hp hq x
  have hfrac := (hasDerivAt_const x (4 * p * q)).div (deriv_mean p q x) hm.ne'
  unfold gapSecond gapThird
  convert ((hasDerivAt_const x (2 * c)).sub
    ((deriv_logRatio hp hq hx).const_mul (2 * p))).sub hfrac using 1
  simp only [zero_mul, zero_sub]
  field_simp [hx.ne', hm.ne'] <;> unfold mean <;> ring

private theorem gap_at_one {p q c : ℝ} (hsum : p + q = 1) :
    gap p q c 1 = 0 := by
  simp [gap, entropy, hsum]

private theorem gapFirst_at_one {p q c : ℝ} (hsum : p + q = 1) :
    gapFirst p q c 1 = 0 := by
  simp [gapFirst, logRatio, mean, hsum]

private theorem gap_at_ratio {p q : ℝ} (hp : 0 < p) (hsum : p + q = 1) (hne : p ≠ q) :
    gap p q (sharpConstant p q) (q / p) = 0 ∧ gapFirst p q (sharpConstant p q) (q / p) = 0 := by
  let r := q / p
  have hpr : p * r = q := by
    dsimp [r]
    field_simp [hp.ne'] <;> ring
  have hm : mean p q r = r := by
    calc
      mean p q r = (p * r) * r + p * r := by rw [hpr]; unfold mean; ring
      _ = (p + q) * r := by rw [hpr]; ring
      _ = r := by rw [hsum, one_mul]
  have hrsub : r - 1 = (q - p) / p := by
    dsimp [r]
    field_simp [hp.ne'] <;> ring
  have hc : sharpConstant p q * (r - 1) = q * Real.log r := by
    rw [sharpConstant, if_neg hne, hrsub]
    change p * q * Real.log r / (q - p) * ((q - p) / p) = _
    field_simp [hp.ne', sub_ne_zero.mpr (Ne.symm hne)] <;> ring
  have hlog : logRatio p q r = Real.log r := by
    unfold logRatio
    rw [hm, Real.log_pow]
    norm_num <;> ring
  change gap p q (sharpConstant p q) r = 0 ∧ gapFirst p q (sharpConstant p q) r = 0
  constructor
  · have hcost : sharpConstant p q * (r - 1) ^ 2 = q * Real.log r * (r - 1) := by
      rw [pow_two, ← mul_assoc, hc]
    have hpsq : p * r ^ 2 = q * r := by rw [pow_two, ← mul_assoc, hpr]
    unfold gap entropy
    rw [hcost, show p * r ^ 2 + q * 1 = r by simpa [mean] using hm]
    simp only [Real.negMulLog_one, mul_zero, add_zero, Real.negMulLog_def, Real.log_pow]
    calc
      _ = q * Real.log r * (r - 1) - (-r * Real.log r +
          (p * r ^ 2) * (2 * Real.log r)) := by norm_num <;> ring
      _ = (1 - q) * r * Real.log r - q * Real.log r := by rw [hpsq]; ring
      _ = 0 := by rw [show 1 - q = p by linarith, hpr]; ring
  · unfold gapFirst
    rw [hlog]
    calc
      _ = 2 * (sharpConstant p q * (r - 1)) - 2 * (p * r) * Real.log r := by ring
      _ = 0 := by rw [hc, hpr]; ring

-- The closed endpoints in the mean-value theorem allow comparison with x = 0.
private theorem interval_rise {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ z ∈ Ioo a b, HasDerivAt f (d z) z)
    (hs : ∀ z ∈ Ioo a b, 0 < d z) : f a < f b := by
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope f d hab hf hd
  have h := mul_pos (hs z hz) (sub_pos.mpr hab)
  rw [(eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he] at h
  exact sub_pos.mp h

private theorem interval_fall {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ z ∈ Ioo a b, HasDerivAt f (d z) z)
    (hs : ∀ z ∈ Ioo a b, d z < 0) : f b < f a := by
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope f d hab hf hd
  have h := mul_neg_of_neg_of_pos (hs z hz) (sub_pos.mpr hab)
  rw [(eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he] at h
  exact sub_neg.mp h

private theorem continuousOn_pos {f d : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hd : ∀ z, 0 < z → HasDerivAt f (d z) z) : ContinuousOn f (Icc a b) :=
  fun z hz => (hd z (ha.trans_le hz.1)).continuousAt.continuousWithinAt

-- At the unique turn of the curvature, p * s² = q. The curvature strictly
-- decreases up to the turn and strictly increases after it.
private theorem gapSecond_turn {p q c s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hturn : p * s ^ 2 = q) :
    (∀ {a b}, 0 < a → a < b → b ≤ s → gapSecond p q c b < gapSecond p q c a) ∧
    (∀ {a b}, s ≤ a → a < b → gapSecond p q c a < gapSecond p q c b) := by
  have hd (z : ℝ) (hz : 0 < z) : HasDerivAt (gapSecond p q c) (gapThird p q z) z :=
    deriv_gapSecond hp hq hz
  constructor
  · intro a b ha hab hb
    refine interval_fall hab (continuousOn_pos ha hd) (fun z hz => hd z (ha.trans hz.1)) ?_
    intro z hz
    have hz0 := ha.trans hz.1
    have hsq := (sq_lt_sq₀ hz0.le hs.le).2 (hz.2.trans_le hb)
    have hnum : p * z ^ 2 - q < 0 := by
      rw [← hturn]
      exact sub_neg.mpr (mul_lt_mul_of_pos_left hsq hp)
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hnum)
      (mul_pos hz0 (pow_pos (mean_pos hp hq z) 2))
  · intro a b ha hab
    have ha0 := hs.trans_le ha
    refine interval_rise hab (continuousOn_pos ha0 hd) (fun z hz => hd z (ha0.trans hz.1)) ?_
    intro z hz
    have hz0 := ha0.trans hz.1
    have hsq := (sq_lt_sq₀ hs.le hz0.le).2 (ha.trans_lt hz.1)
    have hnum : 0 < p * z ^ 2 - q := by
      rw [← hturn]
      exact sub_pos.mpr (mul_lt_mul_of_pos_left hsq hp)
    exact div_pos (mul_pos (by positivity) hnum)
      (mul_pos hz0 (pow_pos (mean_pos hp hq z) 2))

private theorem gap_ordered {p q c a b x : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (hab : a < b) (hx : 0 ≤ x)
    (haF : gap p q c a = 0) (hbF : gap p q c b = 0)
    (haG : gapFirst p q c a = 0) (hbG : gapFirst p q c b = 0) :
    0 ≤ gap p q c x ∧ (gap p q c x = 0 ↔ x = a ∨ x = b) := by
  let F := gap p q c
  let G := gapFirst p q c
  let H := gapSecond p q c
  have dF (z : ℝ) (hz : 0 < z) : HasDerivAt F (G z) z := deriv_gap hp hq hz
  have dG (z : ℝ) (hz : 0 < z) : HasDerivAt G (H z) z := deriv_gapFirst hp hq hz
  have dH (z : ℝ) (hz : 0 < z) : HasDerivAt H (gapThird p q z) z := deriv_gapSecond hp hq hz
  have hF : Continuous F := continuous_gap p q c
  change F a = 0 at haF
  change F b = 0 at hbF
  change G a = 0 at haG
  change G b = 0 at hbG
  -- Rolle separates the three stationary points by two curvature zeros.
  obtain ⟨m, hm, hmG⟩ := exists_hasDerivAt_eq_zero hab hF.continuousOn
    (haF.trans hbF.symm) (fun z hz => dF z (ha.trans hz.1))
  have hm0 := ha.trans hm.1
  obtain ⟨u, hu, huH⟩ := exists_hasDerivAt_eq_zero hm.1 (continuousOn_pos ha dG)
    (haG.trans hmG.symm) (fun z hz => dG z (ha.trans hz.1))
  obtain ⟨v, hv, hvH⟩ := exists_hasDerivAt_eq_zero hm.2 (continuousOn_pos hm0 dG)
    (hmG.trans hbG.symm) (fun z hz => dG z (hm0.trans hz.1))
  have hu0 := ha.trans hu.1
  obtain ⟨s, hs, hsD⟩ := exists_hasDerivAt_eq_zero (hu.2.trans hv.1)
    (continuousOn_pos hu0 dH) (huH.trans hvH.symm) (fun z hz => dH z (hu0.trans hz.1))
  have hs0 := hu0.trans hs.1
  have hturn : p * s ^ 2 = q := by
    have hden : s * mean p q s ^ 2 ≠ 0 := (mul_pos hs0 (pow_pos (mean_pos hp hq s) 2)).ne'
    unfold gapThird at hsD
    have hnum := (div_eq_zero_iff.mp hsD).resolve_right hden
    have hcoef : 4 * p * q ≠ 0 := (show 0 < 4 * p * q by positivity).ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left hcoef)
  obtain ⟨fallH, riseH⟩ := gapSecond_turn (c := c) hp hq hs0 hturn
  have hLeft (z : ℝ) (hz : 0 < z) (hzu : z < u) : 0 < H z := by
    simpa only [huH] using fallH hz hzu hs.1.le
  have hMid (z : ℝ) (huz : u < z) (hzv : z < v) : H z < 0 := by
    by_cases hzs : z ≤ s
    · simpa only [huH] using fallH hu0 huz hzs
    · simpa only [hvH] using riseH (le_of_not_ge hzs) hzv
  have hRight (z : ℝ) (hvz : v < z) : 0 < H z := by
    simpa only [hvH] using riseH hs.2.le hvz
  have riseLeft {l r : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r ≤ u) : G l < G r :=
    interval_rise hlr (continuousOn_pos hl dG) (fun z hz => dG z (hl.trans hz.1))
      (fun z hz => hLeft z (hl.trans hz.1) (hz.2.trans_le hr))
  have fallMid {l r : ℝ} (hl : u ≤ l) (hlr : l < r) (hr : r ≤ v) : G r < G l := by
    have hl0 := hu0.trans_le hl
    exact interval_fall hlr (continuousOn_pos hl0 dG) (fun z hz => dG z (hl0.trans hz.1))
      (fun z hz => hMid z (hl.trans_lt hz.1) (hz.2.trans_le hr))
  have riseRight {l r : ℝ} (hl : v ≤ l) (hlr : l < r) : G l < G r := by
    have hl0 := (hm0.trans hv.1).trans_le hl
    exact interval_rise hlr (continuousOn_pos hl0 dG) (fun z hz => dG z (hl0.trans hz.1))
      (fun z hz => hRight z (hl.trans_lt hz.1))
  have positiveGap (hxa : x ≠ a) (hxb : x ≠ b) : 0 < F x := by
    by_cases hxl : x < a
    · rw [← haF]
      refine interval_fall hxl hF.continuousOn (fun z hz => dF z (hx.trans_lt hz.1)) ?_
      intro z hz
      simpa only [haG] using riseLeft (hx.trans_lt hz.1) hz.2 hu.1.le
    have hax := lt_of_le_of_ne (le_of_not_gt hxl) hxa.symm
    by_cases hxm : x ≤ m
    · rw [← haF]
      refine interval_rise hax hF.continuousOn (fun z hz => dF z (ha.trans hz.1)) ?_
      intro z hz
      by_cases hzu : z ≤ u
      · simpa only [haG] using riseLeft ha hz.1 hzu
      · simpa only [hmG] using fallMid (le_of_not_ge hzu) (hz.2.trans_le hxm) hv.1.le
    by_cases hxr : x < b
    · rw [← hbF]
      have hmx := lt_of_not_ge hxm
      refine interval_fall hxr hF.continuousOn (fun z hz => dF z (hx.trans_lt hz.1)) ?_
      intro z hz
      by_cases hzv : z ≤ v
      · simpa only [hmG] using fallMid hu.2.le (hmx.trans hz.1) hzv
      · simpa only [hbG] using riseRight (le_of_not_ge hzv) hz.2
    have hbx := lt_of_le_of_ne (le_of_not_gt hxr) hxb.symm
    rw [← hbF]
    refine interval_rise hbx hF.continuousOn (fun z hz => dF z ((ha.trans hab).trans hz.1)) ?_
    intro z hz
    simpa only [hbG] using riseRight hv.2.le hz.1
  change 0 ≤ F x ∧ (F x = 0 ↔ x = a ∨ x = b)
  by_cases h : x = a ∨ x = b
  · have hz : F x = 0 := h.elim (fun e => e.symm ▸ haF) (fun e => e.symm ▸ hbF)
    exact ⟨hz.ge, ⟨fun _ => h, fun _ => hz⟩⟩
  · have hz := positiveGap (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
    exact ⟨hz.le, ⟨fun e => False.elim (hz.ne' e), fun e => False.elim (h e)⟩⟩

private theorem gapSecond_balanced_at_one (c : ℝ) :
    gapSecond (1 / 2) (1 / 2) c 1 = 2 * c - 1 := by
  norm_num [gapSecond, logRatio, mean]

private theorem gap_balanced {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gap (1 / 2) (1 / 2) (1 / 2) x ∧
      (gap (1 / 2) (1 / 2) (1 / 2) x = 0 ↔ x = 1) := by
  let F := gap (1 / 2) (1 / 2) (1 / 2)
  let G := gapFirst (1 / 2) (1 / 2) (1 / 2)
  let H := gapSecond (1 / 2) (1 / 2) (1 / 2)
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hF : Continuous F := continuous_gap _ _ _
  have dF (z : ℝ) (hz : 0 < z) : HasDerivAt F (G z) z := deriv_gap hp hp hz
  have dG (z : ℝ) (hz : 0 < z) : HasDerivAt G (H z) z := deriv_gapFirst hp hp hz
  have hF1 : F 1 = 0 := gap_at_one (by norm_num)
  have hG1 : G 1 = 0 := gapFirst_at_one (by norm_num)
  have hH1 : H 1 = 0 := by
    dsimp [H]
    rw [gapSecond_balanced_at_one]
    norm_num
  obtain ⟨fallH, riseH⟩ := gapSecond_turn (c := 1 / 2) hp hp
    (show (0 : ℝ) < 1 by norm_num) (by norm_num)
  change 0 ≤ F x ∧ (F x = 0 ↔ x = 1)
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hGneg (z : ℝ) (hz : 0 < z) (hz1 : z < 1) : G z < 0 := by
      rw [← hG1]
      refine interval_rise hz1 (continuousOn_pos hz dG) (fun t ht => dG t (hz.trans ht.1)) ?_
      intro t ht
      simpa only [hH1] using fallH (hz.trans ht.1) ht.2 le_rfl
    have hpos : F 1 < F x :=
      interval_fall hlt hF.continuousOn (fun z hz => dF z (hx.trans_lt hz.1))
        (fun z hz => hGneg z (hx.trans_lt hz.1) hz.2)
    rw [hF1] at hpos
    exact ⟨hpos.le, ⟨fun e => False.elim (hpos.ne' e),
      fun e => False.elim (hlt.ne e)⟩⟩
  · subst x
    simp [hF1]
  · have hGpos (z : ℝ) (hz : 1 < z) : 0 < G z := by
      rw [← hG1]
      refine interval_rise hz (continuousOn_pos zero_lt_one dG)
        (fun t ht => dG t (zero_lt_one.trans ht.1)) ?_
      intro t ht
      simpa only [hH1] using riseH le_rfl ht.1
    have hpos : F 1 < F x :=
      interval_rise hgt hF.continuousOn (fun z hz => dF z (zero_lt_one.trans hz.1))
        (fun z hz => hGpos z hz.1)
    rw [hF1] at hpos
    exact ⟨hpos.le, ⟨fun e => False.elim (hpos.ne' e),
      fun e => False.elim (hgt.ne' e)⟩⟩

private theorem gap_normalized {p q x : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hx : 0 ≤ x) :
    0 ≤ gap p q (sharpConstant p q) x ∧
      (gap p q (sharpConstant p q) x = 0 ↔ x = 1 ∨ (p ≠ q ∧ x = q / p)) := by
  by_cases heq : p = q
  · subst q
    have hhalf : p = 1 / 2 := by linarith
    subst p
    simpa [sharpConstant] using gap_balanced hx
  · have haF : gap p q (sharpConstant p q) 1 = 0 := gap_at_one hsum
    have haG : gapFirst p q (sharpConstant p q) 1 = 0 := gapFirst_at_one hsum
    obtain ⟨hbF, hbG⟩ := gap_at_ratio hp hsum heq
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hab : 1 < q / p := (lt_div_iff₀ hp).2 (by simpa using hlt)
      simpa [heq] using gap_ordered hp hq zero_lt_one hab hx haF hbF haG hbG
    · have hba : q / p < 1 := (div_lt_iff₀ hp).2 (by simpa using hgt)
      simpa [heq, or_comm] using
        gap_ordered hp hq (div_pos hq hp) hba hx hbF haF hbG haG

private theorem entropy_bound_pos_right {p q x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q = 1) (hx : 0 ≤ x) (hy : 0 < y) :
    entropy p q (x ^ 2) (y ^ 2) ≤ sharpConstant p q * (x - y) ^ 2 ∧
      (entropy p q (x ^ 2) (y ^ 2) = sharpConstant p q * (x - y) ^ 2 ↔
        x = y ∨ (p ≠ q ∧ p * x = q * y)) := by
  let t := x / y
  obtain ⟨hle, heq⟩ := gap_normalized hp hq hsum (div_nonneg hx hy.le)
  change 0 ≤ sharpConstant p q * (t - 1) ^ 2 - entropy p q (t ^ 2) 1 at hle
  change gap p q (sharpConstant p q) t = 0 ↔ t = 1 ∨ (p ≠ q ∧ t = q / p) at heq
  have hdiff : y * (t - 1) = x - y := by
    dsimp [t]
    field_simp [hy.ne'] <;> ring
  have hsquare : y ^ 2 * t ^ 2 = x ^ 2 := by
    dsimp [t]
    field_simp [hy.ne'] <;> ring
  have hent : entropy p q (x ^ 2) (y ^ 2) = y ^ 2 * entropy p q (t ^ 2) 1 := by
    simpa only [hsquare, mul_one] using entropy_scale (p := p) (q := q) (y ^ 2) (t ^ 2) 1
  have hcost :
      sharpConstant p q * (x - y) ^ 2 = y ^ 2 * (sharpConstant p q * (t - 1) ^ 2) := by
    rw [← hdiff, mul_pow]
    ring
  have hdiag : t = 1 ↔ x = y := by
    dsimp [t]
    rw [div_eq_iff hy.ne', one_mul]
  have hratio : t = q / p ↔ p * x = q * y := by
    dsimp [t]
    rw [div_eq_div_iff hy.ne' hp.ne', mul_comm x p]
  have hzero :
      entropy p q (t ^ 2) 1 = sharpConstant p q * (t - 1) ^ 2 ↔
        gap p q (sharpConstant p q) t = 0 := by
    rw [gap, sub_eq_zero, eq_comm]
  rw [hent, hcost]
  refine ⟨mul_le_mul_of_nonneg_left (sub_nonneg.mp hle) (sq_nonneg y), ?_⟩
  rw [mul_right_inj' (pow_ne_zero 2 hy.ne'), hzero, heq, hdiag, hratio]

/-- The sharp two-point bound and all its equality cases, including inputs with a zero value.
For positive `y` and unequal weights, the nonconstant equality condition is `x / y = q / p`. -/
theorem entropy_le_and_eq_iff {p q x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropy p q (x ^ 2) (y ^ 2) ≤ sharpConstant p q * (x - y) ^ 2 ∧
      (entropy p q (x ^ 2) (y ^ 2) = sharpConstant p q * (x - y) ^ 2 ↔
        x = y ∨ (p ≠ q ∧ p * x = q * y)) := by
  by_cases hypos : 0 < y
  · exact entropy_bound_pos_right hp hq hsum hx hypos
  by_cases hxpos : 0 < x
  · have hswap := entropy_bound_pos_right hq hp ((add_comm q p).trans hsum) hy hxpos
    have hsquare : (y - x) ^ 2 = (x - y) ^ 2 := by ring
    rw [entropy_swap p q (x ^ 2) (y ^ 2), constant_swap hp hq, hsquare] at hswap
    exact ⟨hswap.1, hswap.2.trans <| or_congr eq_comm (and_congr ne_comm eq_comm)⟩
  have hxx : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
  have hyy : y = 0 := le_antisymm (le_of_not_gt hypos) hy
  simp [hxx, hyy, entropy]

-- With equal weights the optimal constant is forced by the curvature at 1.
private theorem balanced_constant_le {c : ℝ}
    (hbound : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      entropy (1 / 2) (1 / 2) (x ^ 2) (y ^ 2) ≤ c * (x - y) ^ 2) :
    (1 : ℝ) / 2 ≤ c := by
  by_contra h
  have hc : c < 1 / 2 := lt_of_not_ge h
  let F := gap (1 / 2) (1 / 2) c
  let G := gapFirst (1 / 2) (1 / 2) c
  let H := gapSecond (1 / 2) (1 / 2) c
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hF : Continuous F := continuous_gap _ _ _
  have dF (z : ℝ) (hz : 0 < z) : HasDerivAt F (G z) z := deriv_gap hp hp hz
  have dG (z : ℝ) (hz : 0 < z) : HasDerivAt G (H z) z := deriv_gapFirst hp hp hz
  have hF1 : F 1 = 0 := gap_at_one (by norm_num)
  have hG1 : G 1 = 0 := gapFirst_at_one (by norm_num)
  have hH1 : H 1 < 0 := by
    change gapSecond _ _ _ _ < 0
    rw [gapSecond_balanced_at_one]
    linarith
  have hcH : ContinuousAt H 1 :=
    (deriv_gapSecond (c := c) hp hp zero_lt_one).continuousAt
  have hn : H ⁻¹' Iio 0 ∈ nhds (1 : ℝ) := hcH.preimage_mem_nhds (Iio_mem_nhds hH1)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let t := (1 + b) / 2
  have ht : 1 < t := by dsimp [t]; linarith [hab.2]
  have htb : t < b := by dsimp [t]; linarith [hab.2]
  have hGneg (z : ℝ) (hz : z ∈ Ioo 1 t) : G z < 0 := by
    rw [← hG1]
    refine interval_fall hz.1 (continuousOn_pos zero_lt_one dG)
      (fun w hw => dG w (zero_lt_one.trans hw.1)) ?_
    intro w hw
    exact hsub ⟨hab.1.trans hw.1, hw.2.trans (hz.2.trans htb)⟩
  have hFt : F t < F 1 := interval_fall ht hF.continuousOn
    (fun z hz => dF z (zero_lt_one.trans hz.1)) hGneg
  have hnonneg : 0 ≤ F t := by
    unfold F gap
    exact sub_nonneg.mpr (by simpa only [one_pow] using
      hbound t 1 (zero_lt_one.trans ht).le zero_le_one)
  exact (not_lt_of_ge hnonneg) (hF1 ▸ hFt)

/-- Every coefficient valid for all nonnegative inputs is at least the sharp coefficient. -/
theorem constant_le_of_entropy_bound {p q c : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q = 1)
    (hbound : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      entropy p q (x ^ 2) (y ^ 2) ≤ c * (x - y) ^ 2) :
    sharpConstant p q ≤ c := by
  by_cases heq : p = q
  · subst q
    have hhalf : p = 1 / 2 := by linarith
    subst p
    rw [sharpConstant, if_pos rfl]
    exact balanced_constant_le hbound
  · let r := q / p
    have hr : 0 < r := div_pos hq hp
    have hpr : p * r = q := by
      dsimp [r]
      field_simp [hp.ne'] <;> ring
    have hrne : r ≠ 1 := by
      intro h
      rw [h, mul_one] at hpr
      exact heq hpr
    have hwitness := (entropy_le_and_eq_iff hp hq hsum hr.le zero_le_one).2.mpr
      (Or.inr ⟨heq, hpr.trans (mul_one q).symm⟩)
    have hle := hbound r 1 hr.le zero_le_one
    rw [hwitness] at hle
    have hpos : 0 < (r - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrne)
    exact le_of_mul_le_mul_right hle hpos

end Omega.MeasureTheory.TwoPointLogSobolev
