/- GID: D5/S3/Analytic/Asymptotics/OneSidedTailCurvature
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/OneSidedTailCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monotone count bounds the weighted primitive's central second difference from above. -/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A monotone count on the image of a compact positive log interval gives a
one-sided quadratic bound for the weighted second difference of its tail
primitive. The proof compares adjacent interval integrals.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace OneSidedTailCurvature

noncomputable section

def q (v : ℝ) : ℝ := (v + 1) / v ^ 2

def r (V : ℝ → ℝ) (v : ℝ) : ℝ := 1 - Real.exp (-v) * V (Real.exp v)

/-- The pointwise estimate from the order of the two count values. -/
private theorem residual_sub_le {V : ℝ → ℝ} {s t : ℝ}
    (hV : V (Real.exp s) ≤ V (Real.exp t)) :
    r V t - r V s ≤ (1 - Real.exp (-(t - s))) * (1 - r V s) := by
  have he : Real.exp (-(t - s)) * Real.exp (-s) = Real.exp (-t) := by
    rw [← Real.exp_add, show -(t - s) + -s = -t by ring]
  calc
    r V t - r V s =
        Real.exp (-s) * V (Real.exp s) - Real.exp (-t) * V (Real.exp t) := by
      unfold r
      ring
    _ ≤ Real.exp (-s) * V (Real.exp s) - Real.exp (-t) * V (Real.exp s) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le) _
    _ = (1 - Real.exp (-(t - s))) * (1 - r V s) := by
      unfold r
      rw [← he]
      ring

/-- An upper bound on the left endpoint value of `1 - r` controls the increment of `r`. -/
private theorem residual_sub_le_mul {V : ℝ → ℝ} {s t M : ℝ} (hst : s ≤ t)
    (hV : V (Real.exp s) ≤ V (Real.exp t)) (hM : 0 ≤ M) (hs : 1 - r V s ≤ M) :
    r V t - r V s ≤ M * (t - s) := by
  have he : 0 ≤ 1 - Real.exp (-(t - s)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sub_nonneg.mpr hst)))
  have he' : 1 - Real.exp (-(t - s)) ≤ t - s := by
    linarith only [Real.add_one_le_exp (-(t - s))]
  calc
    r V t - r V s ≤ (1 - Real.exp (-(t - s))) * (1 - r V s) := residual_sub_le hV
    _ ≤ (1 - Real.exp (-(t - s))) * M := mul_le_mul_of_nonneg_left hs he
    _ ≤ (t - s) * M := mul_le_mul_of_nonneg_right he' hM
    _ = M * (t - s) := mul_comm _ _

/-- The two upper estimates on the integrand that suffice for the weighted primitive. -/
theorem weighted_second_difference_le {f k : ℝ → ℝ} {a b B L t h : ℝ}
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hf : IntervalIntegrable f volume a b)
    (hk : ∀ ⦃x y⦄, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      k y - k x = ∫ v in x..y, f v)
    (hbound : ∀ x ∈ Icc a b, f x ≤ B)
    (hinc : ∀ ⦃x y⦄, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      f y - f x ≤ L * (y - x))
    (hh : 0 ≤ h) (hlow : a ≤ t - h) (hhigh : t + h ≤ b) :
    (t + h) * k (t + h) + (t - h) * k (t - h) - 2 * t * k t ≤
      (b * L + 2 * B) * h ^ 2 := by
  have hlt : t - h ≤ t := by linarith only [hh]
  have htr : t ≤ t + h := by linarith only [hh]
  have ht : t ∈ Icc a b := ⟨hlow.trans hlt, htr.trans hhigh⟩
  have hminus : t - h ∈ Icc a b := ⟨hlow, hlt.trans ht.2⟩
  have hplus : t + h ∈ Icc a b := ⟨ht.1.trans htr, hhigh⟩
  have hab : a ≤ b := ht.1.trans ht.2
  have hleft : IntervalIntegrable f volume (t - h) t := by
    apply hf.mono_set
    rw [uIcc_of_le hlt, uIcc_of_le hab]
    exact Icc_subset_Icc hlow ht.2
  have hright : IntervalIntegrable f volume t (t + h) := by
    apply hf.mono_set
    rw [uIcc_of_le htr, uIcc_of_le hab]
    exact Icc_subset_Icc ht.1 hhigh
  have hshift : IntervalIntegrable (fun x => f (x + h)) volume (t - h) t := by
    apply (IntervalIntegrable.comp_add_right_iff (f := f) (c := h)
      (a := t - h) (b := t) (by finiteness)).2
    simpa only [sub_add_cancel] using hright
  have htranslate :
      (∫ x in t - h..t, f (x + h)) = ∫ x in t..t + h, f x := by
    simpa only [sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (a := t - h) (b := t) f h)
  have hdifference :
      (∫ x in t..t + h, f x) - (∫ x in t - h..t, f x) ≤ L * h ^ 2 := by
    calc
      (∫ x in t..t + h, f x) - (∫ x in t - h..t, f x) =
          ∫ x in t - h..t, f (x + h) - f x := by
        rw [intervalIntegral.integral_sub hshift hleft, htranslate]
      _ ≤ (∫ _ in t - h..t, L * h) := by
        apply intervalIntegral.integral_mono_on hlt (hshift.sub hleft) intervalIntegrable_const
        intro x hx
        have hx' : x ∈ Icc a b := ⟨hlow.trans hx.1, hx.2.trans ht.2⟩
        have hxx : x ≤ x + h := le_add_of_nonneg_right hh
        have hxh : x + h ∈ Icc a b :=
          ⟨hx'.1.trans hxx, (add_le_add_left hx.2 h).trans hhigh⟩
        have hi := hinc hx' hxh hxx
        rwa [show x + h - x = h by ring] at hi
      _ = L * h ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hleft_bound : (∫ x in t - h..t, f x) ≤ h * B := by
    calc
      (∫ x in t - h..t, f x) ≤ ∫ _ in t - h..t, B :=
        intervalIntegral.integral_mono_on hlt hleft intervalIntegrable_const
          (fun x hx => hbound x ⟨hlow.trans hx.1, hx.2.trans ht.2⟩)
      _ = h * B := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show t - (t - h) = h by ring]
  calc
    (t + h) * k (t + h) + (t - h) * k (t - h) - 2 * t * k t =
        (t + h) * ((k (t + h) - k t) - (k t - k (t - h))) +
          (2 * h) * (k t - k (t - h)) := by ring
    _ = (t + h) * ((∫ x in t..t + h, f x) - (∫ x in t - h..t, f x)) +
          (2 * h) * (∫ x in t - h..t, f x) := by
      rw [hk ht hplus htr, hk hminus ht hlt]
    _ ≤ (t + h) * (L * h ^ 2) + (2 * h) * (h * B) :=
      add_le_add (mul_le_mul_of_nonneg_left hdifference (ha.trans hplus.1))
        (mul_le_mul_of_nonneg_left hleft_bound (mul_nonneg (by norm_num) hh))
    _ ≤ b * (L * h ^ 2) + (2 * h) * (h * B) :=
      add_le_add (mul_le_mul_of_nonneg_right hhigh (mul_nonneg hL (sq_nonneg h))) le_rfl
    _ = (b * L + 2 * B) * h ^ 2 := by ring

private theorem q_sub_bounds {a s t : ℝ} (ha : 0 < a) (has : a ≤ s) (hst : s ≤ t) :
    0 ≤ q s - q t ∧
      q s - q t ≤ ((1 / a) ^ 2 * (1 + 2 * (1 / a))) * (t - s) := by
  have hs : 0 < s := ha.trans_le has
  have ht : 0 < t := hs.trans_le hst
  have hs_inv : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha has
  have ht_inv : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha (has.trans hst)
  have hsum : 1 + 1 / s + 1 / t ≤ 1 + 2 * (1 / a) := by
    linarith only [hs_inv, ht_inv]
  have hprod : (1 / s) * (1 / t) ≤ (1 / a) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hs_inv ht_inv (by positivity : 0 ≤ 1 / t) (by positivity : 0 ≤ 1 / a)
  have hfactor : (1 / s) * (1 / t) * (1 + 1 / s + 1 / t) ≤
      (1 / a) ^ 2 * (1 + 2 * (1 / a)) :=
    mul_le_mul hprod hsum (by positivity) (sq_nonneg (1 / a))
  have heq : q s - q t = (t - s) * ((1 / s) * (1 / t) * (1 + 1 / s + 1 / t)) := by
    unfold q
    field_simp [ne_of_gt hs, ne_of_gt ht]
    ring
  rw [heq]
  exact ⟨mul_nonneg (sub_nonneg.mpr hst) (by positivity),
    (mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hst)).trans_eq (mul_comm _ _)⟩

/-- A single finite constant bounds the weighted second difference on the compact log interval.
With `M` the maximum of the absolute endpoint counts, take `R = 1 + M`,
`Lq = (1/a)^2 * (1 + 2/a)`, and `C = b * (q a * M + Lq * R) + 2 * (q a * R)`. -/
theorem weighted_tail_curvature {V k : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hV : MonotoneOn V (Icc (Real.exp a) (Real.exp b)))
    (hf : IntervalIntegrable (fun x => q x * r V x) volume a b)
    (hk : ∀ ⦃x y⦄, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      k y - k x = ∫ v in x..y, q v * r V v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃t h : ℝ⦄, 0 ≤ h → a ≤ t - h → t + h ≤ b →
      (t + h) * k (t + h) + (t - h) * k (t - h) - 2 * t * k t ≤ C * h ^ 2 := by
  let M : ℝ := max |V (Real.exp a)| |V (Real.exp b)|
  let R : ℝ := 1 + M
  let Lq : ℝ := (1 / a) ^ 2 * (1 + 2 * (1 / a))
  let L : ℝ := q a * M + Lq * R
  have hM : 0 ≤ M := (abs_nonneg (V (Real.exp a))).trans (le_max_left _ _)
  have hR : 0 ≤ R := add_nonneg zero_le_one hM
  have hLq : 0 ≤ Lq := by
    dsimp [Lq]
    positivity
  have hexp {x : ℝ} (hx : x ∈ Icc a b) : Real.exp x ∈ Icc (Real.exp a) (Real.exp b) :=
    ⟨Real.exp_le_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
  have hcount {x : ℝ} (hx : x ∈ Icc a b) : |V (Real.exp x)| ≤ M := by
    have hends : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    have hlow := hV ⟨le_rfl, hends⟩ (hexp hx) (Real.exp_le_exp.mpr hx.1)
    have hhigh := hV (hexp hx) ⟨hends, le_rfl⟩ (Real.exp_le_exp.mpr hx.2)
    have hleft : |V (Real.exp a)| ≤ M := le_max_left _ _
    have hright : |V (Real.exp b)| ≤ M := le_max_right _ _
    exact abs_le.mpr ⟨(abs_le.mp hleft).1.trans hlow, hhigh.trans (abs_le.mp hright).2⟩
  have hscaled {x : ℝ} (hx : x ∈ Icc a b) : |1 - r V x| ≤ M := by
    have hx0 : 0 ≤ x := ha.le.trans hx.1
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)
    rw [show 1 - r V x = Real.exp (-x) * V (Real.exp x) by unfold r; ring,
      abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans
      (by simpa only [one_mul] using hcount hx)
  have hr {x : ℝ} (hx : x ∈ Icc a b) : |r V x| ≤ R := by
    have hs := abs_le.mp (hscaled hx)
    change |r V x| ≤ 1 + M
    exact abs_le.mpr ⟨by linarith only [hs.2], by linarith only [hs.1]⟩
  have hq0 {x : ℝ} (hx : 0 < x) : 0 ≤ q x := by
    unfold q
    positivity
  have hq {x : ℝ} (hx : x ∈ Icc a b) : q x ≤ q a :=
    sub_nonneg.mp (q_sub_bounds ha le_rfl hx.1).1
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (hq0 ha) hM) (mul_nonneg hLq hR)
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : q x * r V x ≤ q a * R :=
    (mul_le_mul_of_nonneg_left (abs_le.mp (hr hx)).2 (hq0 (ha.trans_le hx.1))).trans
      (mul_le_mul_of_nonneg_right (hq hx) hR)
  have hinc ⦃x y : ℝ⦄ (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      q y * r V y - q x * r V x ≤ L * (y - x) := by
    have hri := residual_sub_le_mul hxy
      (hV (hexp hx) (hexp hy) (Real.exp_le_exp.mpr hxy)) hM (abs_le.mp (hscaled hx)).2
    have hqi := q_sub_bounds ha hx.1 hxy
    have hleft : q y * (r V y - r V x) ≤ q a * (M * (y - x)) :=
      (mul_le_mul_of_nonneg_left hri (hq0 (ha.trans_le hy.1))).trans
        (mul_le_mul_of_nonneg_right (hq hy) (mul_nonneg hM (sub_nonneg.mpr hxy)))
    have hrneg : -r V x ≤ R := by
      simpa only [neg_neg] using neg_le_neg (abs_le.mp (hr hx)).1
    have hright : (q x - q y) * (-r V x) ≤ (Lq * (y - x)) * R :=
      (mul_le_mul_of_nonneg_left hrneg hqi.1).trans (mul_le_mul_of_nonneg_right hqi.2 hR)
    calc
      q y * r V y - q x * r V x =
          q y * (r V y - r V x) + (q x - q y) * (-r V x) := by ring
      _ ≤ q a * (M * (y - x)) + (Lq * (y - x)) * R := add_le_add hleft hright
      _ = L * (y - x) := by
        dsimp [L]
        ring
  refine ⟨b * L + 2 * (q a * R), ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (ha.le.trans hab) hL)
      (mul_nonneg (by norm_num) (mul_nonneg (hq0 ha) hR))
  · intro t h hh hlow hhigh
    exact weighted_second_difference_le ha.le hL hf hk hbound hinc hh hlow hhigh

end

end OneSidedTailCurvature
