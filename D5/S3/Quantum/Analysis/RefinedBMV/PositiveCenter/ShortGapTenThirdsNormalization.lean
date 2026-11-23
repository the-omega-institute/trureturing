/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirdsNormalization
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform logarithmic slope bounds for the short-gap normalization from ten thirds. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortEvenTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapMoments
import Batteries.Tactic.OpenPrivate

/-! Logarithmic slopes of the two factors in the normalized short-gap kernel.
The weight in both factors is `shortGapWeight`, which unfolds to `CompactGap.W`. -/

open Set

namespace RefinedBMV.PositiveCenter

open private stride_tail_bound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortEvenTails
open private hasDerivAt_shortGapWeight from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapMoments
open private hasDerivAt_exp_decay from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailAverage

private theorem tenThirds_gap_scale {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 10 / 3 ≤ t) : 20 / 3 < (3 + 2 * h) * upperTailGap h t := by
  let x : ℝ := h * (10 / 3)
  let D : ℝ := 1 + x + x ^ 2 / 2
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hInv : Real.exp (-x) ≤ D⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hD (Real.quadratic_le_exp_of_nonneg hx)
  have hgap : (10 / 3) * (1 + x / 2) / D ≤ upperTailGap h (10 / 3) := by
    change _ ≤ (1 - Real.exp (-x)) / h
    apply (le_div_iff₀ hh).mpr
    calc
      _ = 1 - D⁻¹ := by
        field_simp [hD.ne']
        dsimp only [D, x]
        ring
      _ ≤ _ := sub_le_sub_left hInv 1
  have hmono : Monotone (upperTailGap h) :=
    monotone_of_deriv_nonneg
      (fun s ↦ (hasDerivAt_upperTailGap (t := s) hh).differentiableAt)
      (fun s ↦ by rw [(hasDerivAt_upperTailGap (t := s) hh).deriv]; positivity)
  have hh2 : h ^ 2 ≤ (3 / 11 : ℝ) ^ 2 := pow_le_pow_left₀ hh.le hhmax 2
  have hpoly : (20 / 3) * D < (3 + 2 * h) * ((10 / 3) * (1 + x / 2)) := by
    dsimp only [D, x]
    nlinarith only [hh.le, hh2]
  calc
    _ < (3 + 2 * h) * ((10 / 3) * (1 + x / 2) / D) := by
      rw [← mul_div_assoc]
      exact (lt_div_iff₀ hD).mpr hpoly
    _ ≤ _ := mul_le_mul_of_nonneg_left (hgap.trans (hmono ht)) (by positivity)

private theorem sinh_le_at_tenThirds_radius {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ 5 / 11) :
    Real.sinh x ≤ x * (726 / 701) := by
  have hs : Summable (fun n : ℕ ↦ x ^ (1 + 2 * n) / ((1 + 2 * n).factorial : ℝ)) := by
    simpa only [Nat.add_comm 1] using (Real.hasSum_sinh x).summable
  rw [Real.sinh_eq_tsum]
  calc
    _ ≤ x ^ 1 / ((1 : ℕ).factorial : ℝ) / (1 - (5 / 11 : ℝ) ^ 2 / 6) := by
      have h := stride_tail_bound 1 hx hxmax (by norm_num) hs
      simpa only [Nat.add_comm 1] using h
    _ = _ := by norm_num [Nat.factorial] <;> ring

private theorem tenThirds_correction_bound {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 10 / 3 ≤ t) :
    ((3 + h) / 2) * upperTailGap h t ^ 2 * Real.exp (-((1 - h) * t)) < 7 / 10 := by
  let S (s : ℝ) := upperTailGap h s ^ 2 * Real.exp (-((1 - h) * s))
  have hd (s : ℝ) : HasDerivAt S
      ((2 * upperTailGap h s * Real.exp (-(h * s)) -
        (1 - h) * upperTailGap h s ^ 2) * Real.exp (-((1 - h) * s))) s := by
    convert ((hasDerivAt_upperTailGap (t := s) hh).pow 2).mul
      (hasDerivAt_exp_decay (1 - h) s) using 1
    simp only [Pi.pow_apply]
    ring
  have hmono : AntitoneOn S (Ici (10 / 3)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      (fun s _ ↦ (hd s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hd s).differentiableAt.differentiableWithinAt)
    intro s hs
    have hsmin : 10 / 3 ≤ s := interior_subset hs
    have hspos : 0 < s := by linarith only [hsmin]
    have ha : 0 < upperTailGap h s := by
      rw [expGapMean_eq hh]
      exact mul_pos hspos (expGapMean_pos h s)
    have hL := (upperTailSlope_bounds hh hspos).2.1.trans
      (one_div_le_one_div_of_le (by norm_num) hsmin)
    have hb := upperTailGap_logDeriv hh hspos
    rw [(hasDerivAt_upperTailGap (t := s) hh).deriv] at hb
    rw [(hd s).deriv, (div_eq_iff ha.ne').mp hb]
    have hsign : 2 * upperTailSlope h s - (1 - h) ≤ 0 := by
      linarith only [hL, hhmax]
    convert mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (upperTailGap h s)) hsign)
      (Real.exp_pos (-((1 - h) * s))).le using 1
    ring
  have hS : S t ≤ S (10 / 3) :=
    hmono (self_mem_Ici : (10 / 3 : ℝ) ∈ Ici (10 / 3)) (mem_Ici.mpr ht) ht
  let x : ℝ := h * (10 / 3) / 2
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hxmax : x ≤ 5 / 11 := by dsimp only [x]; linarith only [hhmax]
  have hsplit : Real.exp (-((1 - h) * (10 / 3))) =
      Real.exp (-(10 / 3 : ℝ)) * Real.exp x ^ 2 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [x]
    ring
  have hhyper : upperTailGap h (10 / 3) * Real.exp x = 2 * Real.sinh x / h := by
    rw [upperTailGap, div_mul_eq_mul_div, sub_mul, one_mul, ← Real.exp_add, Real.sinh_eq,
      show -(h * (10 / 3)) + x = -x by dsimp only [x]; ring]
    ring
  have hscaled : upperTailGap h (10 / 3) * Real.exp x ≤ (10 / 3) * (726 / 701) := by
    rw [hhyper]
    apply (div_le_iff₀ hh).mpr
    have h := sinh_le_at_tenThirds_radius hx hxmax
    dsimp only [x] at h
    linarith only [h]
  have ha : 0 < upperTailGap h (10 / 3) := by
    rw [expGapMean_eq hh]
    exact mul_pos (by norm_num) (expGapMean_pos h _)
  have hsquare := pow_le_pow_left₀ (mul_pos ha (Real.exp_pos x)).le hscaled 2
  have hexp : 28 < Real.exp (10 / 3 : ℝ) := by
    have hTaylor := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 3) 13
    norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
    linarith only [hTaylor]
  have he : Real.exp (-(10 / 3 : ℝ)) < 1 / 28 := by
    rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hexp
  have hS₀ : S (10 / 3) ≤ ((10 / 3) * (726 / 701)) ^ 2 * (1 / 28) := calc
    S (10 / 3) = (upperTailGap h (10 / 3) * Real.exp x) ^ 2 * Real.exp (-(10 / 3 : ℝ)) := by
      dsimp only [S]
      rw [hsplit]
      ring
    _ ≤ _ := mul_le_mul hsquare he.le (Real.exp_pos _).le (by positivity)
  calc
    _ = ((3 + h) / 2) * S t := by dsimp only [S]; ring
    _ ≤ (18 / 11) * (((10 / 3) * (726 / 701)) ^ 2 * (1 / 28)) :=
      mul_le_mul (by linarith only [hhmax]) (hS.trans hS₀)
        (by dsimp only [S]; positivity) (by norm_num)
    _ < _ := by norm_num

private theorem tenThirds_normalization_of_rate {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 10 / 3 ≤ t) :
    let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    let α := deriv P t / P t
    let β := deriv V t / V t
    0 < α ∧ α ≤ upperTailSlope h t / 2 ∧ upperTailSlope h t / 2 ≤ 1 / (2 * t) ∧
      -(1 / t) < β ∧ β ≤ -(upperTailSlope h t / 2) ∧ -(upperTailSlope h t / 2) < 0 := by
  let a := upperTailGap h t
  let b := Real.exp (-(h * t))
  let k : ℝ := 3 + 2 * h
  let g : ℝ := 3 + h
  let c : ℝ := g * k / 2
  let E := Real.exp (-(k * t))
  let W := shortGapWeight h t
  let w := k * (b - E) + c * a * Real.exp (-t) * (a - 2 * b)
  let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
  let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
  let α := deriv P t / P t
  let β := deriv V t / V t
  have htpos : 0 < t := by linarith only [ht]
  have ha : 0 < a := by
    dsimp only [a]
    rw [expGapMean_eq hh]
    exact mul_pos htpos (expGapMean_pos h t)
  have hb : 0 < b := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hk : 0 < k := by dsimp only [k]; positivity
  have hg : 0 < g := by dsimp only [g]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hW : 0 < W := shortGapWeight_pos hh htpos
  have hwd : HasDerivAt (shortGapWeight h) w t := hasDerivAt_shortGapWeight hh
  have hL : b / a = upperTailSlope h t := by
    simpa only [(hasDerivAt_upperTailGap (t := t) hh).deriv] using upperTailGap_logDeriv hh htpos
  obtain ⟨hLpos, hLle, _⟩ := upperTailSlope_bounds hh htpos

  -- The two strict scalar estimates give a positive numerator for the left slope.
  have hka : 0 < k * a := mul_pos hk ha
  have hks : 20 / 3 < k * a := tenThirds_gap_scale hh hhmax ht
  have hfirst : 2 / (k * a) ≤ 3 / 10 :=
    (div_le_iff₀ hka).mpr (by linarith only [hks])
  have hscalar : 2 / (k * a) + (g / 2) * a ^ 2 * Real.exp (-((1 - h) * t)) < 1 := by
    have hsecond : (g / 2) * a ^ 2 * Real.exp (-((1 - h) * t)) < 7 / 10 :=
      tenThirds_correction_bound hh hhmax ht
    linarith only [hfirst, hsecond]
  have hdecay : b * Real.exp (-((1 - h) * t)) = Real.exp (-t) := by
    dsimp only [b]
    rw [← Real.exp_add]
    congr 1
    ring
  have hcore : 0 < b * (k * a - 2) - c * a ^ 3 * Real.exp (-t) := calc
    0 < b * (k * a) * (1 - (2 / (k * a) + (g / 2) * a ^ 2 * Real.exp (-((1 - h) * t)))) :=
      mul_pos (mul_pos hb hka) (sub_pos.mpr hscalar)
    _ = b * (k * a - 2) - c * a ^ 3 * (b * Real.exp (-((1 - h) * t))) := by
      dsimp only [c]
      field_simp [hka.ne', hk.ne', ha.ne'] <;> ring
    _ = _ := by rw [hdecay]
  have hnum : 0 < 2 * b * W - a * w := by
    have heq : 2 * b * W - a * w =
        b * (k * a - 2) - c * a ^ 3 * Real.exp (-t) + (2 * b + k * a) * E := by
      change 2 * b * (E - 1 + k * a - c * a ^ 2 * Real.exp (-t)) -
        a * (k * (b - E) + c * a * Real.exp (-t) * (a - 2 * b)) = _
      ring
    rw [heq]
    exact add_pos hcore (mul_pos (by positivity) hE)

  -- The geometric bound controls the other cross-multiplied numerator.
  have hba : b ≤ a := by
    have hrecip : 1 / t ≤ 1 := (div_le_one htpos).mpr (by linarith only [ht])
    have hratio : b / a ≤ 1 := hL.le.trans (hLle.trans hrecip)
    simpa only [one_mul] using (div_le_iff₀ ha).mp hratio
  have hgap : h * a + b = 1 := by
    dsimp only [a, b, upperTailGap]
    field_simp [hh.ne'] <;> ring
  have hgeom : 0 ≤ b - (b + k * a) * E := by
    have hsum : b + k * a ≤ Real.exp (g * t) := calc
      b + k * a = 1 + g * a := by
        dsimp only [k, g]
        linear_combination hgap
      _ ≤ 1 + g * t :=
        add_le_add_left (mul_le_mul_of_nonneg_left (upperTailGap_le hh) hg.le) 1
      _ ≤ _ := by simpa only [add_comm (g * t) 1] using Real.add_one_le_exp (g * t)
    apply sub_nonneg.mpr
    calc
      _ ≤ Real.exp (g * t) * E := mul_le_mul_of_nonneg_right hsum hE.le
      _ = b := by
        dsimp only [E, b, g, k]
        rw [← Real.exp_add]
        congr 1
        ring
  have hcompare : b * W ≤ a * w := by
    have heq : a * w - b * W =
        b - (b + k * a) * E + c * a ^ 2 * Real.exp (-t) * (a - b) := by
      change a * (k * (b - E) + c * a * Real.exp (-t) * (a - 2 * b)) -
        b * (E - 1 + k * a - c * a ^ 2 * Real.exp (-t)) = _
      ring
    apply sub_nonneg.mp
    rw [heq]
    exact add_nonneg hgeom (mul_nonneg (by positivity) (sub_nonneg.mpr hba))
  have hwlo : b / a / 2 ≤ w / (2 * W) := by
    rw [div_div]
    exact (div_le_div_iff₀ (by positivity : 0 < a * 2) (by positivity : 0 < 2 * W)).mpr
      (by nlinarith only [hcompare])
  have hwhi : w / (2 * W) < b / a :=
    (div_lt_div_iff₀ (by positivity : 0 < 2 * W) ha).mpr (by nlinarith only [hnum])

  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hβ : β = -(w / (2 * W)) := by
    change deriv (fun s ↦ 1 / Real.sqrt (shortGapWeight h s)) t / (1 / Real.sqrt W) = _
    rw [((hasDerivAt_const t (1 : ℝ)).fun_div (hwd.sqrt hW.ne') hs.ne').deriv]
    change (0 * Real.sqrt W - 1 * (w / (2 * Real.sqrt W))) / (Real.sqrt W) ^ 2 /
      (1 / Real.sqrt W) = _
    calc
      _ = -(w / (2 * (Real.sqrt W) ^ 2)) := by field_simp [hs.ne'] <;> ring
      _ = _ := by rw [Real.sq_sqrt hW.le]
  have hlog : α - β = upperTailSlope h t := shortGapNormalization_logDiff hh htpos
  have hαpos : 0 < α := by linarith only [hlog, hL, hβ, hwhi]
  change 0 < α ∧ α ≤ upperTailSlope h t / 2 ∧ upperTailSlope h t / 2 ≤ 1 / (2 * t) ∧
    -(1 / t) < β ∧ β ≤ -(upperTailSlope h t / 2) ∧ -(upperTailSlope h t / 2) < 0
  refine ⟨hαpos, by linarith only [hlog, hL, hβ, hwlo], ?_,
    by linarith only [hlog, hLle, hαpos], by linarith only [hL, hβ, hwlo],
    neg_neg_of_pos (div_pos hLpos (by norm_num))⟩
  rw [show 1 / (2 * t) = (1 / t) / 2 by rw [div_div, mul_comm t]]
  exact div_le_div_of_nonneg_right hLle (by norm_num)

/-- The two logarithmic slopes of the short-gap kernel at and above ten thirds. -/
theorem shortGapNormalization_bounds_of_ten_thirds_le {p : ℕ} (hp : 11 ≤ p)
    {t : ℝ} (ht : 10 / 3 ≤ t) :
    let h := 3 / (p : ℝ)
    let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    let α := deriv P t / P t
    let β := deriv V t / V t
    0 < α ∧ α ≤ upperTailSlope h t / 2 ∧ upperTailSlope h t / 2 ≤ 1 / (2 * t) ∧
      -(1 / t) < β ∧ β ≤ -(upperTailSlope h t / 2) ∧ -(upperTailSlope h t / 2) < 0 := by
  have hpR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact tenThirds_normalization_of_rate (h := 3 / (p : ℝ))
    (div_pos (by norm_num) (by linarith only [hpR]))
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR) ht

/-- The two logarithmic slopes together contribute at most one half to the gap derivative. -/
theorem shortGapNormalization_slopeDifference_le_half_of_ten_thirds_le
    {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} (hu : 10 / 3 ≤ u) (huv : u < v) :
    let h := 3 / (p : ℝ)
    let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
    let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
    deriv P u / P u - deriv V v / V v ≤ 1 / 2 := by
  let h := 3 / (p : ℝ)
  let P := fun s ↦ upperTailGap h s / Real.sqrt (shortGapWeight h s)
  let V := fun s ↦ 1 / Real.sqrt (shortGapWeight h s)
  change deriv P u / P u - deriv V v / V v ≤ _
  have hv : 10 / 3 ≤ v := hu.trans huv.le
  have hU := shortGapNormalization_bounds_of_ten_thirds_le hp hu
  have hV := shortGapNormalization_bounds_of_ten_thirds_le hp hv
  have hα : deriv P u / P u ≤ 1 / (2 * u) := hU.2.1.trans hU.2.2.1
  have hβ : -(1 / v) < deriv V v / V v := hV.2.2.2.1
  have hu' : 1 / (2 * u) ≤ 3 / 20 := calc
    _ ≤ 1 / (2 * (10 / 3 : ℝ)) := one_div_le_one_div_of_le (by norm_num)
      (mul_le_mul_of_nonneg_left hu (by norm_num))
    _ = _ := by norm_num
  have hv' : 1 / v ≤ 3 / 10 := calc
    _ ≤ 1 / (10 / 3 : ℝ) := one_div_le_one_div_of_le (by norm_num) hv
    _ = _ := by norm_num
  have hsum : deriv P u / P u - deriv V v / V v < 9 / 20 := by
    linarith only [hα, hβ, hu', hv']
  exact hsum.le.trans (by norm_num)

#print axioms shortGapNormalization_bounds_of_ten_thirds_le
#print axioms shortGapNormalization_slopeDifference_le_half_of_ten_thirds_le

end RefinedBMV.PositiveCenter
