/- GID: D5/S3/Fourier/Concentration/ActiveCosineConstraints
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ActiveCosineConstraints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both lower cosine moment bounds are active at a least-squared-mass weight. -/

import D5.S3.Fourier.Concentration.ClippedMomentWeights
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Nat.Prime.Basic

/-! Strict moment comparisons and active constraints on the first two modes of a finite cycle. -/

open Finset AddChar

noncomputable section

namespace D5.S3.Fourier.Concentration.ActiveCosineConstraints

private def clip (t x : ℝ) : ℝ := max 0 (1 - t * (1 - x))

private theorem clip_mono {t : ℝ} (ht : 0 ≤ t) : Monotone (clip t) := by
  intro x y hxy
  exact max_le_max le_rfl (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hxy)])

private theorem clip_lt {t x y : ℝ} (ht : 0 < t) (hxy : x < y)
    (hy : 0 < clip t y) : clip t x < clip t y := by
  change max 0 (1 - t * (1 - x)) < clip t y
  refine max_lt_iff.mpr ⟨hy, ?_⟩
  exact (by nlinarith [mul_pos ht (sub_pos.mpr hxy)] :
    1 - t * (1 - x) < 1 - t * (1 - y)).trans_le (le_max_right _ _)

private theorem clip_defect {t x y : ℝ} (ht : 0 < t) :
    0 ≤ clip t y ^ 2 - clip t x ^ 2 - 2 * t * (clip t x * (y - x)) ∧
    (x < y → 0 < clip t y →
      0 < clip t y ^ 2 - clip t x ^ 2 - 2 * t * (clip t x * (y - x))) := by
  by_cases hx : 1 - t * (1 - x) ≤ 0
  · rw [show clip t x = 0 from max_eq_left hx]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, zero_mul, mul_zero]
    exact ⟨sq_nonneg _, fun _ hy => sq_pos_of_pos hy⟩
  · have hx' : 0 < 1 - t * (1 - x) := lt_of_not_ge hx
    rw [show clip t x = 1 - t * (1 - x) from max_eq_right hx'.le]
    by_cases hy : 1 - t * (1 - y) ≤ 0
    · rw [show clip t y = 0 from max_eq_left hy]
      have h : t * (y - x) ≤ -(1 - t * (1 - x)) := by linarith
      refine ⟨?_, fun _ hp => (lt_irrefl _ hp).elim⟩
      nlinarith only [sq_nonneg (1 - t * (1 - x)),
        mul_nonneg hx'.le (sub_nonneg.mpr h)]
    · rw [show clip t y = 1 - t * (1 - y) from max_eq_right (le_of_not_ge hy)]
      have heq : (1 - t * (1 - y)) ^ 2 - (1 - t * (1 - x)) ^ 2 -
          2 * t * ((1 - t * (1 - x)) * (y - x)) = (t * (y - x)) ^ 2 := by ring
      rw [heq]
      exact ⟨sq_nonneg _, fun hxy _ => sq_pos_of_pos (mul_pos ht (sub_pos.mpr hxy))⟩

variable {q : ℕ} [NeZero q]

private def cosine (k : ZMod q) : ℝ := (ZMod.stdAddChar k).re

private theorem cosine_angle (k : ZMod q) :
    cosine k = Real.cos (2 * Real.pi * (k.val : ℝ) / q) := by
  rw [cosine, ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

private theorem cosine_double_angle (k : ZMod q) :
    cosine (2 * k) = Real.cos (4 * Real.pi * (k.val : ℝ) / q) := by
  have hcast : ((2 * (k.val : ℤ) : ℤ) : ZMod q) = 2 * k := by
    simp [Int.cast_mul]
  rw [cosine, ← hcast, ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

private theorem cosine_zero : cosine (0 : ZMod q) = 1 := by
  simp [cosine]

private theorem cosine_mean (m : ZMod q) (hm : m ≠ 0) :
    (∑ k : ZMod q, cosine (m * k)) = 0 := by
  have hh : (∑ k : ZMod q, ZMod.stdAddChar (m * k)) = 0 :=
    sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hm)
  simpa only [cosine, map_sum, Complex.reCLM_apply, Complex.zero_re] using
    congrArg (Complex.reCLM : ℂ →L[ℝ] ℝ) hh

omit [NeZero q] in
private theorem two_ne_zero_of_four_le (hq : 4 ≤ q) : (2 : ZMod q) ≠ 0 := by
  intro h
  have hv : (2 : ZMod q).val = 2 := ZMod.val_natCast_of_lt (n := q) (a := 2) (by omega)
  rw [h, ZMod.val_zero] at hv
  omega

omit [NeZero q] in
private theorem one_ne_zero_of_four_le (hq : 4 ≤ q) : (1 : ZMod q) ≠ 0 := by
  intro h
  have hv := ZMod.val_one'' (by omega : q ≠ 1)
  rw [h, ZMod.val_zero] at hv
  omega

private theorem cosine_one_order (hq : 4 ≤ q) :
    0 ≤ cosine (1 : ZMod q) ∧ cosine (1 : ZMod q) < 1 := by
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
  let θ : ℝ := 2 * Real.pi / q
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ' : θ ≤ Real.pi / 2 := by
    dsimp only [θ]
    apply (div_le_iff₀ (show (0 : ℝ) < q by linarith)).2
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hqR)]
  have hp := Real.cos_le_cos_of_nonneg_of_le_pi hθ.le
    (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]) hθ'
  have hlt := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show θ ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hθ.le, by linarith [Real.pi_pos]⟩) hθ
  rw [Real.cos_pi_div_two] at hp
  rw [Real.cos_zero] at hlt
  simpa only [cosine_angle, ZMod.val_one'' (by omega : q ≠ 1), Nat.cast_one, mul_one, θ]
    using And.intro hp hlt

private theorem cosine_le_at_one (hq : 4 ≤ q) (k : ZMod q) (hk : k ≠ 0) :
    cosine k ≤ cosine (1 : ZMod q) := by
  have hqR : (0 : ℝ) < q := by positivity
  let angle (n : ℕ) : ℝ := (2 * Real.pi / q) * n
  have hp : 0 < 2 * Real.pi / (q : ℝ) := by positivity
  have hf (n : ℕ) (h₁ : 1 ≤ n) (h₂ : n + n ≤ q) :
      Real.cos (angle n) ≤ Real.cos (angle 1) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (show 0 ≤ angle 1 by dsimp [angle]; positivity)
    · have hn : (n : ℝ) + n ≤ q := by exact_mod_cast h₂
      dsimp only [angle]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hqR).2
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn)]
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast h₁) hp.le
  have hk' := ZMod.val_pos.mpr hk
  have hval := ZMod.val_lt k
  have hc (i : ZMod q) : cosine i = Real.cos (angle i.val) := by
    rw [cosine_angle]
    congr 1
    dsimp only [angle]
    ring
  rw [hc, hc, ZMod.val_one'' (by omega : q ≠ 1)]
  by_cases h : k.val + k.val ≤ q
  · exact hf _ (by omega) h
  · have hangle : angle (q - k.val) = 2 * Real.pi - angle k.val := by
      dsimp only [angle]
      rw [Nat.cast_sub hval.le]
      field_simp [hqR.ne']
    rw [← Real.cos_two_pi_sub (angle k.val), ← hangle]
    exact hf _ (by omega) (by omega)

private theorem cosine_difference (k : ZMod q) :
    cosine k - cosine (2 * k) = (1 - cosine k) * (2 * cosine k + 1) := by
  rw [cosine_angle, cosine_double_angle,
    show 4 * Real.pi * (k.val : ℝ) / q = 2 * (2 * Real.pi * (k.val : ℝ) / q) by ring,
    Real.cos_two_mul]
  ring

private theorem clip_total_pos (b : ZMod q → ℝ) (hb : b 0 = 1) (t : ℝ) :
    0 < ∑ k, clip t (b k) := by
  apply sum_pos' (fun k _ => le_max_left _ _)
  refine ⟨0, mem_univ _, ?_⟩
  simp [hb]

private theorem clip_at_one_pos (b : ZMod q → ℝ) (hb : b 0 = 1)
    (hupper : ∀ k, b k ≠ 1 → b k ≤ cosine (1 : ZMod q))
    {a t : ℝ} (ht : 0 ≤ t) (ha : a < 1)
    (hm : (∑ k, clip t (b k) / (∑ j, clip t (b j)) * b k) = a) :
    0 < clip t (cosine (1 : ZMod q)) := by
  by_contra! h
  have hz (k : ZMod q) : clip t (b k) * b k = clip t (b k) := by
    by_cases hk : b k = 1
    · rw [hk, mul_one]
    · have hclip : clip t (b k) = 0 :=
        le_antisymm ((clip_mono ht (hupper k hk)).trans h) (le_max_left _ _)
      simp [hclip]
  have he : (∑ k, clip t (b k) / (∑ j, clip t (b j)) * b k) = 1 := by
    simp_rw [div_mul_eq_mul_div, hz, ← sum_div]
    exact div_self (clip_total_pos b hb t).ne'
  linarith

private theorem clip_sums_first (hq : 4 ≤ q) {t : ℝ} (ht : 0 < t)
    (hw : 0 < clip t (cosine (1 : ZMod q))) :
    (∑ k : ZMod q, clip t (cosine k) * cosine (2 * k)) <
      ∑ k : ZMod q, clip t (cosine k) * cosine k := by
  have hc : (∑ k : ZMod q, cosine k) = 0 := by
    simpa only [one_mul] using cosine_mean (1 : ZMod q) (one_ne_zero_of_four_le hq)
  have hd := cosine_mean (2 : ZMod q) (two_ne_zero_of_four_le hq)
  have hbal : (∑ k : ZMod q, (cosine k - cosine (2 * k)) * clip t (-1 / 2)) = 0 := by
    rw [← sum_mul, sum_sub_distrib, hc, hd, sub_self, zero_mul]
  have hpos : 0 < ∑ k : ZMod q,
      (cosine k - cosine (2 * k)) * (clip t (cosine k) - clip t (-1 / 2)) := by
    apply sum_pos'
    · intro k _
      have hk : cosine k ≤ 1 := (cosine_angle k).trans_le (Real.cos_le_one _)
      rw [cosine_difference]
      by_cases h : -(1 : ℝ) / 2 ≤ cosine k
      · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hk) (by linarith))
          (sub_nonneg.mpr (clip_mono ht.le h))
      · exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) (by linarith [le_of_not_ge h]))
          (sub_nonpos.mpr (clip_mono ht.le (le_of_not_ge h)))
    · obtain ⟨hlo, hhi⟩ := cosine_one_order hq
      refine ⟨1, mem_univ _, ?_⟩
      rw [cosine_difference]
      exact mul_pos (mul_pos (sub_pos.mpr hhi) (by linarith))
        (sub_pos.mpr (clip_lt ht (by linarith) hw))
  have hz : (∑ k : ZMod q,
      (cosine k - cosine (2 * k)) * (clip t (cosine k) - clip t (-1 / 2))) =
      (∑ k : ZMod q, clip t (cosine k) * cosine k) -
        ∑ k : ZMod q, clip t (cosine k) * cosine (2 * k) := by
    simp_rw [mul_sub, sum_sub_distrib, hbal, sub_zero, sub_mul, sum_sub_distrib]
    simp only [mul_comm (cosine _) (clip _ _)]
  linarith

private theorem clip_sums_odd (hq : 4 ≤ q) (hodd : Odd q) {t : ℝ} (ht : 0 < t)
    (hw : 0 < clip t (cosine (1 : ZMod q))) :
    (∑ k : ZMod q, clip t (cosine (2 * k)) * cosine k) <
      ∑ k : ZMod q, clip t (cosine (2 * k)) * cosine (2 * k) := by
  let u := ZMod.unitOfCoprime 2 hodd.coprime_two_left
  have hperm : (∑ k : ZMod q, clip t (cosine (2 * k)) ^ 2) =
      ∑ k : ZMod q, clip t (cosine k) ^ 2 := by
    simpa [u, Units.mulLeft_apply] using
      Equiv.sum_comp u.mulLeft (fun k => clip t (cosine k) ^ 2)
  have hlt : cosine (2 * (1 : ZMod q)) < cosine (1 : ZMod q) := by
    apply sub_pos.mp
    rw [cosine_difference]
    obtain ⟨hlo, hhi⟩ := cosine_one_order hq
    exact mul_pos (sub_pos.mpr hhi) (by linarith)
  have hp : 0 < ∑ k : ZMod q,
      (clip t (cosine k) ^ 2 - clip t (cosine (2 * k)) ^ 2 -
        2 * t * (clip t (cosine (2 * k)) * (cosine k - cosine (2 * k)))) := by
    apply sum_pos'
    · intro k _
      exact (clip_defect ht).1
    · exact ⟨1, mem_univ _, (clip_defect ht).2 hlt hw⟩
  simp_rw [sum_sub_distrib, hperm, sub_self, ← mul_sum, mul_sub, sum_sub_distrib] at hp
  by_contra! h
  have hnonneg := mul_nonneg (show 0 ≤ 2 * t by positivity) (sub_nonneg.mpr h)
  linarith

private theorem clip_sums_even (heven : Even q) (t : ℝ) :
    (∑ k : ZMod q, clip t (cosine (2 * k)) * cosine k) = 0 := by
  obtain ⟨n, hn⟩ := heven
  let shift : ZMod q := n
  have hnR : (q : ℂ) = (n : ℂ) + n := by exact_mod_cast hn
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hchar : ZMod.stdAddChar shift = -1 := by
    rw [show shift = ((n : ℤ) : ZMod q) by simp [shift]]
    rw [ZMod.stdAddChar_coe, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    apply (div_eq_iff hqC).2
    rw [hnR]
    ring
  have hshift : (2 : ZMod q) * shift = 0 := by
    rw [two_mul]
    change (n : ZMod q) + (n : ZMod q) = 0
    rw [← Nat.cast_add, ← hn, ZMod.natCast_self]
  have hc (k : ZMod q) : cosine (shift + k) = -cosine k := by
    simp [cosine, map_add_eq_mul, hchar]
  have hd (k : ZMod q) : cosine (2 * (shift + k)) = cosine (2 * k) := by
    rw [mul_add, hshift, zero_add]
  let f (k : ZMod q) : ℝ := clip t (cosine (2 * k)) * cosine k
  have hh := Equiv.sum_comp (Equiv.addLeft shift) f
  change (∑ k, clip t (cosine (2 * (shift + k))) * cosine (shift + k)) = ∑ k, f k at hh
  simp only [hc, hd, mul_neg, sum_neg_distrib] at hh
  change -(∑ k, f k) = ∑ k, f k at hh
  change (∑ k, f k) = 0
  linarith

section Optimization

variable {ι : Type*} [Fintype ι]

private def probability (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1

private def moment (c w : ι → ℝ) : ℝ := ∑ i, w i * c i

private def energy (w : ι → ℝ) : ℝ := ∑ i, w i ^ 2

private def minimum (F : (ι → ℝ) → Prop) (w : ι → ℝ) : Prop :=
  F w ∧ ∀ v, F v → energy w ≤ energy v

private theorem clipped_minimum (b : ι → ℝ) (hb : ∃ i, b i = 1) (hmean : (∑ i, b i) = 0)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    ∃ t : ℝ, 0 < t ∧
      let v := fun i => clip t (b i) / ∑ j, clip t (b j)
      probability v ∧ moment b v = a ∧
      ∀ w, probability w → a ≤ moment b w →
        (∑ i, (w i - v i) ^ 2) ≤ energy w - energy v := by
  obtain ⟨t, ht, _, _, hn, hs, hm, hgap⟩ :=
    ClippedMomentWeights.exists_clipped_moment_minimizer b hb ha'
  rw [hmean, zero_div, max_eq_right ha.le] at hm
  have htp : 0 < t := by
    by_contra! h
    have hz := le_antisymm h ht
    subst t
    simp only [zero_mul, sub_zero, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hm
    rw [← mul_sum, hmean, mul_zero] at hm
    linarith
  refine ⟨t, htp, ⟨hn, hs⟩, hm, ?_⟩
  intro w hw hwb
  exact (hgap w hw.2).2 hw.1 hwb

private theorem energy_strict_of_distance {w v : ι → ℝ} (hne : w ≠ v)
    (hgap : (∑ i, (w i - v i) ^ 2) ≤ energy w - energy v) :
    energy v < energy w := by
  have hex : ∃ i, w i ≠ v i := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < ∑ i, (w i - v i) ^ 2 :=
    sum_pos' (fun j _ => sq_nonneg _) ⟨i, mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
  linarith

private theorem tight_opposite {c d w v : ι → ℝ} {a : ℝ}
    (hw : minimum (fun u => probability u ∧ a ≤ moment c u ∧ a ≤ moment d u) w)
    (hv : probability v) (hvc : a ≤ moment c v) (hvd : moment d v < a)
    (he : energy v < energy w) : moment d w = a := by
  apply le_antisymm _ hw.1.2.2
  by_contra! hslack
  let fraction : ℝ := (moment d w - a) / (moment d w - moment d v)
  have hden : 0 < moment d w - moment d v := sub_pos.mpr (hvd.trans hslack)
  have hl : 0 < fraction := div_pos (sub_pos.mpr hslack) hden
  have hl' : fraction ≤ 1 := (div_le_one hden).2 (by linarith)
  have hlmul : fraction * (moment d w - moment d v) = moment d w - a :=
    div_mul_cancel₀ _ hden.ne'
  let mix (i : ι) : ℝ := (1 - fraction) * w i + fraction * v i
  have hnonneg : 0 ≤ 1 - fraction := sub_nonneg.mpr hl'
  have hp : probability mix := by
    refine ⟨fun i => add_nonneg (mul_nonneg hnonneg (hw.1.1.1 i))
      (mul_nonneg hl.le (hv.1 i)), ?_⟩
    simp only [mix, sum_add_distrib, ← mul_sum, hw.1.1.2, hv.2, mul_one]
    ring
  have hm (b : ι → ℝ) : moment b mix = (1 - fraction) * moment b w + fraction * moment b v := by
    simp only [moment, mix, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  have hmc : a ≤ moment c mix := by
    rw [hm]
    nlinarith only [mul_nonneg hnonneg (sub_nonneg.mpr hw.1.2.1),
      mul_nonneg hl.le (sub_nonneg.mpr hvc)]
  have hmd : moment d mix = a := by rw [hm]; linarith only [hlmul]
  have henergy : energy mix ≤ (1 - fraction) * energy w + fraction * energy v := by
    simp only [energy, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    dsimp only [mix]
    nlinarith only [mul_nonneg (mul_nonneg hl.le hnonneg) (sq_nonneg (w i - v i))]
  have hstrict : (1 - fraction) * energy w + fraction * energy v < energy w := by
    nlinarith only [mul_pos hl (sub_pos.mpr he)]
  exact (not_lt_of_ge (hw.2 mix ⟨hp, hmc, hmd.ge⟩)) (henergy.trans_lt hstrict)

end Optimization

private theorem cosine_active (hq : 4 ≤ q) {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    let c := fun k : ZMod q => cosine k
    let d := fun k : ZMod q => cosine (2 * k)
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment c w) w →
      moment c w = a ∧ moment d w < a) ∧
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment d w) w →
      moment d w = a ∧ moment c w < a ∧ (Even q → moment c w = 0)) ∧
    ∀ w, minimum (fun w => probability w ∧ a ≤ moment c w ∧ a ≤ moment d w) w →
      moment c w = a ∧ moment d w = a := by
  dsimp only
  let c := fun k : ZMod q => cosine k
  let d := fun k : ZMod q => cosine (2 * k)
  have hc : c 0 = 1 := cosine_zero
  have hd : d 0 = 1 := by simpa [d] using (cosine_zero (q := q))
  have hcm : (∑ k, c k) = 0 := by
    simpa only [one_mul] using cosine_mean (1 : ZMod q) (one_ne_zero_of_four_le hq)
  have hdm : (∑ k, d k) = 0 := cosine_mean (2 : ZMod q) (two_ne_zero_of_four_le hq)
  obtain ⟨s, hs, hvs, hsc, hsgap⟩ := clipped_minimum c ⟨0, hc⟩ hcm ha ha'.le
  obtain ⟨t, ht, hvt, htd, htgap⟩ := clipped_minimum d ⟨0, hd⟩ hdm ha ha'.le
  let vs := fun k => clip s (c k) / ∑ j, clip s (c j)
  let vt := fun k => clip t (d k) / ∑ j, clip t (d j)
  have hsd : moment d vs < a := by
    have hw := clip_at_one_pos c hc (fun k hk =>
      cosine_le_at_one hq k (fun h => hk (by simpa only [h] using hc))) hs.le ha' hsc
    have hsum := clip_sums_first hq hs hw
    rw [← hsc]
    change moment d vs < moment c vs
    simp only [moment, vs, div_mul_eq_mul_div, ← sum_div]
    exact div_lt_div_of_pos_right hsum (clip_total_pos c hc s)
  have hEven (heven : Even q) : moment c vt = 0 := by
    simp only [moment, vt, div_mul_eq_mul_div, ← sum_div]
    rw [clip_sums_even heven t, zero_div]
  have htc : moment c vt < a := by
    rcases Nat.even_or_odd q with heven | hodd
    · rw [hEven heven]
      exact ha
    · have hw := clip_at_one_pos d hd (fun k hk =>
        cosine_le_at_one hq (2 * k) (fun h => hk (by simpa only [d, h] using (cosine_zero (q := q))))) ht.le ha' htd
      have hsum := clip_sums_odd hq hodd ht hw
      rw [← htd]
      change moment c vt < moment d vt
      simp only [moment, vt, div_mul_eq_mul_div, ← sum_div]
      exact div_lt_div_of_pos_right hsum (clip_total_pos d hd t)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have heq : w = vs := by
      by_contra hne
      exact (not_lt_of_ge (hw.2 vs ⟨hvs, hsc.ge⟩))
        (energy_strict_of_distance hne (hsgap w hw.1.1 hw.1.2))
    exact ⟨by simpa only [heq] using hsc, by simpa only [heq] using hsd⟩
  · intro w hw
    have heq : w = vt := by
      by_contra hne
      exact (not_lt_of_ge (hw.2 vt ⟨hvt, htd.ge⟩))
        (energy_strict_of_distance hne (htgap w hw.1.1 hw.1.2))
    exact ⟨by simpa only [heq] using htd, by simpa only [heq] using htc,
      by simpa only [heq] using hEven⟩
  · intro w hw
    have hslt := energy_strict_of_distance (w := w) (v := vs)
      (fun h => (not_lt_of_ge (by simpa only [h] using hw.1.2.2)) hsd) (hsgap w hw.1.1 hw.1.2.1)
    have htlt := energy_strict_of_distance (w := w) (v := vt)
      (fun h => (not_lt_of_ge (by simpa only [h] using hw.1.2.1)) htc) (htgap w hw.1.1 hw.1.2.2)
    have hswap : minimum (fun u => probability u ∧ a ≤ moment d u ∧ a ≤ moment c u) w :=
      ⟨⟨hw.1.1, hw.1.2.2, hw.1.2.1⟩, fun u hu => hw.2 u ⟨hu.1, hu.2.2, hu.2.1⟩⟩
    exact ⟨tight_opposite hswap hvt htd.ge htc htlt, tight_opposite hw hvs hsc.ge hsd hslt⟩

/-- Each singly constrained minimum violates the opposite lower cosine bound strictly.
Consequently both lower bounds are attained at every jointly constrained minimum. -/
theorem active_cosine_constraints (hq : 4 ≤ q) {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    let c := fun k : ZMod q => Real.cos (2 * Real.pi * (k.val : ℝ) / q)
    let d := fun k : ZMod q => Real.cos (4 * Real.pi * (k.val : ℝ) / q)
    let square := fun x : ℝ => x ^ 2
    let probability := fun w : ZMod q → ℝ => (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1
    let moment := fun b w : ZMod q → ℝ => ∑ k, w k * b k
    let energy := fun w : ZMod q → ℝ => ∑ k, square (w k)
    let minimum := fun (F : (ZMod q → ℝ) → Prop) w =>
      F w ∧ ∀ v, F v → energy w ≤ energy v
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment c w) w →
      moment c w = a ∧ moment d w < a) ∧
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment d w) w →
      moment d w = a ∧ moment c w < a ∧ (Even q → moment c w = 0)) ∧
    ∀ w, minimum (fun w => probability w ∧ a ≤ moment c w ∧ a ≤ moment d w) w →
      moment c w = a ∧ moment d w = a := by
  have h := cosine_active (q := q) hq ha ha'
  dsimp only at h
  have hd : (fun k : ZMod q => cosine (2 * k)) =
      (fun k => Real.cos (4 * Real.pi * (k.val : ℝ) / q)) :=
    funext cosine_double_angle
  have hc : (fun k : ZMod q => cosine k) =
      (fun k => Real.cos (2 * Real.pi * (k.val : ℝ) / q)) :=
    funext cosine_angle
  rw [hd, hc] at h
  exact h

end D5.S3.Fourier.Concentration.ActiveCosineConstraints
