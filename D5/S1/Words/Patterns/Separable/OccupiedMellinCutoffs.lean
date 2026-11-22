/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinCutoffs
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals]
   utility: none
   digest: Uniform absolute cutoffs for paired occupation Mellin samples. -/

import D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.LinearCombination

/-! Bounds at the origin, the center singularity, and the far end complement
the regular-cell comparison of paired occupation Mellin samples. -/

open MeasureTheory
namespace D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs

open OccupiedMellinInterior

private theorem symmetric_rpow_second_difference
    {β a n m : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 3 / 4) (ha : 0 ≤ a)
    (hn : 0 < n) (hm : 0 ≤ m) (hmn : m ≤ n / 2) :
    |(a + (n+m)) ^ (-β) + (a + (n-m)) ^ (-β) - 2*(a+n)^(-β)| ≤
      32 * m^2 * n^(-β-2) := by
  let f : ℝ → ℝ := fun x => (a+x)^(-β)
  let F : ℝ → ℝ := fun x => -β * (a+x)^(-β-1)
  let C := (16 : ℝ) * n^(-β-2)
  let S := Set.Icc (n / 2) (n+m)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.rpow_nonneg hn.le _)
  have hD (x : ℝ) (hx : 0 < a+x) : HasDerivAt f (F x) x := by
    have hi : HasDerivAt (fun x : ℝ => a+x) 1 x := (hasDerivAt_id x).const_add a
    simpa only [f, F, mul_one, Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx.ne')).comp x hi
  have hDF (x : ℝ) (hx : 0 < a+x) :
      HasDerivAt F ((-β)*((-β-1)*(a+x)^(-β-2))) x := by
    have hi : HasDerivAt (fun x : ℝ => a+x) 1 x := (hasDerivAt_id x).const_add a
    have he : (-β-1)-1 = -β-2 := by ring
    simpa only [F, he, mul_one, Function.comp_def] using
      ((Real.hasDerivAt_rpow_const (p := -β-1) (Or.inl hx.ne')).comp x hi).const_mul (-β)
  have hbound (x : ℝ) (hx : x ∈ S) :
      ‖(-β)*((-β-1)*(a+x)^(-β-2))‖ ≤ C := by
    have hxp : 0 < a+x := by linarith [hx.1]
    have hfirst : (a+x)^(-β-2) ≤ (n / 2)^(-β-2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hx.1]) (by linarith)
    have hsecond : (n / 2)^(-β-2) ≤ 8 * n^(-β-2) := by
      rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm (n^(-β-2))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      calc
        _ ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 8 := by norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hβ0,
      abs_of_nonpos (show -β-1 ≤ 0 by linarith),
      abs_of_nonneg (Real.rpow_nonneg hxp.le _), ← mul_assoc]
    have hfac : β * -(-β-1) ≤ 2 := by
      nlinarith only [hβ0, hβ1, mul_nonneg hβ0 (sub_nonneg.mpr hβ1)]
    calc
      _ ≤ 2 * (a+x)^(-β-2) :=
        mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hxp.le _)
      _ ≤ C := by
        dsimp [C]
        linarith only [hfirst.trans hsecond]
  have hLip (u v : ℝ) (hu : u ∈ S) (hv : v ∈ S) : |F v - F u| ≤ C * |v-u| := by
    have h := (convex_Icc (n / 2) (n+m)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hDF x (by linarith [hx.1])).hasDerivWithinAt) hbound hu hv
    simpa only [Real.norm_eq_abs] using h
  let g : ℝ → ℝ := fun t => f (n+t) + f (n-t) - 2*f n
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) m) :
      HasDerivWithinAt g (F (n+t)-F (n-t)) (Set.Icc 0 m) t := by
    have hp : HasDerivAt (fun t : ℝ => n+t) 1 t := (hasDerivAt_id t).const_add n
    have hq : HasDerivAt (fun t : ℝ => n-t) (-1) t := (hasDerivAt_id t).const_sub n
    have h := ((hD (n+t) (by linarith [ht.1])).comp t hp).add
      ((hD (n-t) (by linarith [ht.2])).comp t hq)
    simpa only [g, mul_one, mul_neg, sub_eq_add_neg, Function.comp_def, Pi.add_apply] using
      (h.sub_const (2*f n)).hasDerivWithinAt
  have hgB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) m) :
      ‖F (n+t) - F (n-t)‖ ≤ 2*C*m := by
    have hu : n-t ∈ S := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hv : n+t ∈ S := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [Real.norm_eq_abs]
    apply (hLip _ _ hu hv).trans
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ n+t-(n-t))]
    have h := mul_le_mul_of_nonneg_left ht.2 hC
    nlinarith only [h]
  have h := (convex_Icc (0 : ℝ) m).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg hgB (show (0 : ℝ) ∈ Set.Icc 0 m from ⟨le_rfl, hm⟩)
    (show m ∈ Set.Icc 0 m from ⟨hm, le_rfl⟩)
  have hg0 : g 0 = 0 := by simp only [g, add_zero, sub_zero]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hg0, sub_zero, sub_zero, abs_of_nonneg hm] at h
  change |g m| ≤ _
  convert h using 1
  dsimp [C]
  ring

private theorem small_sample_bound {β a s : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hs : 0 < s) (hs₁ : s ≤ 1 / 2) :
    |sample β a s| ≤ 32 * s ^ (1 / 2 : ℝ) := by
  have h := symmetric_rpow_second_difference (a := a) (n := 1) (m := s)
    hβ₀ hβ₁ ha zero_lt_one hs.le (by simpa using hs₁)
  rw [Real.one_rpow, mul_one] at h
  unfold sample
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
  apply (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hs.le _)).trans_eq
  have hpow : s ^ (-(3 / 2 : ℝ)) * s ^ (2 : ℕ) = s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    norm_num
  linear_combination 32 * hpow

private theorem far_sample_bound {β a s : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) (hs : 2 ≤ s) :
    |sample β a s| ≤ 2 * s ^ (-(3 / 2:ℝ)) := by
  have h₁ : 1 ≤ a+(1+s) := by linarith
  have h₂ : 1 ≤ a+|1 - s| := by
    rw [abs_of_neg (show 1-s < 0 by linarith)]
    linarith
  have h₃ : 1 ≤ a+1 := by linarith
  have hc (x : ℝ) (hx : 1 ≤ x) : 0 ≤ x^(-β) ∧ x^(-β) ≤ 1 :=
    ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hβ)⟩
  have h : |(a+(1+s))^(-β)+(a+|1 - s|)^(-β)-2*(a+1)^(-β)| ≤ 2 := by
    apply abs_le.mpr
    obtain ⟨h₁₀, h₁₁⟩ := hc _ h₁
    obtain ⟨h₂₀, h₂₁⟩ := hc _ h₂
    obtain ⟨h₃₀, h₃₁⟩ := hc _ h₃
    constructor <;> linarith
  have hs₀ : 0 ≤ s ^ (-(3 / 2:ℝ)) := Real.rpow_nonneg (by linarith) _
  unfold sample
  rw [abs_mul, abs_of_nonneg hs₀, mul_comm 2 (s ^ (-(3 / 2:ℝ)))]
  exact mul_le_mul_of_nonneg_left h hs₀

private theorem sample_measurable (β a : ℝ) : Measurable (sample β a) := by
  unfold sample
  fun_prop

private theorem unshifted_center_majorant {β s : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (hs : 1 / 2 ≤ s) (hds : |1 - s| ≤ 1 / 2) (hne : s ≠ 1) :
    |sample β 0 s| ≤ 4 * |1 - s| ^(-(3 / 4:ℝ)) := by
  have hsp : 0 < s := by linarith
  have hweight : s^(-(3 / 2:ℝ)) ≤ 4 := by
    calc
      _ ≤ (1 / 2 : ℝ)^(-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hs (by norm_num)
      _ ≤ (1 / 2 : ℝ)^(-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = _ := by norm_num [Real.rpow_neg]
  have hp : (1+s)^(-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hβ)
  have hp0 : 0 ≤ (1+s)^(-β) := Real.rpow_nonneg (by linarith) _
  have hdist : 0 < |1 - s| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
  have hdist1 : |1 - s| ≤ 1 := hds.trans (by norm_num)
  have hq1 : 1 ≤ |1 - s| ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdist hdist1 (neg_nonpos.mpr hβ)
  have hq : |1 - s|^(-β) ≤ |1 - s|^(-(3 / 4:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge (abs_pos.mpr (sub_ne_zero.mpr hne.symm))
      hdist1 (by linarith)
  have hab : |(1+s)^(-β)+|1 - s|^(-β)-2| ≤ |1 - s|^(-(3 / 4:ℝ)) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold sample
  simp only [zero_add, Real.one_rpow, mul_one, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hsp.le (-(3 / 2:ℝ)))]
  exact mul_le_mul hweight hab (abs_nonneg _) (by norm_num)

private theorem continuous_center_one_side (δ : ℝ) (hδ : 0 ≤ δ) (r : ℝ) (hr : -1 < r) :
    IntervalIntegrable (fun s : ℝ => |1 - s|^r) volume (1-δ) 1 ∧
    IntervalIntegrable (fun s : ℝ => |1 - s|^r) volume 1 (1+δ) ∧
    (∫ s in (1-δ)..1, |1 - s|^r) = (∫ s in (0:ℝ)..δ, s^r) ∧
    (∫ s in 1..(1+δ), |1 - s|^r) = (∫ s in (0:ℝ)..δ, s^r) := by
  have hh : IntervalIntegrable (fun s : ℝ => s^r) volume 0 δ :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hA : IntervalIntegrable (fun s : ℝ => (1-s)^r) volume (1-δ) 1 := by
    simpa only [sub_zero] using (hh.comp_sub_left 1).symm
  have hB : IntervalIntegrable (fun s : ℝ => (s-1)^r) volume 1 (1+δ) := by
    simpa only [zero_add, add_comm δ 1] using hh.comp_sub_right 1
  have hAL : Set.EqOn (fun s : ℝ => (1-s)^r) (fun s : ℝ => |1 - s|^r)
      (Set.uIcc (1-δ) 1) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (1-s)^r = |1 - s|^r
    rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hBR : Set.EqOn (fun s : ℝ => (s-1)^r) (fun s : ℝ => |1 - s|^r)
      (Set.uIcc 1 (1+δ)) := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    change (s-1)^r = |1 - s|^r
    rw [abs_sub_comm 1 s, abs_of_nonneg (sub_nonneg.mpr hs.1)]
  refine ⟨hA.congr (hAL.mono Set.uIoc_subset_uIcc),
    hB.congr (hBR.mono Set.uIoc_subset_uIcc), ?_, ?_⟩
  · rw [← intervalIntegral.integral_congr hAL]
    simpa using (intervalIntegral.integral_comp_sub_left (a := 1-δ) (b := 1) (fun s : ℝ => s^r) 1)
  · rw [← intervalIntegral.integral_congr hBR]
    simpa using (intervalIntegral.integral_comp_sub_right (a := 1) (b := 1+δ) (fun s : ℝ => s^r) 1)

/-- Exact unshifted Mellin mesh integrand: integrable on the complete center
window, with uniform quarter-power loss. The point s=1 is volume-null. -/
private theorem continuous_center_cutoff {β δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    IntervalIntegrable (fun s : ℝ => |sample β 0 s|) volume (1-δ) (1+δ) ∧
    (∫ s in (1-δ)..(1+δ), |sample β 0 s|) ≤ 32 * δ^(1 / 4:ℝ) := by
  let g (s : ℝ) := |1 - s|^(-(3 / 4:ℝ))
  let G (s : ℝ) := 4 * g s
  obtain ⟨hA, hB, hIA, hIB⟩ := continuous_center_one_side δ hδ (-(3 / 4:ℝ)) (by norm_num)
  have hg : IntervalIntegrable g volume (1-δ) (1+δ) := hA.trans hB
  have hG : IntervalIntegrable G volume (1-δ) (1+δ) :=
    hg.const_mul 4
  have hle : 1-δ ≤ 1+δ := by linarith
  have hF : IntervalIntegrable (fun s : ℝ => |sample β 0 s|) volume (1-δ) (1+δ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle] at hG ⊢
    apply hG.mono' (continuous_abs.measurable.comp (sample_measurable β 0)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
      with s hs hne
    rw [Real.norm_eq_abs, Function.comp_apply, abs_abs]
    exact unshifted_center_majorant hβ hβ' (by linarith [hs.1])
      (abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩) hne
  refine ⟨hF, ?_⟩
  have hmono := intervalIntegral.integral_mono_ae_restrict hle hF hG (by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (1:ℝ)), ae_restrict_mem measurableSet_Icc]
      with s hne hs
    exact unshifted_center_majorant hβ hβ' (by linarith [hs.1])
      (abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩) hne)
  apply hmono.trans
  have hp : (∫ s in (0:ℝ)..δ, s^(-(3 / 4:ℝ))) = 4*δ^(1 / 4:ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(3 / 4:ℝ))),
      show -(3 / 4:ℝ)+1 = 1 / 4 by norm_num, Real.zero_rpow (by norm_num), sub_zero]
    ring
  have hIg : (∫ s in (1-δ)..(1+δ), g s) = 8*δ^(1 / 4:ℝ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hA hB]
    change (∫ s in (1-δ)..1, |1 - s|^(-(3 / 4:ℝ))) +
      (∫ s in 1..(1+δ), |1 - s|^(-(3 / 4:ℝ))) = _
    rw [hIA, hIB, hp]
    ring
  unfold G
  rw [intervalIntegral.integral_const_mul, hIg]
  ring_nf
  exact le_rfl

private theorem continuous_small_cutoff {β a δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    IntervalIntegrable (fun s : ℝ => |sample β a s|) volume 0 δ ∧
    (∫ s in (0:ℝ)..δ, |sample β a s|) ≤ (64 / 3 : ℝ) * δ^(3 / 2:ℝ) := by
  have hg : IntervalIntegrable (fun s : ℝ => 32*s^(1 / 2:ℝ)) volume 0 δ :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 32
  have hpoint : (fun s : ℝ => |sample β a s|) ≤ᵐ[volume.restrict (Set.Icc 0 δ)]
      (fun s : ℝ => 32*s^(1 / 2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
      with s hs hn
    exact small_sample_bound hβ hβ' ha
      (lt_of_le_of_ne hs.1 (Ne.symm hn)) (hs.2.trans hδ')
  have hF : IntervalIntegrable (fun s : ℝ => |sample β a s|) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hδ] at hg ⊢
    apply hg.mono' (continuous_abs.measurable.comp (sample_measurable β a)).aestronglyMeasurable
    exact hpoint.mono fun s hs => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, abs_abs] using hs
  refine ⟨hF, (intervalIntegral.integral_mono_ae_restrict hδ hF hg hpoint).trans ?_⟩
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ) < 1 / 2)),
    show (1 / 2:ℝ)+1 = 3 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero]
  ring_nf
  exact le_rfl

private theorem continuous_far_cutoff {β a R : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) (hR : 2 ≤ R) :
    IntegrableOn (fun s : ℝ => |sample β a s|) (Set.Ioi R) ∧
    (∫ s in Set.Ioi R, |sample β a s|) ≤ 4 * R^(-(1 / 2:ℝ)) := by
  have hR0 : 0 < R := by linarith
  have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2:ℝ)) < -1) hR0).const_mul 2
  have hbound : ∀ s ∈ Set.Ioi R, |sample β a s| ≤ 2*s^(-(3 / 2:ℝ)) :=
    fun _ hs => far_sample_bound hβ ha (hR.trans (Set.mem_Ioi.mp hs).le)
  have hf : IntegrableOn (fun s : ℝ => |sample β a s|) (Set.Ioi R) := by
    apply hg.mono' (continuous_abs.measurable.comp (sample_measurable β a)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with s hs
    simpa only [Real.norm_eq_abs, Function.comp_apply, abs_abs] using hbound s hs
  refine ⟨hf, (setIntegral_mono_on hf hg measurableSet_Ioi hbound).trans ?_⟩
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2:ℝ)) < -1) hR0,
    show -(3 / 2:ℝ)+1 = -(1 / 2:ℝ) by norm_num]
  linarith only

/-- Absolute integral bounds on the three excluded regions, with their
shift-uniform pointwise suppliers at the origin and in the far tail. -/
theorem mellin_cutoff_bounds :
    (∀ β a δ : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 ≤ δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun s => |sample β a s|) volume 0 δ ∧
        (∫ s in (0 : ℝ)..δ, |sample β a s|) ≤ (64 / 3 : ℝ) * δ ^ (3 / 2 : ℝ)) ∧
    (∀ β δ : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun s => |sample β 0 s|) volume (1 - δ) (1 + δ) ∧
        (∫ s in (1 - δ)..(1 + δ), |sample β 0 s|) ≤ 32 * δ ^ (1 / 4 : ℝ)) ∧
    (∀ β a R : ℝ, 0 ≤ β → 0 ≤ a → 2 ≤ R →
      IntegrableOn (fun s => |sample β a s|) (Set.Ioi R) ∧
        (∫ s in Set.Ioi R, |sample β a s|) ≤ 4 * R ^ (-(1 / 2 : ℝ))) ∧
    (∀ β a s : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 < s → s ≤ 1 / 2 →
      |sample β a s| ≤ 32 * s ^ (1 / 2 : ℝ)) ∧
    (∀ β a s : ℝ, 0 ≤ β → 0 ≤ a → 2 ≤ s →
      |sample β a s| ≤ 2 * s ^ (-(3 / 2 : ℝ))) :=
  ⟨fun _ _ _ => continuous_small_cutoff, fun _ _ => continuous_center_cutoff,
    fun _ _ _ => continuous_far_cutoff, fun _ _ _ => small_sample_bound,
    fun _ _ _ => far_sample_bound⟩

end D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
