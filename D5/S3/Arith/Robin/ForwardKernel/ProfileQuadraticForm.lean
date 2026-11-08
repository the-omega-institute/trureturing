/- GID: D5/S3/Arith/Robin/ForwardKernel/ProfileQuadraticForm
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ProfileQuadraticForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The min-kernel energy is the squared L² norm of the tail integral of an L¹ profile. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The min-kernel energy, its L¹ continuity, and its strict positivity. -/

namespace D5.S3.Arith.Robin.ForwardKernel.ProfileQuadraticForm

open Set MeasureTheory Filter
open scoped NNReal Topology
open D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

noncomputable section

private lemma tail_eq_indicator {g : ℝ → ℝ} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    tailProfile g r = ∫ s, (Ioi r).indicator g s ∂unitMeasure := by
  rw [tailProfile, intervalIntegral.integral_of_le hr.2, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi r ∩ Ioc (0 : ℝ) 1 = Ioc r 1 := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_of_le_of_lt hr.1 h.1, h.2⟩
  rw [he]

private lemma integral_cutoff {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (c : ℝ) :
    (∫ r, if r < min s t then c else 0 ∂unitMeasure) = c * min s t := by
  change (∫ r, (Iio (min s t)).indicator (fun _ => c) r ∂unitMeasure) = _
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have he : Iio (min s t) ∩ Ioc (0 : ℝ) 1 = Ioo 0 (min s t) := by
    ext r
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.le.trans ((min_le_left _ _).trans hs.2)⟩
  rw [he, setIntegral_const]
  rw [Measure.real, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal (le_min hs.1 ht.1), smul_eq_mul, mul_comm]

/-- The min-kernel quadratic form is the squared L² energy of the profile's tail integral. -/
theorem Q_eq_tail_energy {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Q g = ∫ r in (0 : ℝ)..1, tailProfile g r ^ 2 := by
  classical
  let k : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    if p.2 < min p.1.1 p.1.2 then g p.1.1 * g p.1.2 else 0
  have hk : Integrable k ((unitMeasure.prod unitMeasure).prod unitMeasure) := by
    apply (((hg.2.norm.mul_prod hg.2.norm).mul_prod
      (integrable_const (1 : ℝ)))).mono'
    · exact ((hg.1.comp measurable_fst.fst).mul (hg.1.comp measurable_fst.snd)).ite
        (measurableSet_lt measurable_snd (measurable_fst.fst.min measurable_fst.snd))
        measurable_const |>.aestronglyMeasurable
    · filter_upwards [] with p
      dsimp [k]
      split_ifs
      · simp
      · simp only [abs_zero, mul_one]
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hkernel : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2 * min p.1 p.2)
      (unitMeasure.prod unitMeasure) := by
    apply hk.integral_prod_left.congr
    have hmem : ∀ᵐ p ∂unitMeasure.prod unitMeasure,
        p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    exact integral_cutoff ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩ (g p.1 * g p.2)
  rw [Q, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_prod _ hkernel]
  calc
    _ = ∫ p : ℝ × ℝ, ∫ r, k (p, r) ∂unitMeasure ∂unitMeasure.prod unitMeasure := by
      apply integral_congr_ae
      have hmem : ∀ᵐ p ∂unitMeasure.prod unitMeasure,
          p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      exact (integral_cutoff ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩ (g p.1 * g p.2)).symm
    _ = ∫ r, ∫ p : ℝ × ℝ, k (p, r) ∂unitMeasure.prod unitMeasure ∂unitMeasure :=
      integral_integral_swap hk
    _ = ∫ r, tailProfile g r ^ 2 ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [tail_eq_indicator ⟨hr.1.le, hr.2⟩, pow_two, ← integral_prod_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [k]
      simp only [lt_min_iff, indicator_apply, mem_Ioi]
      split_ifs <;> simp_all
    _ = _ := rfl

private lemma tail_continuousOn {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    ContinuousOn (tailProfile g) (Icc (0 : ℝ) 1) := by
  have hi : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hg.2
  have he : tailProfile g = -(fun r : ℝ => ∫ s in (1 : ℝ)..r, g s) := by
    funext r
    change (∫ s in r..(1 : ℝ), g s) = -(∫ s in (1 : ℝ)..r, g s)
    exact intervalIntegral.integral_symm 1 r
  rw [he]
  simpa only [uIcc_of_le zero_le_one] using
    (intervalIntegral.continuousOn_primitive_interval' hi
      (right_mem_uIcc : (1 : ℝ) ∈ uIcc 0 1)).neg

private lemma tail_bound {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : |tailProfile g r| ≤ profileL1 g := by
  rw [tail_eq_indicator hr, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ s, ‖(Ioi r).indicator g s‖ ∂unitMeasure) ≤ ∫ s, |g s| ∂unitMeasure
  apply integral_mono (hg.2.indicator measurableSet_Ioi).norm hg.2.norm
  intro s
  by_cases hs : s ∈ Ioi r <;> simp [hs]

private lemma tail_memLp {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    MemLp (tailProfile g) 2 unitMeasure := by
  apply MemLp.of_bound
    ((tail_continuousOn hg).mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)
    (profileL1 g)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact tail_bound hg ⟨hr.1.le, hr.2⟩

private lemma tail_sub {f g : ℝ → ℝ} (hf : ProfileIntegrable f) (hg : ProfileIntegrable g)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    tailProfile (fun s => g s - f s) r = tailProfile g r - tailProfile f r := by
  rw [tail_eq_indicator hr, tail_eq_indicator hr, tail_eq_indicator hr,
    ← integral_sub (hg.2.indicator measurableSet_Ioi) (hf.2.indicator measurableSet_Ioi)]
  congr 1
  ext s
  by_cases hs : s ∈ Ioi r <;> simp [hs]

/-- The square root of the min-kernel energy is 1-Lipschitz for the L¹ distance. -/
theorem sqrt_Q_sub_le {f g : ℝ → ℝ}
    (hf : ProfileIntegrable f) (hg : ProfileIntegrable g) :
    |Real.sqrt (Q g) - Real.sqrt (Q f)| ≤ profileL1 (fun s => g s - f s) := by
  have hfg : ProfileIntegrable (fun s => g s - f s) := ⟨hg.1.sub hf.1, hg.2.sub hf.2⟩
  have hfm := tail_memLp hf
  have hgm := tail_memLp hg
  have hrev : |Real.sqrt (Q g) - Real.sqrt (Q f)| ≤
      Real.sqrt (∫ r, (tailProfile g r - tailProfile f r) ^ 2 ∂unitMeasure) := by
    rw [Q_eq_tail_energy hg, Q_eq_tail_energy hf]
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      VarianceTransfer.interval_l2_reverse_triangle zero_le_one hgm hfm
  apply hrev.trans
  have hsq : (∫ r, (tailProfile g r - tailProfile f r) ^ 2 ∂unitMeasure) ≤
      profileL1 (fun s => g s - f s) ^ 2 := by
    calc
      _ ≤ ∫ _r, profileL1 (fun s => g s - f s) ^ 2 ∂unitMeasure := by
        apply integral_mono_ae ((hgm.sub hfm).integrable_sq) (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hb := tail_bound hfg ⟨hr.1.le, hr.2⟩
        rw [tail_sub hf hg ⟨hr.1.le, hr.2⟩] at hb
        simpa only [sq_abs, Pi.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by simp [unitMeasure]
  exact (Real.sqrt_le_sqrt hsq).trans_eq
    (Real.sqrt_sq (integral_nonneg fun s => abs_nonneg (g s - f s)))

private lemma Q_eq_zero_iff {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Q g = 0 ↔ g =ᵐ[unitMeasure] 0 := by
  constructor
  · intro hQ
    have he : (∫ r, tailProfile g r ^ 2 ∂unitMeasure) = 0 := by
      simpa only [Q_eq_tail_energy hg, intervalIntegral.integral_of_le zero_le_one] using hQ
    have htail : tailProfile g =ᵐ[unitMeasure] 0 := by
      have hs := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun r => sq_nonneg (tailProfile g r))
        (tail_memLp hg).integrable_sq).mp he
      filter_upwards [hs] with r hr
      simpa only [Pi.zero_apply, sq_eq_zero_iff] using hr
    have htail' : EqOn (tailProfile g) (fun _ => 0) (Icc (0 : ℝ) 1) := by
      apply Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1)
        _ (tail_continuousOn hg) continuousOn_const
      change ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) 1), tailProfile g r = 0
      change ∀ᵐ r ∂unitMeasure, tailProfile g r = 0 at htail
      rwa [unitMeasure, restrict_Ioc_eq_restrict_Icc] at htail
    have hi : IntervalIntegrable g volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hg.2
    have hd := hi.ae_hasDerivAt_integral
    change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), g x = 0
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hd, (show ∀ᵐ x : ℝ, x ≠ 1 by rw [ae_iff]; simp)] with x hx hx1 hmem
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1, lt_of_le_of_ne hmem.2 hx1⟩
    have hx' : x ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]
      exact ⟨hmem.1.le, hmem.2⟩
    have hdx := hx hx' 1 right_mem_uIcc
    have hlocal : (fun r => ∫ s in (1 : ℝ)..r, g s) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hx01.1 hx01.2] with r hr
      rw [intervalIntegral.integral_symm]
      change -tailProfile g r = 0
      rw [htail' ⟨hr.1.le, hr.2.le⟩, neg_zero]
    have hd0 := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hlocal
    exact hdx.unique hd0
  · intro hg0
    rw [Q, intervalIntegral.integral_of_le zero_le_one]
    apply integral_eq_zero_of_ae
    filter_upwards [hg0] with s hs
    simp [hs]

/-- The min-kernel energy is strictly positive exactly when the profile is not a.e. zero. -/
theorem Q_pos_iff {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    0 < Q g ↔ ¬ (g =ᵐ[unitMeasure] 0) := by
  have hnonneg : 0 ≤ Q g := by
    rw [Q_eq_tail_energy hg]
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one fun r => sq_nonneg _
  constructor
  · intro hQ hg0
    have := (Q_eq_zero_iff hg).mpr hg0
    linarith
  · intro hg0
    exact lt_of_le_of_ne hnonneg (Ne.symm fun hQ => hg0 ((Q_eq_zero_iff hg).mp hQ))

end
end D5.S3.Arith.Robin.ForwardKernel.ProfileQuadraticForm
