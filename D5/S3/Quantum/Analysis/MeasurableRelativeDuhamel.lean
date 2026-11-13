/- GID: D5/S3/Quantum/Analysis/MeasurableRelativeDuhamel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/MeasurableRelativeDuhamel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative Bochner integrals for the original measurable evolution. -/

import D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
import Mathlib.MeasureTheory.Integral.Prod

/-! # Relative integrals of the original measurable evolution -/

open scoped Topology
open MeasureTheory Filter intervalIntegral
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem native_data (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) :
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => measurableEvolution S B p.1 p.2 x)
      (triangle T)) ∧
    (∀ t r, (t,r) ∈ triangle T →
      ‖measurableEvolution S B t r‖ ≤ Real.exp (∫ s in 0..T, g s)) ∧
    (∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      measurableEvolution S B t r x = S.action (t-r) x +
        ∫ s in r..t, S.action (t-s) (B s (measurableEvolution S B s r x))) := by
  obtain ⟨Phi, hPhi⟩ := measurable_evolution S
  rcases hPhi B T hT hB g hg hgn hBg with
    ⟨_, _, _, hseries, hc, hm, _, _, _, hb, _⟩
  have heq : ∀ t r, (t,r) ∈ triangle T → Phi B t r = measurableEvolution S B t r := by
    intro t r hp
    ext x
    have hBr := fun z => (hB z).mono_set (Set.Icc_subset_Icc hp.1 le_rfl)
    have hgr := hg.mono_set (Set.Icc_subset_Icc hp.1 le_rfl)
    have hnr := fun s (hs : s ∈ Set.Icc r T) => hgn s ⟨hp.1.trans hs.1, hs.2⟩
    have hBgr := fun s (hs : s ∈ Set.Icc r T) => hBg s ⟨hp.1.trans hs.1, hs.2⟩
    rw [measurableEvolution_apply S B (hp.2.1.trans hp.2.2) hBr g hgr hnr hBgr
      ⟨hp.2.1, hp.2.2⟩ x]
    exact (hseries t r hp x).2.tsum_eq.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (hc x).congr (fun p hp => congrArg (fun A : E →L[ℂ] E => A x) (heq p.1 p.2 hp).symm)
  · intro t r hp
    rw [← heq t r hp]
    apply (hb t r hp).trans
    apply Real.exp_le_exp.mpr
    apply intervalIntegral.integral_mono_interval hp.1 hp.2.1 hp.2.2
      _ ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hg)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hgn s ⟨hs.1.le, hs.2⟩
  · intro t r hp x
    rw [← heq t r hp, hm t r hp x]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hp.2.1] at hs
    dsimp only
    rw [heq s r ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩]

private noncomputable def clippedKernel (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    (T t s : ℝ) : E →L[ℂ] E :=
  measurableEvolution S B (max (max 0 (min T t)) (max 0 (min T s))) (max 0 (min T s))

private theorem clippedKernel_eq (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T t s : ℝ} (hp : (t,s) ∈ triangle T) :
    clippedKernel S B T t s = measurableEvolution S B t s := by
  simp only [clippedKernel, min_eq_right hp.2.2,
    min_eq_right (hp.2.1.trans hp.2.2), max_eq_right hp.1,
    max_eq_right (hp.1.trans hp.2.1), max_eq_left hp.2.1]

private theorem kernel_regular (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) :
    (∀ x : E, Continuous (fun p : ℝ × ℝ => clippedKernel S B T p.1 p.2 x)) ∧
    (∀ t s, ‖clippedKernel S B T t s‖ ≤ Real.exp (∫ s in 0..T, g s)) := by
  have hd := native_data S B hT hB g hg hgn hBg
  let c : ℝ → ℝ := fun s => max 0 (min T s)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hc0 : ∀ s, 0 ≤ c s := fun s => le_max_left _ _
  have hcT : ∀ s, c s ≤ T := fun s => max_le hT (min_le_left _ _)
  have hp : ∀ t s, (max (c t) (c s), c s) ∈ triangle T := fun t s =>
    ⟨hc0 s, le_max_right _ _, max_le (hcT t) (hcT s)⟩
  constructor
  · intro x
    exact (hd.1 x).comp_continuous
      (((hc.comp continuous_fst).max (hc.comp continuous_snd)).prodMk
        (hc.comp continuous_snd)) (fun p => hp p.1 p.2)
  · intro t s
    exact hd.2.1 _ _ (hp t s)

theorem forced_regular (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T r : ℝ} (hT : 0 ≤ T) (hr : r ∈ Set.Icc 0 T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    {f : ℝ → E} (hf : IntegrableOn f (Set.Icc r T)) :
    ContinuousOn (fun t => ∫ s in r..t, measurableEvolution S B t s (f s)) (Set.Icc r T) ∧
    ∀ t ∈ Set.Icc r T, IntervalIntegrable
      (fun s => measurableEvolution S B t s (f s)) volume r t := by
  classical
  let w := (Set.Icc r T).indicator f
  have hw : Integrable w := hf.integrable_indicator measurableSet_Icc
  have hk := kernel_regular S B hT hB g hg hgn hBg
  let C := Real.exp (∫ s in 0..T, g s)
  have hm : ∀ t, AEStronglyMeasurable (fun s => clippedKernel S B T t s (w s)) := by
    intro t
    exact aestronglyMeasurable_evaluation _
      (fun x => ((hk.1 x).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      hw.aestronglyMeasurable
  have hb : ∀ t s, ‖clippedKernel S B T t s (w s)‖ ≤ C * ‖w s‖ := fun t s =>
    ((clippedKernel S B T t s).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hk.2 t s) (norm_nonneg _))
  have hc : Continuous (fun p : ℝ × ℝ =>
      ∫ s in r..p.2, clippedKernel S B T p.1 s (w s)) :=
    parametric_primitive_continuous _ (hw.norm.const_mul C) hm hb
      (fun s => (hk.1 (w s)).comp (continuous_id.prodMk continuous_const)) r
  have heq : ∀ t ∈ Set.Icc r T,
      (∫ s in r..t, clippedKernel S B T t s (w s)) =
        ∫ s in r..t, measurableEvolution S B t s (f s) := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    dsimp only
    rw [clippedKernel_eq S B ⟨hr.1.trans hs.1, hs.2, ht.2⟩]
    change measurableEvolution S B t s ((Set.Icc r T).indicator f s) = _
    rw [Set.indicator_of_mem (show s ∈ Set.Icc r T from ⟨hs.1, hs.2.trans ht.2⟩)]
  constructor
  · exact (hc.comp (continuous_id.prodMk continuous_id)).continuousOn.congr
      (fun t ht => (heq t ht).symm)
  · intro t ht
    have hi : Integrable (fun s => clippedKernel S B T t s (w s)) :=
      (hw.norm.const_mul C).mono' (hm t) (Eventually.of_forall (hb t))
    apply hi.intervalIntegrable.congr
    intro s hs
    rw [Set.uIoc_of_le ht.1] at hs
    dsimp only
    rw [clippedKernel_eq S B ⟨hr.1.trans hs.1.le, hs.2, ht.2⟩]
    exact congrArg (measurableEvolution S B t s)
      (Set.indicator_of_mem (show s ∈ Set.Icc r T from ⟨hs.1.le, hs.2.trans ht.2⟩) f)

private theorem triangle_swap {r t : ℝ} (hrt : r ≤ t) (F : ℝ → ℝ → E)
    (hF : Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then F p.1 p.2 else 0)
      ((volume.restrict (Set.Icc r t)).prod (volume.restrict (Set.Icc r t)))) :
    (∫ q in r..t, ∫ s in r..q, F q s) = ∫ s in r..t, ∫ q in s..t, F q s := by
  classical
  have hl : ∀ q ∈ Set.Icc r t,
      (∫ s in Set.Icc r t, if s ≤ q then F q s else 0) = ∫ s in r..q, F q s := by
    intro q hq
    change (∫ s in Set.Icc r t, (Set.Iic q).indicator (F q) s) = _
    rw [setIntegral_indicator measurableSet_Iic]
    have he : Set.Icc r t ∩ Set.Iic q = Set.Icc r q := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, h.2.trans hq.2⟩, h.2⟩
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.1]
  have hr : ∀ s ∈ Set.Icc r t,
      (∫ q in Set.Icc r t, if s ≤ q then F q s else 0) = ∫ q in s..t, F q s := by
    intro s hs
    change (∫ q in Set.Icc r t, (Set.Ici s).indicator (fun q => F q s) q) = _
    rw [setIntegral_indicator measurableSet_Ici]
    have he : Set.Icc r t ∩ Set.Ici s = Set.Icc s t := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      constructor
      · exact fun h => ⟨h.2, h.1.2⟩
      · exact fun h => ⟨⟨hs.1.trans h.1, h.2⟩, h.1⟩
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2]
  calc
    _ = ∫ q in Set.Icc r t, ∫ s in Set.Icc r t,
        if s ≤ q then F q s else 0 := by
      rw [intervalIntegral.integral_of_le hrt, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (fun q hq => (hl q hq).symm)
    _ = ∫ s in Set.Icc r t, ∫ q in Set.Icc r t,
        if s ≤ q then F q s else 0 := integral_integral_swap hF
    _ = _ := by
      rw [intervalIntegral.integral_of_le hrt, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc hr

private theorem forced_mild (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T r : ℝ} (hT : 0 ≤ T) (hr : r ∈ Set.Icc 0 T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    {f : ℝ → E} (hf : IntegrableOn f (Set.Icc r T)) :
    ∀ t ∈ Set.Icc r T,
      (∫ s in r..t, measurableEvolution S B t s (f s)) =
        (∫ s in r..t, S.action (t-s) (f s)) +
        ∫ q in r..t, S.action (t-q)
          (B q (∫ s in r..q, measurableEvolution S B q s (f s))) := by
  classical
  have hk := kernel_regular S B hT hB g hg hgn hBg
  have hd := native_data S B hT hB g hg hgn hBg
  have hJ := forced_regular S B hT hr hB g hg hgn hBg hf
  let C := Real.exp (∫ s in 0..T, g s)
  intro t ht
  let μ := volume.restrict (Set.Icc r t)
  have hft : Integrable f μ := hf.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hgt : Integrable g μ := hg.mono_set (Set.Icc_subset_Icc hr.1 ht.2)
  let F : ℝ → ℝ → E := fun q s =>
    S.action (t-q) (B q (clippedKernel S B T q s (f s)))
  have hkm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => clippedKernel S B T p.1 p.2 (f p.2)) (μ.prod μ) :=
    aestronglyMeasurable_evaluation _ (fun x => (hk.1 x).aestronglyMeasurable)
      hft.aestronglyMeasurable.comp_snd
  have hBm : ∀ x : E, AEStronglyMeasurable (fun p : ℝ × ℝ => B p.1 x) (μ.prod μ) :=
    fun x => ((hB x).mono_set (Set.Icc_subset_Icc hr.1 ht.2)).comp_fst
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) :=
    S.action_continuous.comp_aestronglyMeasurable
      ((continuous_const.sub continuous_fst).aestronglyMeasurable.prodMk
        (aestronglyMeasurable_evaluation _ hBm hkm))
  have hmem : ∀ᵐ p ∂μ.prod μ, p ∈ (Set.Icc r t) ×ˢ (Set.Icc r t) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hFi : Integrable (Function.uncurry F) (μ.prod μ) := by
    apply ((hgt.mul_const C).mul_prod hft.norm).mono' hFm
    filter_upwards [hmem] with p hp
    have hq : p.1 ∈ Set.Icc 0 T := ⟨hr.1.trans hp.1.1, hp.1.2.trans ht.2⟩
    calc
      ‖F p.1 p.2‖ ≤ ‖B p.1 (clippedKernel S B T p.1 p.2 (f p.2))‖ := S.action_bound _ _
      _ ≤ ‖B p.1‖ * ‖clippedKernel S B T p.1 p.2 (f p.2)‖ := (B p.1).le_opNorm _
      _ ≤ g p.1 * (C * ‖f p.2‖) := mul_le_mul (hBg p.1 hq)
        (((clippedKernel S B T p.1 p.2).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hk.2 _ _) (norm_nonneg _)))
        (norm_nonneg _) (hgn p.1 hq)
      _ = (g p.1 * C) * ‖f p.2‖ := by ring
  have htri : Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then F p.1 p.2 else 0)
      (μ.prod μ) := by
    exact hFi.indicator (measurableSet_le measurable_snd measurable_fst)
  have hfree : IntervalIntegrable (fun s => S.action (t-s) (f s)) volume r t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
    exact hft.norm.mono'
      (S.action_continuous.comp_aestronglyMeasurable
        ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hft.aestronglyMeasurable))
      (Eventually.of_forall fun s => S.action_bound _ _)
  have hm : ∀ s ∈ Set.Icc r t,
      measurableEvolution S B t s (f s) = S.action (t-s) (f s) + ∫ q in s..t, F q s := by
    intro s hs
    rw [hd.2.2 t s ⟨hr.1.trans hs.1, hs.2, ht.2⟩ (f s)]
    congr 1
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hs.2] at hq
    dsimp only [F]
    rw [clippedKernel_eq S B ⟨hr.1.trans hs.1, hq.1, hq.2.trans ht.2⟩]
  have hinner : IntervalIntegrable (fun s => ∫ q in s..t, F q s) volume r t := by
    apply ((hJ.2 t ht).sub hfree).congr
    intro s hs
    rw [Set.uIoc_of_le ht.1] at hs
    dsimp only
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hm s ⟨hs.1.le, hs.2⟩)
  have hpush : ∀ q ∈ Set.Icc r t, (∫ s in r..q, F q s) =
      S.action (t-q) (B q (∫ s in r..q, measurableEvolution S B q s (f s))) := by
    intro q hq
    have hi := hJ.2 q ⟨hq.1, hq.2.trans ht.2⟩
    change (∫ s in r..q, F q s) =
      ((S.action (t-q)).comp (B q)) (∫ s in r..q, measurableEvolution S B q s (f s))
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      ((S.action (t-q)).comp (B q)) hi]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hq.1] at hs
    dsimp only [F, ContinuousLinearMap.comp_apply]
    rw [clippedKernel_eq S B ⟨hr.1.trans hs.1, hs.2, hq.2.trans ht.2⟩]
  calc
    _ = ∫ s in r..t, (S.action (t-s) (f s) + ∫ q in s..t, F q s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      exact hm s hs
    _ = (∫ s in r..t, S.action (t-s) (f s)) + ∫ s in r..t, ∫ q in s..t, F q s :=
      intervalIntegral.integral_add hfree hinner
    _ = (∫ s in r..t, S.action (t-s) (f s)) + ∫ q in r..t, ∫ s in r..q, F q s := by
      rw [triangle_swap ht.1 F htri]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro q hq
      rw [Set.uIcc_of_le ht.1] at hq
      exact hpush q hq

private theorem relative_left (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    {T r : ℝ} (hT : 0 ≤ T) (hr : r ∈ Set.Icc 0 T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (hH : ∀ x : E, AEStronglyMeasurable (fun s => H s x) (volume.restrict (Set.Icc 0 T)))
    (g h : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (hh : IntegrableOn h (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hhn : ∀ s ∈ Set.Icc 0 T, 0 ≤ h s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (hHh : ∀ s ∈ Set.Icc 0 T, ‖H s‖ ≤ h s)
    (x : E) : ∀ t ∈ Set.Icc r T,
    IntervalIntegrable
      (fun s => measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x))) volume r t ∧
    measurableEvolution S (B+H) t r x - measurableEvolution S B t r x =
      ∫ s in r..t, measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x)) := by
  have hQ : ∀ z : E, AEStronglyMeasurable (fun s => (B+H) s z)
      (volume.restrict (Set.Icc 0 T)) := fun z => (hB z).add (hH z)
  have hQgh : ∀ s ∈ Set.Icc 0 T, ‖(B+H) s‖ ≤ (g+h) s := by
    intro s hs
    exact (norm_add_le _ _).trans (add_le_add (hBg s hs) (hHh s hs))
  have hngh : ∀ s ∈ Set.Icc 0 T, 0 ≤ (g+h) s := fun s hs => add_nonneg (hgn s hs) (hhn s hs)
  have hdQ := native_data S (B+H) hT hQ (g+h) (hg.add hh) hngh hQgh
  have hdB := native_data S B hT hB g hg hgn hBg
  let X : ℝ → E := fun s => measurableEvolution S (B+H) s r x
  let V : ℝ → E := fun s => measurableEvolution S B s r x
  have hX : ContinuousOn X (Set.Icc r T) := (hdQ.1 x).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hr.1, ht.1, ht.2⟩)
  have hV : ContinuousOn V (Set.Icc r T) := (hdB.1 x).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hr.1, ht.1, ht.2⟩)
  let f : ℝ → E := fun s => H s (X s)
  have hf : IntegrableOn f (Set.Icc r T) := evaluation_integrable
    (fun z => (hH z).mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (hh.mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (fun s hs => hHh s ⟨hr.1.trans hs.1, hs.2⟩) hX
  let J : ℝ → E := fun t => ∫ s in r..t, measurableEvolution S B t s (f s)
  have hJ := forced_regular S B hT hr hB g hg hgn hBg hf
  have hJM := forced_mild S B hT hr hB g hg hgn hBg hf
  have hBr := fun z => (hB z).mono_set (Set.Icc_subset_Icc hr.1 le_rfl)
  have hgr := hg.mono_set (Set.Icc_subset_Icc hr.1 le_rfl)
  have hnr := fun s (hs : s ∈ Set.Icc r T) => hgn s ⟨hr.1.trans hs.1, hs.2⟩
  have hBgr := fun s (hs : s ∈ Set.Icc r T) => hBg s ⟨hr.1.trans hs.1, hs.2⟩
  have hiX := (causal_regular S hBr hgr hBgr hX).2
  have hiV := (causal_regular S hBr hgr hBgr hV).2
  have hiJ := (causal_regular S hBr hgr hBgr hJ.1).2
  have hiH := (causal_regular S
    (fun z => (hH z).mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (hh.mono_set (Set.Icc_subset_Icc hr.1 le_rfl))
    (fun s hs => hHh s ⟨hr.1.trans hs.1, hs.2⟩) hX).2
  let Y : ℝ → E := fun t => X t - V t - J t
  have hY : ContinuousOn Y (Set.Icc r T) := (hX.sub hV).sub hJ.1
  have hYM : ∀ t ∈ Set.Icc r T, Y t = causal S B r Y t := by
    intro t ht
    have hMX : X t = S.action (t-r) x + causal S (B+H) r X t :=
      hdQ.2.2 t r ⟨hr.1, ht.1, ht.2⟩ x
    have hMV : V t = S.action (t-r) x + causal S B r V t :=
      hdB.2.2 t r ⟨hr.1, ht.1, ht.2⟩ x
    have hMJ : J t = (∫ s in r..t, S.action (t-s) (f s)) + causal S B r J t := hJM t ht
    have hsplit : causal S (B+H) r X t = causal S B r X t +
        ∫ s in r..t, S.action (t-s) (f s) := by
      simp only [causal, Pi.add_apply, ContinuousLinearMap.add_apply, map_add, f]
      exact intervalIntegral.integral_add (hiX t ht) (hiH t ht)
    have hlin : causal S B r Y t = causal S B r X t - causal S B r V t - causal S B r J t := by
      simp only [causal, Y, map_sub]
      rw [intervalIntegral.integral_sub ((hiX t ht).sub (hiV t ht)) (hiJ t ht),
        intervalIntegral.integral_sub (hiX t ht) (hiV t ht)]
    change X t - V t - J t = _
    rw [hlin, hMX, hMV, hMJ, hsplit]
    abel
  have hzero := continuous_residual_eq_zero S B hr.2 hBr g hgr hnr hBgr hY hYM
  intro t ht
  refine ⟨hJ.2 t ht, ?_⟩
  exact sub_eq_zero.mp (hzero t ht)

/-- Both noncommuting relative identities have actual vector Bochner integrands. -/
theorem relative_duhamel (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (hH : ∀ x : E, AEStronglyMeasurable (fun s => H s x) (volume.restrict (Set.Icc 0 T)))
    (g h : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (hh : IntegrableOn h (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hhn : ∀ s ∈ Set.Icc 0 T, 0 ≤ h s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (hHh : ∀ s ∈ Set.Icc 0 T, ‖H s‖ ≤ h s)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (x : E) :
    IntervalIntegrable
      (fun s => measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x))) volume r t ∧
    IntervalIntegrable
      (fun s => measurableEvolution S (B+H) t s (H s (measurableEvolution S B s r x))) volume r t ∧
    (measurableEvolution S (B+H) t r x - measurableEvolution S B t r x =
      ∫ s in r..t, measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x))) ∧
    (measurableEvolution S (B+H) t r x - measurableEvolution S B t r x =
      ∫ s in r..t, measurableEvolution S (B+H) t s (H s (measurableEvolution S B s r x))) := by
  have hl := relative_left S B H hT ⟨hr, hrt.trans htT⟩ hB hH g h hg hh hgn hhn hBg hHh x t ⟨hrt, htT⟩
  have hQ : ∀ z : E, AEStronglyMeasurable (fun s => (B+H) s z)
      (volume.restrict (Set.Icc 0 T)) := fun z => (hB z).add (hH z)
  have hnH : ∀ z : E, AEStronglyMeasurable (fun s => (-H) s z)
      (volume.restrict (Set.Icc 0 T)) := fun z => (hH z).neg
  have hQgh : ∀ s ∈ Set.Icc 0 T, ‖(B+H) s‖ ≤ (g+h) s := fun s hs =>
    (norm_add_le _ _).trans (add_le_add (hBg s hs) (hHh s hs))
  have hngh : ∀ s ∈ Set.Icc 0 T, 0 ≤ (g+h) s := fun s hs => add_nonneg (hgn s hs) (hhn s hs)
  have hnHh : ∀ s ∈ Set.Icc 0 T, ‖(-H) s‖ ≤ h s := by
    intro s hs
    simpa only [Pi.neg_apply, norm_neg] using hHh s hs
  have hs := relative_left S (B+H) (-H) hT ⟨hr, hrt.trans htT⟩ hQ hnH
    (g+h) h (hg.add hh) hh hngh hhn hQgh hnHh x t ⟨hrt, htT⟩
  have hcancel : B + H + -H = B := add_neg_cancel_right B H
  rw [hcancel] at hs
  have hint : (fun s => measurableEvolution S (B+H) t s ((-H) s (measurableEvolution S B s r x))) =
      (fun s => -(measurableEvolution S (B+H) t s (H s (measurableEvolution S B s r x)))) := by
    funext s
    simp only [Pi.neg_apply, ContinuousLinearMap.neg_apply, map_neg]
  rw [hint] at hs
  refine ⟨hl.1, ?_, hl.2, ?_⟩
  · apply hs.1.neg.congr
    intro s _
    exact neg_neg _
  · have he := congrArg Neg.neg hs.2
    simpa only [neg_sub, intervalIntegral.integral_neg, neg_neg] using he

end D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
