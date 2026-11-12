/- GID: D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/ShiftOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Increasing hazard and real-shift order of the concrete delay kernel. -/

module

public import D5.S3.StatisticalMechanics.DelayedCooling.Kernel
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Real-shift comparison of the delayed cooling kernel

The hazard is smooth before and after one delay, with separate one-sided
rates there. Its strict monotonicity gives the weak order of shifted kernels.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder

open Set Filter
open scoped Topology
open Kernel

noncomputable section

/-- The logarithmic cooling rate, with the source equilibrium extension. -/
def hazard (τ t : ℝ) : ℝ := relaxation τ (t - τ) / relaxation τ t

private theorem continuous_hazard {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) : Continuous (hazard τ) := by
  exact ((continuous_relaxation hτ).comp (continuous_id.sub continuous_const)).div
    (continuous_relaxation hτ) (fun t => (relaxation_pos hτ hsmall t).ne')

private theorem hazard_pos {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) (t : ℝ) :
    0 < hazard τ t := div_pos (relaxation_pos hτ hsmall _) (relaxation_pos hτ hsmall _)

private theorem hazard_initial {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    hazard τ t = 1 / (1 - t) := by
  simp [hazard, relaxation_of_nonpos hτ (sub_nonpos.mpr htτ),
    relaxation_initial_segment hτ ht htτ]

private theorem hasDerivAt_hazard_early {τ t : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (ht : 0 < t) (htτ : t < τ) :
    HasDerivAt (hazard τ) ((hazard τ t) ^ 2) t := by
  have hden : 1 - t ≠ 0 := by
    rw [← relaxation_initial_segment hτ ht.le htτ.le]
    exact (relaxation_pos hτ hsmall t).ne'
  have hd := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv hden
  rw [hazard_initial hτ ht.le htτ.le]
  convert hd.congr_of_eventuallyEq ?_ using 1
  · simp
  · filter_upwards [Ioo_mem_nhds ht htτ] with s hs
    simpa using hazard_initial hτ (mem_Ioo.mp hs).1.le (mem_Ioo.mp hs).2.le

private theorem hasDerivAt_hazard_late {τ t : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (ht : τ < t) :
    HasDerivAt (hazard τ) (hazard τ t * (hazard τ t - hazard τ (t - τ))) t := by
  have hnum := (hasDerivAt_relaxation hτ (sub_pos.mpr ht)).comp t
    ((hasDerivAt_id t).sub_const τ)
  have hd := hnum.div (hasDerivAt_relaxation hτ (hτ.trans ht))
    (relaxation_pos hτ hsmall t).ne'
  convert hd using 1
  · rfl
  · dsimp [hazard]
    have h0 := (relaxation_pos hτ hsmall t).ne'
    have h1 := (relaxation_pos hτ hsmall (t - τ)).ne'
    field_simp
    ring_nf

private theorem strictMonoOn_hazard_initial {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) : StrictMonoOn (hazard τ) (Icc 0 τ) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_hazard hτ hsmall).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_hazard_early hτ hsmall ht.1 ht.2).deriv]
  exact sq_pos_of_pos (hazard_pos hτ hsmall t)

private def hazardRate (τ t : ℝ) : ℝ := hazard τ t * (hazard τ t - hazard τ (t - τ))

private theorem hazardRate_pos {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1))
    (t : ℝ) (ht : τ ≤ t) : 0 < hazardRate τ t := by
  have hi := strictMonoOn_hazard_initial hτ hsmall
  have hstart : 0 < hazardRate τ τ := by
    have hh := hi (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl, hτ.le⟩)
      (show τ ∈ Icc 0 τ from ⟨hτ.le, le_rfl⟩) hτ
    simpa [hazardRate] using mul_pos (hazard_pos hτ hsmall τ) (sub_pos.mpr hh)
  by_contra hbad
  let S : Set ℝ := Icc τ t ∩ {s | hazardRate τ s ≤ 0}
  have hcont : Continuous (hazardRate τ) :=
    (continuous_hazard hτ hsmall).mul ((continuous_hazard hτ hsmall).sub
      ((continuous_hazard hτ hsmall).comp (continuous_id.sub continuous_const)))
  obtain ⟨T, hT⟩ := (isCompact_Icc.inter_right (isClosed_le hcont continuous_const)).exists_isLeast
    (show S.Nonempty from ⟨t, ⟨⟨ht, le_rfl⟩, le_of_not_gt hbad⟩⟩)
  have hTτ : τ < T := by
    have hn : T ≠ τ := by intro he; subst T; exact (not_le_of_gt hstart) hT.1.2
    exact lt_of_le_of_ne hT.1.1.1 (Ne.symm hn)
  have hp : ∀ s ∈ Ioo τ T, 0 < hazardRate τ s := by
    intro s hs
    by_contra hh
    have hm : s ∈ S := ⟨⟨hs.1.le, hs.2.le.trans hT.1.1.2⟩, le_of_not_gt hh⟩
    exact (not_le_of_gt hs.2) (hT.2 hm)
  have hm : StrictMonoOn (hazard τ) (Icc τ T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_hazard hτ hsmall).continuousOn
    intro s hs
    rw [interior_Icc] at hs
    rw [(hasDerivAt_hazard_late hτ hsmall hs.1).deriv]
    exact hp s hs
  have hall : StrictMonoOn (hazard τ) (Icc 0 τ ∪ Icc τ T) :=
    hi.union hm (isGreatest_Icc hτ.le) (isLeast_Icc hTτ.le)
  have hleft : T - τ ∈ Icc 0 τ ∪ Icc τ T := by
    rw [Icc_union_Icc_eq_Icc hτ.le hTτ.le]
    exact ⟨by linarith, by linarith⟩
  have hright : T ∈ Icc 0 τ ∪ Icc τ T := Or.inr ⟨hTτ.le, le_rfl⟩
  have hh := hall hleft hright (by linarith : T - τ < T)
  exact (not_le_of_gt (mul_pos (hazard_pos hτ hsmall T) (sub_pos.mpr hh))) hT.1.2

/-- The actual hazard increases strictly, despite its derivative kink at one delay. -/
theorem strictMonoOn_hazard {τ : ℝ} (hτ : 0 < τ) (hsmall : τ ≤ Real.exp (-1)) :
    StrictMonoOn (hazard τ) (Ici 0) := by
  have hl := strictMonoOn_hazard_initial hτ hsmall
  have hr : StrictMonoOn (hazard τ) (Ici τ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_hazard hτ hsmall).continuousOn
    intro t ht
    simp only [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_hazard_late hτ hsmall ht).deriv]
    exact hazardRate_pos hτ hsmall t ht.le
  have hh := hl.union hr (isGreatest_Icc hτ.le) isLeast_Ici
  rwa [Icc_union_Ici_eq_Ici hτ.le] at hh

private theorem continuous_ratio {τ : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (w : ℝ) :
    Continuous (fun t => relaxation τ (t + w) / relaxation τ t) := by
  exact ((continuous_relaxation hτ).comp (continuous_id.add continuous_const)).div
    (continuous_relaxation hτ) (fun t => (relaxation_pos hτ hsmall t).ne')

private theorem hasDerivAt_ratio {τ t w : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (ht : 0 < t) (hw : 0 ≤ w) :
    HasDerivAt (fun t => relaxation τ (t + w) / relaxation τ t)
      ((relaxation τ (t + w) / relaxation τ t) * (hazard τ t - hazard τ (t + w))) t := by
  have hn := (hasDerivAt_relaxation hτ (by linarith : 0 < t + w)).comp t
    ((hasDerivAt_id t).add_const w)
  have hd := hn.div (hasDerivAt_relaxation hτ ht) (relaxation_pos hτ hsmall t).ne'
  convert hd using 1
  · rfl
  · dsimp [hazard]
    have h0 := (relaxation_pos hτ hsmall t).ne'
    have h1 := (relaxation_pos hτ hsmall (t + w)).ne'
    field_simp
    ring

/-- Every positive shift gives a strictly decreasing ratio on nonnegative time.
The statement uses the concrete quasi-exponential rather than an assumed kernel. -/
theorem strictAntiOn_relaxation_ratio {τ w : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (hw : 0 < w) :
    StrictAntiOn (fun t => relaxation τ (t + w) / relaxation τ t) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_ratio hτ hsmall w).continuousOn
  intro t ht
  simp only [interior_Ici, mem_Ioi] at ht
  rw [(hasDerivAt_ratio hτ hsmall ht hw.le).deriv]
  apply mul_neg_of_pos_of_neg (div_pos (relaxation_pos hτ hsmall _) (relaxation_pos hτ hsmall _))
  exact sub_neg.mpr (strictMonoOn_hazard hτ hsmall ht.le
    (show 0 ≤ t + w by linarith) (show t < t + w by linarith))

private theorem antitone_ratio {τ w : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (hw : 0 ≤ w) :
    Antitone (fun t => relaxation τ (t + w) / relaxation τ t) := by
  have hl : AntitoneOn (fun t => relaxation τ (t + w) / relaxation τ t) (Iic 0) := by
    intro x hx y hy hxy
    simp only [relaxation_of_nonpos hτ hx, relaxation_of_nonpos hτ hy, div_one]
    exact antitone_relaxation hτ hsmall (by linarith : x + w ≤ y + w)
  have hr : AntitoneOn (fun t => relaxation τ (t + w) / relaxation τ t) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (continuous_ratio hτ hsmall w).continuousOn
    · intro t ht
      simp only [interior_Ici, mem_Ioi] at ht
      exact (hasDerivAt_ratio hτ hsmall ht hw).differentiableAt.differentiableWithinAt
    · intro t ht
      simp only [interior_Ici, mem_Ioi] at ht
      rw [(hasDerivAt_ratio hτ hsmall ht hw).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos
        (div_pos (relaxation_pos hτ hsmall _) (relaxation_pos hτ hsmall _)).le
      exact sub_nonpos.mpr ((strictMonoOn_hazard hτ hsmall).monotoneOn
        ht.le (show 0 ≤ t + w by linarith) (show t ≤ t + w by linarith))
  exact hl.Iic_union_Ici hr

/-- The delayed kernel in the source bath-history integrals. -/
def responseKernel (τ s : ℝ) : ℝ := relaxation τ (s - τ)

/-- Weak real-shift order, retaining the initial plateau of the delayed kernel.
All ages and shifts are real; no mesh or integer-delay restriction is used. -/
theorem kernel_shift_order {τ a b t : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (hab : a ≤ b) (ht : 0 ≤ t) :
    responseKernel τ (t + b) * responseKernel τ a ≤
      responseKernel τ (t + a) * responseKernel τ b := by
  have h := antitone_ratio hτ hsmall ht (sub_le_sub_right hab τ)
  have hmul := (div_le_div_iff₀ (relaxation_pos hτ hsmall (b - τ))
    (relaxation_pos hτ hsmall (a - τ))).mp h
  simpa only [responseKernel, show b - τ + t = t + b - τ by ring,
    show a - τ + t = t + a - τ by ring] using hmul

/-- Every translated kernel tail is integrable, and its mass is the corresponding
source relaxation. The lower endpoint may be any real age with nonnegative sum. -/
theorem kernel_tail_mass {τ t L : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (hstart : 0 ≤ t + L) :
    MeasureTheory.IntegrableOn (fun a => responseKernel τ (t + a)) (Ioi L) ∧
      (∫ a in Ioi L, responseKernel τ (t + a)) = relaxation τ (t + L) := by
  have hc : Continuous (fun a => relaxation τ (t + a)) :=
    (continuous_relaxation hτ).comp (continuous_const.add continuous_id)
  have hd : ∀ a ∈ Ioi L, HasDerivAt (fun a => relaxation τ (t + a))
      (-responseKernel τ (t + a)) a := by
    intro a ha
    have hpos : 0 < t + a := by have := mem_Ioi.mp ha; linarith
    simpa [responseKernel] using! (hasDerivAt_relaxation hτ hpos).comp a
      ((hasDerivAt_id a).const_add t)
  have hn : ∀ a ∈ Ioi L, -responseKernel τ (t + a) ≤ 0 := by
    intro a _
    exact neg_nonpos.mpr (relaxation_pos hτ hsmall _).le
  have hl : Tendsto (fun a => relaxation τ (t + a)) atTop (𝓝 0) :=
    (tendsto_relaxation_atTop hτ hsmall).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  have hi := MeasureTheory.integrableOn_Ioi_deriv_of_nonpos
    hc.continuousAt.continuousWithinAt hd hn hl
  have he := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hc.continuousAt.continuousWithinAt hd hi hl
  rw [MeasureTheory.integral_neg, zero_sub] at he
  exact ⟨MeasureTheory.integrable_neg_iff.mp hi, neg_injective he⟩

end

end D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
