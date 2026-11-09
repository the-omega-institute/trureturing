/- GID: D5/S3/Quantum/Analysis/MeasurableFirstResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/MeasurableFirstResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp vector response of the original measurable evolution. -/

import D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Taylor

/-! # Sharp first response for vectorwise measurable coefficients -/

open scoped Topology
open MeasureTheory Filter intervalIntegral
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel

namespace D5.S3.Quantum.Analysis.MeasurableFirstResponse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual vector Bochner response, using the original measurable evolution. -/
noncomputable def response (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    (t r : ℝ) (x : E) : E :=
  ∫ s in r..t, measurableEvolution S B t s (H s (measurableEvolution S B s r x))

private theorem native_bound (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    {t r : ℝ} (hp : (t,r) ∈ triangle T) (x : E) :
    ‖measurableEvolution S B t r x‖ ≤ Real.exp (∫ s in r..t, g s) * ‖x‖ := by
  obtain ⟨Phi, hPhi⟩ := measurable_evolution S
  rcases hPhi B T hT hB g hg hgn hBg with
    ⟨_, _, _, hseries, _, _, _, _, _, hb, _⟩
  have heq : Phi B t r x = measurableEvolution S B t r x := by
    rw [measurableEvolution_apply S B (hp.2.1.trans hp.2.2)
      (fun z => (hB z).mono_set (Set.Icc_subset_Icc hp.1 le_rfl)) g
      (hg.mono_set (Set.Icc_subset_Icc hp.1 le_rfl))
      (fun s hs => hgn s ⟨hp.1.trans hs.1, hs.2⟩)
      (fun s hs => hBg s ⟨hp.1.trans hs.1, hs.2⟩) ⟨hp.2.1, hp.2.2⟩ x]
    exact (hseries t r hp x).2.tsum_eq
  rw [← heq]
  exact ((Phi B t r).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hb t r hp) (norm_nonneg x))

private theorem clock_nonneg {r t : ℝ} (hrt : r ≤ t) {h : ℝ → ℝ}
    (hn : ∀ s ∈ Set.Icc r t, 0 ≤ h s) : 0 ≤ ∫ s in r..t, h s :=
  intervalIntegral.integral_nonneg hrt (fun s hs => hn s ⟨hs.1.le, hs.2⟩)

private theorem clock_split {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r t)) :
    (∫ z in r..s, g z) + (∫ z in s..t, g z) = ∫ z in r..t, g z := by
  exact intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hrs).mpr
      (hg.mono_set (Set.Icc_subset_Icc le_rfl hst)))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
      (hg.mono_set (Set.Icc_subset_Icc hrs le_rfl)))

private theorem exponential_clock {r t : ℝ} (hrt : r ≤ t) {h : ℝ → ℝ}
    (hh : IntegrableOn h (Set.Icc r t)) (hn : ∀ s ∈ Set.Icc r t, 0 ≤ h s) :
    IntervalIntegrable (fun s => h s * Real.exp (∫ z in s..t, h z)) volume r t ∧
    (∫ s in r..t, h s * Real.exp (∫ z in s..t, h z)) =
      Real.exp (∫ s in r..t, h s) - 1 := by
  let A := ∫ s in r..t, h s
  let F : ℝ → ℝ := fun s => ∫ z in r..s, h z
  let K : ℝ → ℝ := fun s => A - F s
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hh
  have hF : AbsolutelyContinuousOnInterval F r t :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hK : AbsolutelyContinuousOnInterval K r t :=
    (hF.neg).add (show AbsolutelyContinuousOnInterval (fun _ : ℝ => A) r t from
      (LipschitzWith.const A).absolutelyContinuousOnInterval)
  have hKe : ∀ s ∈ Set.Icc r t, K s = ∫ z in s..t, h z := by
    intro s hs
    have he := clock_split hs.1 hs.2 hh
    dsimp [K, F, A]
    linarith
  have hKm : Set.MapsTo K (Set.uIcc r t) (Set.Icc 0 A) := by
    intro s hs
    rw [Set.uIcc_of_le hrt] at hs
    refine ⟨?_, ?_⟩
    · rw [hKe s hs]
      exact clock_nonneg hs.2 (fun z hz => hn z ⟨hs.1.trans hz.1, hz.2⟩)
    · have hpos := clock_nonneg hs.1 (fun z hz => hn z ⟨hz.1, hz.2.trans hs.2⟩)
      dsimp [K, F]
      linarith
  obtain ⟨C, hC⟩ := (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp
    (Set.Icc 0 A)).exists_lipschitzOnWith (by decide) (convex_Icc 0 A) isCompact_Icc
  have hExp : AbsolutelyContinuousOnInterval (fun s => Real.exp (K s)) r t :=
    hC.comp_absolutelyContinuousOnInterval hKm hK
  have hd : (fun s => deriv (fun u => Real.exp (K u)) s) =ᵐ[
      volume.restrict (Set.uIcc r t)] (fun s => -(h s * Real.exp (K s))) := by
    apply (ae_restrict_iff' measurableSet_uIcc).mpr
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    have he := ((hasDerivAt_const s A).sub (hs hmem r (by simp))).exp
    simpa [K, F, mul_comm] using he.deriv
  have hw : IntervalIntegrable (fun s => h s * Real.exp (K s)) volume r t :=
    hi.mul_continuousOn hExp.continuousOn
  have hFTC := hExp.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae_restrict
    (hd.filter_mono (ae_mono (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl))),
    intervalIntegral.integral_neg] at hFTC
  have hval : (∫ s in r..t, h s * Real.exp (K s)) = Real.exp A - 1 := by
    simp only [K, F, intervalIntegral.integral_same, sub_zero, sub_self, Real.exp_zero]
      at hFTC
    linarith
  have heq : ∀ s ∈ Set.uIcc r t,
      h s * Real.exp (K s) = h s * Real.exp (∫ z in s..t, h z) := by
    intro s hs
    rw [hKe s (by simpa [Set.uIcc_of_le hrt] using hs)]
  refine ⟨hw.congr (fun s hs => heq s (Set.uIoc_subset_uIcc hs)), ?_⟩
  rw [← intervalIntegral.integral_congr heq]
  exact hval

end D5.S3.Quantum.Analysis.MeasurableFirstResponse
