/- GID: D5/S3/Analysis/TranslatedFourierPacket
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-de-sitter-kernel-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pairing growth and Fourier norm invariance for translations of compact packets. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import D5.S3.Analysis.LogisticCoordinate

/-!
Omega original.

Pairing growth and Fourier norm invariance for translations of compact packets.
A logistic change of coordinates transfers power singularities to this setting.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform Topology

namespace Omega

/-- Translating a nonnegative compact packet into the region where a continuous function tends
to positive infinity makes its integral pairing tend to positive infinity. -/
theorem tendsto_integral_mul_translate {q g : ℝ → ℝ} (hq : Continuous q)
    (hq_lim : Tendsto q atBot atTop) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : 0 ≤ g) (hg0 : ∃ x, g x ≠ 0) :
    Tendsto (fun a : ℝ => ∫ s : ℝ, q s * g (s + a)) atTop atTop := by
  let m : ℝ := ∫ s : ℝ, g s
  obtain ⟨x, hx⟩ := hg0
  have hm : 0 < m := hg.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc hgn hx
  obtain ⟨b, hb⟩ := hgc.bddAbove
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨B, hB⟩ := eventually_atBot.1 (hq_lim.eventually_ge_atTop (M / m))
  filter_upwards [eventually_ge_atTop (b - B)] with a ha
  have hshift : (∫ s : ℝ, q s * g (s + a)) = ∫ s : ℝ, q (s - a) * g s := by
    simpa [add_sub_cancel_right] using
      integral_add_right_eq_self (fun s : ℝ => q (s - a) * g s) a
  change M ≤ ∫ s : ℝ, q s * g (s + a)
  rw [hshift, ← div_mul_cancel₀ M hm.ne', ← integral_const_mul]
  apply integral_mono ((hg.integrable_of_hasCompactSupport hgc).const_mul _)
  · exact ((hq.comp (continuous_id.sub continuous_const)).mul hg).integrable_of_hasCompactSupport
      hgc.mul_left
  · intro s
    by_cases hs : g s = 0
    · simp [hs]
    · exact mul_le_mul_of_nonneg_right (hB _ (by linarith [hb (subset_tsupport _ hs)])) (hgn s)

/-- The weighted square integral of the Fourier modulus is invariant under translation. -/
theorem integral_weighted_fourier_sq_translate (g : ℝ → ℂ) (w : ℝ → ℝ) (a : ℝ) :
    (∫ ξ : ℝ, w ξ * ‖𝓕 (fun s : ℝ => g (s + a)) ξ‖ ^ 2) =
      ∫ ξ : ℝ, w ξ * ‖𝓕 g ξ‖ ^ 2 := by
  have hphase := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) g a
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  change w ξ * ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (g ∘ fun s => s + a) ξ‖ ^ 2 =
    w ξ * ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g ξ‖ ^ 2
  rw [hphase, Circle.norm_smul]

/-- Solitary power growth of a radial factor with exponent below minus one
survives multiplication by the logistic-coordinate Jacobian. -/
theorem tendsto_logistic_jacobian_mul {b L κ c δ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hκ : 1 < κ) (hc : 0 < c) (hδ : 0 < δ)
    {q : ℝ → ℝ} (hlower : ∀ u ∈ Set.Ioo (0 : ℝ) δ, c * u ^ (-κ) ≤ q u) :
    Tendsto (fun s => b * ((L * logistic b s) * (1 - logistic b s)) *
      q (L * logistic b s)) atBot atTop := by
  let p := logistic b
  let u : ℝ → ℝ := fun s => L * p s
  have hp s : 0 < p s ∧ p s < 1 := ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩
  have hu s : 0 < u s := mul_pos hL (hp s).1
  have hp0 : Tendsto p atBot (𝓝 0) :=
    Real.tendsto_sigmoid_atBot.comp ((tendsto_const_mul_atBot_of_pos hb).2 tendsto_id)
  have hu0 : Tendsto u atBot (𝓝 0) := by
    change Tendsto (fun s : ℝ => L * p s) atBot (𝓝 0)
    simpa only [mul_zero] using hp0.const_mul L
  have hu0' : Tendsto u atBot (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu0 (Eventually.of_forall hu)
  have hpow : Tendsto (fun s => u s ^ (1 - κ)) atBot atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hκ)).comp hu0'
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (𝓝 1) := tendsto_const_nhds
  have hj : Tendsto (fun s => b * (1 - p s) * c) atBot (𝓝 (b * c)) := by
    simpa only [sub_zero, mul_one] using ((hone.sub hp0).const_mul b).mul_const c
  refine tendsto_atTop_mono' _ ?_ (hj.pos_mul_atTop (mul_pos hb hc) hpow)
  filter_upwards [hu0.eventually (eventually_lt_nhds hδ)] with s hs
  calc
    b * (1 - p s) * c * u s ^ (1 - κ) = (b * (u s * (1 - p s))) * (c * u s ^ (-κ)) := by
      rw [show 1 - κ = 1 + (-κ) by ring, Real.rpow_add (hu s), Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hlower (u s) ⟨hu s, hs⟩)
      (mul_nonneg hb.le (mul_nonneg (hu s).le (sub_nonneg.mpr (hp s).2.le)))

end Omega
