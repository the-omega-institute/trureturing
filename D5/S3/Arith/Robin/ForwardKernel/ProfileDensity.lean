/- GID: D5/S3/Arith/Robin/ForwardKernel/ProfileDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ProfileDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lipschitz profiles are dense in the integrable real profiles on the unit interval. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-! Lipschitz approximation of integrable real profiles on the unit interval. -/

namespace D5.S3.Arith.Robin.ForwardKernel.ProfileDensity

open Set MeasureTheory
open scoped NNReal
open D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

noncomputable section

/-- Every integrable profile admits arbitrarily close Lipschitz approximations in L¹. -/
theorem exists_lipschitz_profile_approx
    {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ,
      ProfileIntegrable f ∧
      (∃ L : ℝ≥0, LipschitzOnWith L f (Set.Icc (0 : ℝ) 1)) ∧
      profileL1 (fun s => g s - f s) < ε := by
  obtain ⟨c, hgc, hc⟩ := hg.2.exists_boundedContinuous_integral_sub_le
    (show 0 < ε / 3 by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 c
    c.continuous.continuousOn (ε / 3) (by positivity)
  have hpi : Integrable (fun x => p.eval x) unitMeasure :=
    p.continuous.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    p.derivative.continuous.norm.continuousOn
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith L (fun x => p.eval x) (Icc (0 : ℝ) 1) := by
    apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
    intro x hx
    change ‖p.derivative.eval x‖ ≤ max B 0
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨fun x => p.eval x, ⟨p.continuous.measurable, hpi⟩, ⟨L, hLip⟩, ?_⟩
  have hcp : (∫ x, |c x - p.eval x| ∂unitMeasure) ≤ ε / 3 := by
    calc
      _ ≤ ∫ _x, ε / 3 ∂unitMeasure := by
        apply integral_mono_ae (hc.sub hpi).norm (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using (hp x ⟨hx.1.le, hx.2⟩).le
      _ = ε / 3 := by simp [unitMeasure]
  have htri : profileL1 (fun s => g s - p.eval s) ≤
      (∫ x, |g x - c x| ∂unitMeasure) + ∫ x, |c x - p.eval x| ∂unitMeasure := by
    unfold profileL1
    have hi := integral_mono (hg.2.sub hpi).norm
      ((hg.2.sub hc).norm.add (hc.sub hpi).norm)
      (fun x => show ‖g x - p.eval x‖ ≤ ‖g x - c x‖ + ‖c x - p.eval x‖ from
        norm_sub_le_norm_sub_add_norm_sub _ _ _)
    simp only [Pi.add_apply] at hi
    rw [integral_add (hg.2.sub hc).norm (hc.sub hpi).norm] at hi
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi
  simp only [Real.norm_eq_abs] at hgc
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.ProfileDensity
