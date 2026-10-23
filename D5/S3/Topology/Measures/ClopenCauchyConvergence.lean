/- GID: D5/S3/Topology/Measures/ClopenCauchyConvergence
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/ClopenCauchyConvergence
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Full signed weak-star convergence follows from uniform total variation bounds and Cauchy values on all clopen sets. -/

import D5.S3.Topology.Measures.SignedWeakStarCompactness
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

namespace D5.S3.Topology.Measures.ClopenCauchyConvergence

universe u

variable {K : Type u} [MetricSpace K] [CompactSpace K]
  [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]

private noncomputable def locallyConstantSimpleFunc
    (f : LocallyConstant K ℝ) : SimpleFunc K ℝ :=
  SimpleFunc.mk f
    (fun x => (f.isLocallyConstant.isClopen_fiber x).isClosed.measurableSet)
    f.range_finite

private lemma signedFunctional_charFn (r : SignedMeasure K) {A : Set K}
    (hA : IsClopen A) :
    NormPreservingLifts.signedFunctional r
        (LocallyConstant.charFn ℝ hA).toContinuousMap = r A := by
  letI : IsFiniteMeasure r.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  change (∫ᵛ x, (LocallyConstant.charFn ℝ hA) x ∂•r) = r A
  rw [VectorMeasure.integral_eq_setToFun, LocallyConstant.coe_charFn]
  change setToFun r.variation (r.transpose (ContinuousLinearMap.lsmul ℝ ℝ)) _
      (Set.indicator A (fun _ : K => (1 : ℝ))) = r A
  rw [setToFun_indicator_const
    (dominatedFinMeasAdditive_cbmApplyMeasure r
      (ContinuousLinearMap.lsmul ℝ ℝ)) hA.isClosed.measurableSet
    (measure_ne_top _ _) (1 : ℝ)]
  simp [transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply]

private lemma signedFunctional_locallyConstant_sum (r : SignedMeasure K)
    (f : LocallyConstant K ℝ) :
    NormPreservingLifts.signedFunctional r f.toContinuousMap =
      ∑ x ∈ (locallyConstantSimpleFunc f).range, r (f ⁻¹' {x}) * x := by
  let g := locallyConstantSimpleFunc f
  letI : IsFiniteMeasure r.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hg : Integrable (g : K → ℝ) r.variation := by
    change Integrable (f : K → ℝ) r.variation
    rw [← SignedMeasure.totalVariation_eq_variation]
    exact f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ᵛ x, g x ∂•r) = _
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc
      (dominatedFinMeasAdditive_cbmApplyMeasure r
        (ContinuousLinearMap.lsmul ℝ ℝ)) g hg]
  simp [g, locallyConstantSimpleFunc, transpose_eq_cbmApplyMeasure,
    cbmApplyMeasure_apply, mul_comm]
  rfl

set_option maxHeartbeats 800000 in
theorem tendsto_signedFunctional_of_clopen_cauchy
    (C : ℝ) (hC : 0 ≤ C) (s : ℕ → SignedMeasure K)
    (hbound : ∀ n, (s n).totalVariation.real univ ≤ C)
    (hcauchy : ∀ A : Set K, IsClopen A →
      CauchySeq (fun n => (s n) A)) :
    ∃ μ : SignedMeasure K,
      μ.totalVariation.real univ ≤ C ∧
      Measure.Regular μ.toJordanDecomposition.posPart ∧
      Measure.Regular μ.toJordanDecomposition.negPart ∧
      Tendsto (fun n =>
        (NormPreservingLifts.signedFunctional (s n)).toWeakDual) atTop
        (𝓝 (NormPreservingLifts.signedFunctional μ).toWeakDual) := by
  obtain ⟨phi, μ, hphi, hμbound, hsub⟩ :=
    SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
      C hC s hbound
  have hclopen : ∀ A : Set K, IsClopen A →
      Tendsto (fun n => (s n) A) atTop (𝓝 (μ A)) := by
    intro A hA
    have hsubA :=
      (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hsub)
        ((LocallyConstant.charFn ℝ hA).toContinuousMap)
    change Tendsto (fun n =>
      NormPreservingLifts.signedFunctional (s (phi n))
        ((LocallyConstant.charFn ℝ hA).toContinuousMap)) atTop
      (𝓝 (NormPreservingLifts.signedFunctional μ
        ((LocallyConstant.charFn ℝ hA).toContinuousMap))) at hsubA
    have hsubA' : Tendsto (fun n => (s (phi n)) A) atTop (𝓝 (μ A)) := by
      simpa only [signedFunctional_charFn] using hsubA
    exact tendsto_nhds_of_cauchySeq_of_subseq (hcauchy A hA)
      hphi.tendsto_atTop (by
        simpa [Function.comp_def] using hsubA')
  have hlc : ∀ f : LocallyConstant K ℝ,
      Tendsto (fun n => NormPreservingLifts.signedFunctional (s n)
        f.toContinuousMap) atTop
        (𝓝 (NormPreservingLifts.signedFunctional μ f.toContinuousMap)) := by
    intro f
    let g := locallyConstantSimpleFunc f
    have hsum : Tendsto (fun n =>
        ∑ x ∈ g.range, (s n) (f ⁻¹' {x}) * x) atTop
        (𝓝 (∑ x ∈ g.range, (μ (f ⁻¹' {x})) * x)) := by
      apply tendsto_finsetSum
      intro x hx
      have hfx : IsClopen (f ⁻¹' {x}) :=
        f.isLocallyConstant.isClopen_fiber x
      simpa only using (hclopen (f ⁻¹' {x}) hfx).mul tendsto_const_nhds
    simpa only [signedFunctional_locallyConstant_sum] using hsum
  have hnormS (n : ℕ) :
      ‖NormPreservingLifts.signedFunctional (s n)‖ ≤ C :=
    (NormPreservingLifts.signedFunctional_norm_le (s n)).trans (hbound n)
  have hweak : Tendsto (fun n =>
      (NormPreservingLifts.signedFunctional (s n)).toWeakDual) atTop
      (𝓝 (NormPreservingLifts.signedFunctional μ).toWeakDual) := by
    apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
    intro f
    change Tendsto (fun n =>
      NormPreservingLifts.signedFunctional (s n) f) atTop
      (𝓝 (NormPreservingLifts.signedFunctional μ f))
    let A := (LocallyConstant.toContinuousMapAlgHom ℝ (X := K) (Y := ℝ)).range
    have hequiv :
        (∃ D : ℝ, ∀ n, ‖NormPreservingLifts.signedFunctional (s n)‖ ≤ D) ↔
          Equicontinuous (fun n =>
            (NormPreservingLifts.signedFunctional (s n) : C(K, ℝ) → ℝ)) :=
      (NormedSpace.equicontinuous_TFAE
        (fun n => NormPreservingLifts.signedFunctional (s n))).out 6 2
    have hequi := hequiv.mp ⟨C, hnormS⟩
    apply (hequi f).tendsto_of_mem_closure (s := (A : Set C(K, ℝ)))
      (NormPreservingLifts.signedFunctional μ).continuous.continuousAt.continuousWithinAt
    · rintro g ⟨a, rfl⟩
      exact hlc a
    · exact ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints A
        (LocallyConstant.separatesPoints_range_toContinuousMapAlgHom ℝ) f
  refine ⟨μ, hμbound, inferInstance, inferInstance, hweak⟩

end D5.S3.Topology.Measures.ClopenCauchyConvergence
