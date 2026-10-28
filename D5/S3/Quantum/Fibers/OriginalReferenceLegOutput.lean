/- GID: D5/S3/Quantum/Fibers/OriginalReferenceLegOutput
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceLegOutput
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bochner output on the full reference for actual original affine legs. -/

import D5.S3.Quantum.Fibers.OriginalReferenceKraus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tensor amplification and trace-norm integrals retain the same reference. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace TensorProduct BigOperators Matrix
open TraceClassFiniteBlocks MeasureTheory Set

namespace D5.S3.Quantum.Fibers.OriginalReferenceLegOutput
open OriginalControlMarkedJump OriginalReferenceKraus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual absorbing row tensored with the unchanged reference, on every
joint vector, under the finite Hilbert tensor correspondence. -/
theorem tensor_jump_intertwining (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (z : EuclideanSpace ℂ (Fin 5) ⊗[ℂ] H) :
    referenceJump c a k S g i (tensorCoordinates z) =
      TensorProduct.lid ℂ H
        (TensorProduct.map (referenceJump (H := ℂ) c a k S g i).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    simp [referenceJump, coordinate, tensorCoordinates_tmul,
      TensorProduct.map_tmul, Finset.sum_smul, smul_smul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem leg_scalar_integrable (L : Leg) (i : Fin 5) :
    IntegrableOn (fun t => L.density t i) (Ioc 0 L.duration) := by
  obtain ⟨_,_,_,_,_,_,hS,hprob,_⟩ := L.affine_marked_probability 0 0 0 (fun _ => 0)
  have hk : Continuous L.height := continuous_iff_continuousAt.mpr
    (fun t => (L.height_deriv t).continuousAt)
  have hp : Measurable (fun t => p L.c (L.height t) i) := by
    simp only [p_explicit]
    fin_cases i <;> fun_prop
  have hh : Measurable L.hazard := by unfold Leg.hazard; fun_prop
  have hr : Measurable (fun t => L.jumpRate t i) :=
    hh.sub (measurable_deriv _)
  have hsc : ContinuousOn L.survival (Icc 0 L.duration) := by
    have hi : IntervalIntegrable L.hazard volume 0 L.duration :=
      (L.hazard_cont).intervalIntegrable_of_Icc L.duration_pos.le
    have hc := (intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 L.duration)).neg.exp
    simpa only [uIcc_of_le L.duration_pos.le, Leg.survival] using hc
  have hm : AEStronglyMeasurable (fun t => L.density t i)
      (volume.restrict (Ioc 0 L.duration)) := by
    exact ((hr.aestronglyMeasurable.mul
      ((hsc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mul
        hp.aestronglyMeasurable)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 L.duration)] (fun t => L.density t i) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg (L.jumpRate_nonneg t ⟨ht.1.le,ht.2⟩ i)
      (Real.exp_pos _).le) (p_pos _ _ L.c_lt (L.height_bounds t ⟨ht.1.le,ht.2⟩) i).le
  apply (ENNReal.lintegral_ofReal_ne_top_iff_integrable hm hn).mp
  have hmode : L.modeMeasure i univ ≤ L.markedLaw univ := by
    have he (j : Fin 5) :
        ((L.modeMeasure j).map (fun t => (Sum.inr (j,t) : Leg.Record))) univ =
          L.modeMeasure j univ := by
      rw [Measure.map_apply (measurable_inr.comp (measurable_const.prodMk measurable_id))
        MeasurableSet.univ]
      simp
    simp only [Leg.markedLaw, Measure.add_apply, Measure.finsetSum_apply, he]
    exact le_trans (Finset.single_le_sum (fun j _ => zero_le _) (Finset.mem_univ i))
      (le_add_of_nonneg_left (zero_le _))
  haveI := hprob
  have hf : L.modeMeasure i univ ≠ ⊤ := ne_top_of_le_ne_top (by simp) hmode
  simpa only [Leg.modeMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using hf

/-- The actual original affine-leg failure density is Bochner integrable in the
trace norm for every reference, and every Borel subevent retains that reference. -/
theorem affine_failure_bochner (L : Leg) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    IntegrableOn (fun t => failureOutput L.c L.x (L.height t) (L.survival t)
      (L.jumpRate t) i rho hpos) (Ioc 0 L.duration) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      (∫ t in (Ioc 0 L.duration) ∩ E,
        failureOutput L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i rho hpos) =
      (∫ t in (Ioc 0 L.duration) ∩ E,
        (coefficient L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i : ℂ)) •
          TraceClass.ofOperator (compression rho.1 i)
            (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i) := by
  have he (t : ℝ) : coefficient L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i =
      L.density t i / p L.c L.x i := by
    unfold coefficient Leg.density
    ring
  have hi : IntegrableOn (fun t =>
      (coefficient L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i : ℂ))
      (Ioc 0 L.duration) := by
    simp_rw [he]
    exact ((leg_scalar_integrable L i).div_const (p L.c L.x i)).ofReal
  refine ⟨hi.smul_const _, ?_⟩
  intro E hE
  exact integral_smul_const _ _

end D5.S3.Quantum.Fibers.OriginalReferenceLegOutput
