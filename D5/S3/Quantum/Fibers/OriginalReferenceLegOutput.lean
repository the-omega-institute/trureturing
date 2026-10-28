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
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    L.duration_pos.le).mp
      ((L.density_cont i).intervalIntegrable_of_Icc L.duration_pos.le)

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

/-- Every Borel time event has a positive actual Kraus output. Its Bochner
integral has exactly the integral of the trace norms, on the same reference. -/
theorem affine_failure_event (L : Leg) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (E : Set ℝ) (hE : MeasurableSet E) :
    let D := (Ioc 0 L.duration) ∩ E
    let F := fun t => failureOutput L.c L.x (L.height t) (L.survival t)
      (L.jumpRate t) i rho hpos
    IntegrableOn F D ∧
    (∀ t ∈ D, (F t).1 =
      (referenceJump L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i).comp
        (rho.1.comp
          (referenceJump L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i).adjoint)) ∧
    0 ≤ (∫ t in D, F t).1 ∧
    ‖∫ t in D, F t‖ = ∫ t in D, ‖F t‖ := by
  dsimp only
  let f := fun t => coefficient L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i
  let A : TraceClass H := TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
  have hn (t : ℝ) (ht : t ∈ (Ioc 0 L.duration) ∩ E) : 0 ≤ f t :=
    mul_nonneg (mul_nonneg (L.jumpRate_nonneg t ⟨ht.1.1.le, ht.1.2⟩ i)
      (Real.exp_pos _).le)
      (div_nonneg (p_pos _ _ L.c_lt (L.height_bounds t ⟨ht.1.1.le, ht.1.2⟩) i).le
        (p_pos _ _ L.c_lt ⟨L.x_pos, L.x_lt⟩ i).le)
  have hna : 0 ≤ᵐ[volume.restrict ((Ioc 0 L.duration) ∩ E)] f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.inter hE)] with t ht
    exact hn t ht
  have hint := (affine_failure_bochner L i rho hpos).2 E hE
  rw [integral_complex_ofReal] at hint
  refine ⟨(affine_failure_bochner L i rho hpos).1.mono_set inter_subset_left, ?_, ?_, ?_⟩
  · intro t ht
    exact (actual_jump_trace_norm L.c L.x (L.height t) (L.survival t)
      (L.jumpRate t) i L.c_lt ⟨L.x_pos, L.x_lt⟩
      (L.height_bounds t ⟨ht.1.1.le, ht.1.2⟩) (Real.exp_pos _).le
      (L.jumpRate_nonneg t ⟨ht.1.1.le, ht.1.2⟩ i) rho hpos).1
  · rw [hint]
    change 0 ≤ ((∫ t in (Ioc 0 L.duration) ∩ E, f t : ℝ) : ℂ) • compression rho.1 i
    exact smul_nonneg (by exact_mod_cast integral_nonneg_of_ae hna)
      (compression_nonneg hpos i)
  · have hnorm : ∀ᵐ t ∂volume.restrict ((Ioc 0 L.duration) ∩ E),
        ‖failureOutput L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i rho hpos‖ =
          f t * ‖A‖ := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.inter hE)] with t ht
      change ‖(f t : ℂ) • A‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn t ht)]
    rw [hint, integral_congr_ae hnorm, integral_mul_const]
    change ‖((∫ t in (Ioc 0 L.duration) ∩ E, f t : ℝ) : ℂ) • A‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg_of_ae hna)]

end D5.S3.Quantum.Fibers.OriginalReferenceLegOutput
