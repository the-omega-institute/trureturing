/- GID: D5/S3/Quantum/Fibers/OriginalReferenceOutputMeasure
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceOutputMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual repeated-control failure outputs are trace-norm Bochner integrable. -/

import D5.S3.Quantum.Fibers.OriginalReferenceLegOutput
import D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw

/-! Exact time events retain the same arbitrary Hilbert reference. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix TensorProduct
open TraceClassFiniteBlocks MeasureTheory Set

namespace D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure
open OriginalControlMarkedJump OriginalReferenceKraus OriginalMarkedConcatenation
open OriginalRepeatedPrefix OriginalControlComposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The squared literal jump amplitude, including the totalized values at corners. -/
def modeCoefficient (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ) : ℝ :=
  Complex.normSq (amplitude c a (k t) (survival c k t) (jumpRate c k t) i)

/-- The actual trace-class density on the retained reference, from the same input. -/
def modeOutput (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) : TraceClass H :=
  (modeCoefficient c a k i t : ℂ) • TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)

/-- The literal absorbing row tensored with the identity, as a bounded map on
the complete finite-system Hilbert tensor product. -/
def tensorJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    (EuclideanSpace ℂ (Fin 5) ⊗[ℂ] H) →L[ℂ] H := by
  let L := (TensorProduct.lid ℂ H).toLinearMap.comp
    (TensorProduct.map (referenceJump (H := ℂ) c a k S g i).toLinearMap
      (LinearMap.id : H →ₗ[ℂ] H))
  refine { toLinearMap := L, cont := ?_ }
  have he : (L : _ → H) = fun z => referenceJump c a k S g i (tensorCoordinates z) := by
    funext z
    exact (OriginalReferenceLegOutput.tensor_jump_intertwining c a k S g i z).symm
  change Continuous (L : _ → H)
  rw [he]
  exact (referenceJump c a k S g i).continuous.comp tensorCoordinates.continuous

/-- Coordinates of the actual tensor-amplified row, with no change of reference. -/
def referenceTensorJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Blocks (Fin 5) H →L[ℂ] H :=
  (tensorJump c a k S g i).comp
    (tensorCoordinates (H := H) (ι := Fin 5)).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem referenceTensorJump_eq (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    referenceTensorJump (H := H) c a k S g i = referenceJump c a k S g i := by
  ext x
  change TensorProduct.lid ℂ H
    (TensorProduct.map (referenceJump (H := ℂ) c a k S g i).toLinearMap
      (LinearMap.id : H →ₗ[ℂ] H) (tensorCoordinates.symm x)) = _
  rw [← OriginalReferenceLegOutput.tensor_jump_intertwining,
    LinearIsometryEquiv.apply_symm_apply]

theorem source_coefficient (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (i : Fin 5) (t : ℝ) (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c) :
    failureDensity c a beta m theta k i t = modeCoefficient c a k i t * p c a i := by
  rw [failureDensity, jump_action]
  simp only [jump, live, Complex.normSq_mul, modeCoefficient, amplitude]
  rw [source_diagonal c a beta m theta hc ha]
  ring

theorem coefficient_measurable (c a T : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (hk : OriginalControl (c,c,1-2*c) T k (fun _ => (0:ℝ))) :
    AEStronglyMeasurable (modeCoefficient c a k i) (volume.restrict (Ioc 0 T)) := by
  have hkm : AEStronglyMeasurable k (volume.restrict (Ioc 0 T)) :=
    (hk.2.1.mono (by rw [uIcc_of_le hk.1]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_Ioc
  have hd : AEStronglyMeasurable (deriv k) (volume.restrict (Ioc 0 T)) :=
    (measurable_deriv k).aestronglyMeasurable
  have hh : AEStronglyMeasurable (hazard c k) (volume.restrict (Ioc 0 T)) :=
    ((hd.sup aestronglyMeasurable_const).div₀ hkm).add
      ((hd.neg.sup aestronglyMeasurable_const).div₀ (aestronglyMeasurable_const.sub hkm))
  have hg : AEStronglyMeasurable (fun t => jumpRate c k t i)
      (volume.restrict (Ioc 0 T)) := hh.sub (measurable_deriv _).aestronglyMeasurable
  have hs : ContinuousOn (survival c k) (Icc 0 T) := by
    have hc := ((intervalIntegral.continuousOn_primitive_interval'
      (hazard_integrable c T 0 k hk)
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)).neg.rexp)
    change ContinuousOn (fun t : ℝ => Real.exp (-(∫ u in (0:ℝ)..t, hazard c k u)))
      (Icc 0 T)
    simpa only [uIcc_of_le hk.1, Pi.neg_apply] using hc
  have hsm : AEStronglyMeasurable (survival c k) (volume.restrict (Ioc 0 T)) :=
    (hs.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hp : AEStronglyMeasurable (fun t => p c (k t) i)
      (volume.restrict (Ioc 0 T)) := by
    simp only [p_explicit]
    fin_cases i
    · simpa using hkm
    · change AEStronglyMeasurable ((fun _ : ℝ => c) - k) (volume.restrict (Ioc 0 T))
      exact aestronglyMeasurable_const.sub hkm
    · exact aestronglyMeasurable_const
    · change AEStronglyMeasurable ((fun _ : ℝ => c) - k) (volume.restrict (Ioc 0 T))
      exact aestronglyMeasurable_const.sub hkm
    · simpa using hkm
  have ham : AEStronglyMeasurable
      (fun t => amplitude c a (k t) (survival c k t) (jumpRate c k t) i)
      (volume.restrict (Ioc 0 T)) := by
    unfold amplitude
    exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg)).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          (Real.continuous_sqrt.comp_aestronglyMeasurable hsm))).mul
            (Complex.continuous_ofReal.comp_aestronglyMeasurable
              (Real.continuous_sqrt.comp_aestronglyMeasurable
                (hp.div₀ aestronglyMeasurable_const)))
  exact Complex.continuous_normSq.comp_aestronglyMeasurable ham

private theorem coefficient_integrable (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (i : Fin 5) :
    let k := if e then B.early n hn else B.late n hn
    IntegrableOn (modeCoefficient B.c B.a k i) (Ioc 0 2) := by
  let k := if e then B.early n hn else B.late n hn
  obtain ⟨_,_,hE,hL,_⟩ := early_late_native_survival B n hn 0
  have hk : OriginalControl (B.c,B.c,1-2*B.c) 2 k (fun _ => (0:ℝ)) := by
    cases e <;> assumption
  have hm := coefficient_measurable B.c B.a 2 k i hk
  have hprob := (OriginalRepeatedMarkedLaw.early_late_marked_probability B n hn
    0 0 (fun _ => 0) e).1
  letI := hprob
  have hbound : failureMeasure B.c B.a 0 2 0 (fun _ => 0) k i univ ≤
      markedLaw B.c B.a 0 2 0 (fun _ => 0) k univ := by
    have he (j : Fin 5) :
        ((failureMeasure B.c B.a 0 2 0 (fun _ => 0) k j).map
          (fun t => (Sum.inr (j,t) : Leg.Record))) univ =
          failureMeasure B.c B.a 0 2 0 (fun _ => 0) k j univ := by
      have hm : Measurable (fun t : ℝ => (Sum.inr (j,t) : Leg.Record)) :=
        measurable_inr.comp (measurable_const.prodMk measurable_id)
      rw [Measure.map_apply hm MeasurableSet.univ]
      simp
    simp only [markedLaw, Measure.add_apply, Measure.finsetSum_apply, he]
    calc
      _ ≤ ∑ j : Fin 5, failureMeasure B.c B.a 0 2 0 (fun _ => 0) k j univ :=
        Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hfinite : failureMeasure B.c B.a 0 2 0 (fun _ => 0) k i univ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hbound
  have hf : IntegrableOn (fun t => failureDensity B.c B.a 0 0 (fun _ => 0) k i t)
      (Ioc 0 2) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((hm.mul_const _).congr (by
        filter_upwards [] with t
        exact (source_coefficient B.c B.a 0 0 (fun _ => 0) k i t B.c_lt
          ⟨B.a_pos,B.ab.trans B.bc⟩).symm))
      (ae_of_all _ (fun t => Complex.normSq_nonneg _))).mp
    simpa only [failureMeasure, failureDensity, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using hfinite
  have hp := p_pos B.c B.a B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩ i
  have he (t : ℝ) : modeCoefficient B.c B.a k i t =
      failureDensity B.c B.a 0 0 (fun _ => 0) k i t / p B.c B.a i := by
    rw [source_coefficient B.c B.a 0 0 (fun _ => 0) k i t B.c_lt
      ⟨B.a_pos,B.ab.trans B.bc⟩, mul_div_cancel_right₀ _ hp.ne']
  change IntegrableOn (fun t => modeCoefficient B.c B.a k i t) (Ioc 0 2)
  simp_rw [he]
  exact hf.div_const _

/-- For the literal repeated early/late programmes, every mode is an actual
positive trace-class Kraus density, Bochner integrable on every Borel time event. -/
theorem repeated_failure_event (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (i : Fin 5) (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    let k := if e then B.early n hn else B.late n hn
    let F := modeOutput B.c B.a k i rho hpos
    (∀ t : ℝ, (F t).1 =
      (referenceTensorJump B.c B.a (k t) (survival B.c k t) (jumpRate B.c k t) i).comp
        (rho.1.comp
          (referenceTensorJump B.c B.a (k t) (survival B.c k t) (jumpRate B.c k t) i).adjoint)) ∧
    IntegrableOn F (Ioc 0 2) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      let D := (Ioc 0 2) ∩ E
      IntegrableOn F D ∧ 0 ≤ (∫ t in D, F t).1 ∧
      (∫ t in D, F t) =
        ((∫ t in D, modeCoefficient B.c B.a k i t : ℝ) : ℂ) •
          TraceClass.ofOperator (compression rho.1 i)
            (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i) ∧
      ‖∫ t in D, F t‖ = ∫ t in D, ‖F t‖ := by
  dsimp only
  let k := if e then B.early n hn else B.late n hn
  let f := modeCoefficient B.c B.a k i
  let A : TraceClass H := TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
  have hi := coefficient_integrable B n hn e i
  have hout : IntegrableOn (modeOutput B.c B.a k i rho hpos) (Ioc 0 2) :=
    hi.ofReal.smul_const A
  refine ⟨?_, hout, ?_⟩
  · intro t
    rw [referenceTensorJump_eq]
    exact (actual_raw_jump_operator B.c B.a (k t) (survival B.c k t)
      (jumpRate B.c k t) i rho.1).symm
  intro E hE
  have hn : 0 ≤ᵐ[volume.restrict ((Ioc 0 2) ∩ E)] f :=
    ae_of_all _ (fun t => Complex.normSq_nonneg _)
  have hint : (∫ t in (Ioc 0 2) ∩ E, modeOutput B.c B.a k i rho hpos t) =
      ((∫ t in (Ioc 0 2) ∩ E, f t : ℝ) : ℂ) • A := by
    change (∫ t in (Ioc 0 2) ∩ E, (f t : ℂ) • A) = _
    rw [integral_smul_const, integral_complex_ofReal]
  refine ⟨hout.mono_set inter_subset_left, ?_, hint, ?_⟩
  · rw [hint]
    change 0 ≤ ((∫ t in (Ioc 0 2) ∩ E, f t : ℝ) : ℂ) • compression rho.1 i
    exact smul_nonneg (by exact_mod_cast integral_nonneg_of_ae hn)
      (compression_nonneg hpos i)
  · have he (t : ℝ) : ‖modeOutput B.c B.a k i rho hpos t‖ = f t * ‖A‖ := by
      change ‖(f t : ℂ) • A‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ f t from Complex.normSq_nonneg _)]
    have hnint : (∫ t in (Ioc 0 2) ∩ E, ‖modeOutput B.c B.a k i rho hpos t‖) =
        (∫ t in (Ioc 0 2) ∩ E, f t) * ‖A‖ := by
      rw [integral_congr_ae (ae_of_all _ he), integral_mul_const]
    rw [hint]
    change ‖((∫ t in (Ioc 0 2) ∩ E, f t : ℝ) : ℂ) • A‖ =
      ∫ t in (Ioc 0 2) ∩ E, ‖modeOutput B.c B.a k i rho hpos t‖
    rw [hnint, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg_of_ae hn)]

end D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure
