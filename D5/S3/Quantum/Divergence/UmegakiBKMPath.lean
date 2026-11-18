/- GID: D5/S3/Quantum/Divergence/UmegakiBKMPath
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiBKMPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommuting Umegaki divergence as the integrated BKM form. -/

import D5.S3.Divergence.AudenaertBinaryHolevoBound
import D5.S3.Quantum.Divergence.TraceEntropyCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The logarithmic derivative and trace-entropy derivative are reused at their
original declarations. The new analytic step is dominated continuity of the
resolvent derivative on a common positive floor, then scalar FTC and integration
by parts. No simultaneous diagonalization or Hessian premise is imposed.
proof_shape: content; admission_basis: escape-witness.
escape_witness: continuousOn_logDeriv_of_floor, consumed by relativeEntropy_eq_integral_bkm
and conditional_relativeEntropy_eq_integral_bkm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Divergence.AudenaertBinaryHolevoBound
open D5.S3.Quantum.Divergence.TraceEntropyCalculus

namespace D5.S3.Quantum.Divergence.UmegakiBKMPath

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
lemma common_floor {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ A ∧
      c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B := by
  cases isEmpty_or_nonempty (Fin n) with
  | inl hi =>
    have := hi
    exact ⟨1, zero_lt_one, le_of_eq (Subsingleton.elim _ _),
      le_of_eq (Subsingleton.elim _ _)⟩
  | inr hi =>
    have := hi
    obtain ⟨a, ha, haA⟩ := (CFC.exists_pos_algebraMap_le_iff A).mpr
      (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
    obtain ⟨b, hb, hbB⟩ := (CFC.exists_pos_algebraMap_le_iff B).mpr
      (fun x hx => hB.isStrictlyPositive.spectrum_pos hx)
    refine ⟨min a b, lt_min ha hb, ?_, ?_⟩
    · simpa only [Algebra.algebraMap_eq_smul_one] using
        (algebraMap_mono (Matrix (Fin n) (Fin n) ℂ) (min_le_left a b)).trans haA
    · simpa only [Algebra.algebraMap_eq_smul_one] using
        (algebraMap_mono (Matrix (Fin n) (Fin n) ℂ) (min_le_right a b)).trans hbB

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
theorem continuousOn_logDeriv_of_floor {n : ℕ}
    (B H : Matrix (Fin n) (Fin n) ℂ) (s : Set ℝ) (c : ℝ) (hc : 0 < c)
    (hfloor : ∀ t ∈ s, c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B + t • H) :
    ContinuousOn (fun t : ℝ => logDeriv (B + t • H) H) s := by
  let Z : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => B + t • H
  let K : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ := fun t u =>
    (Z t + u • 1)⁻¹ * H * (Z t + u • 1)⁻¹
  have hp (t : ℝ) (ht : t ∈ s) : (Z t).PosDef :=
    ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le (hfloor t ht)).posDef
  have hbound (t : ℝ) (ht : t ∈ s) :
      ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖K t u‖ ≤ ‖H‖ / (c + u)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hR := inverse_shift_norm_bound (Z t) c u hc hu.le (hfloor t ht)
    have hnon : 0 ≤ (c + u)⁻¹ := inv_nonneg.mpr (add_pos hc hu).le
    calc
      ‖K t u‖ ≤ (‖(Z t + u • 1)⁻¹‖ * ‖H‖) * ‖(Z t + u • 1)⁻¹‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((c + u)⁻¹ * ‖H‖) * (c + u)⁻¹ := mul_le_mul
        (mul_le_mul_of_nonneg_right hR (norm_nonneg H)) hR (norm_nonneg _)
          (mul_nonneg hnon (norm_nonneg H))
      _ = ‖H‖ / (c + u)^2 := by field_simp [(add_pos hc hu).ne']
  have hmajor : Integrable (fun u : ℝ => ‖H‖ / (c + u)^2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hh := ((scalarKernel_integrable c hc).div_const c).const_mul ‖H‖
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    field_simp [hc.ne']
  have hcont : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousOn (fun t => K t u) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro t ht
    have hshift : (B + t • H + u • 1).PosDef :=
      (hp t ht).add_posSemidef (Matrix.nonneg_iff_posSemidef.mp
        (smul_nonneg hu.le (zero_le_one : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1)))
    have hR := (shifted_inverse_hasDerivAt B H t u hshift.isUnit).continuousAt
    exact ((hR.mul continuousAt_const).mul hR).continuousWithinAt
  exact continuousOn_of_dominated
    (fun t ht => (logDeriv_integrable (Z t) H (hp t ht)).aestronglyMeasurable)
    hbound hmajor hcont

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The actual Umegaki expression, with its unequal-trace correction, is the
weighted integral of the actual noncommuting logarithmic resolvent form. -/
theorem relativeEntropy_eq_integral_bkm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    (A * (CFC.log A - CFC.log B)).trace.re - (A - B).trace.re =
      ∫ t in (0 : ℝ)..1, (1 - t) *
        ((A - B) * logDeriv (B + t • (A - B)) (A - B)).trace.re := by
  let H := A - B
  let Z : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => B + t • H
  let T : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    T.comp (mulLeftLinearMap (Fin n) ℝ H).toContinuousLinearMap
  let F : ℝ → ℝ := fun t => (Z t * CFC.log (Z t)).trace.re
  let G : ℝ → ℝ := fun t => (H * (CFC.log (Z t) + 1)).trace.re
  let Q : ℝ → ℝ := fun t => (H * logDeriv (Z t) H).trace.re
  obtain ⟨c, hc, hcA, hcB⟩ := common_floor A B hA hB
  have hZeq (t : ℝ) : Z t = t • A + (1 - t) • B := by dsimp [Z, H]; module
  have hfloor (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ Z t := by
    rw [hZeq]
    exact mix_lower_bound A B c t hcA hcB ht
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (Z t).PosDef :=
    ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le (hfloor t ht)).posDef
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hlog : ContinuousOn (fun t => CFC.log (Z t)) (Set.Icc (0 : ℝ) 1) :=
    CFC.continuousOn_log.comp hZ.continuousOn
      (fun t ht => ⟨(hp t ht).isHermitian, (hp t ht).isUnit⟩)
  have hF : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    T.continuous.comp_continuousOn (hZ.continuousOn.mul hlog)
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    exact T.continuous.comp_continuousOn (continuousOn_const.mul (hlog.add continuousOn_const))
  have hQ : ContinuousOn Q (Set.Icc (0 : ℝ) 1) :=
    L.continuous.comp_continuousOn
      (continuousOn_logDeriv_of_floor B H _ c hc hfloor)
  have hFd (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt F (G t) t := by
    have hd : HasDerivAt Z H t := by
      simpa [Z] using ((hasDerivAt_id t).smul_const H).const_add B
    exact hasDerivAt_trace_mul_log Z H t hd
      (Eventually.of_forall fun u => hB.isHermitian.add
        ((hA.isHermitian.sub hB.isHermitian).smul (isSelfAdjoint_iff.mpr (by simp))))
      (hp t ⟨ht.1.le, ht.2.le⟩)
  have hGd (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt G (Q t) t := by
    have hd := log_hasDerivAt_affine_of_lower_bound B H t c hc (Set.Ioo (0 : ℝ) 1)
      (isOpen_Ioo.mem_nhds ht) (fun u hu => hfloor u ⟨hu.1.le, hu.2.le⟩)
    convert! L.hasFDerivAt.comp_hasDerivAt t (hd.add_const 1) using 1
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF hFd
    (by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le zero_le_one] using hG)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (u := fun t : ℝ => 1 - t) (u' := fun _ => (-1 : ℝ))
    (v := G) (v' := Q)
    (by fun_prop) (by simpa only [Set.uIcc_of_le zero_le_one] using hG)
    (fun t _ => by simpa using (hasDerivAt_id t).const_sub 1)
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hGd)
    (by simp) (by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le zero_le_one] using hQ)
  simp only [sub_self, zero_mul, sub_zero, one_mul, neg_one_mul,
    intervalIntegral.integral_neg, hFT] at hIBP
  change _ = ∫ t in (0 : ℝ)..1, (1 - t) * Q t
  rw [hIBP]
  simp only [F, G, Z, H, zero_smul, one_smul, add_zero, add_sub_cancel,
    Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
  ring

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma weighted_bkm_integrable {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) :
    IntervalIntegrable (fun t : ℝ => (1 - t) *
      ((A - B) * logDeriv (B + t • (A - B)) (A - B)).trace.re) volume 0 1 := by
  obtain ⟨c, hc, hcA, hcB⟩ := common_floor A B hA hB
  have hfloor (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B + t • (A - B) := by
    have he : B + t • (A - B) = t • A + (1 - t) • B := by module
    rw [he]
    exact mix_lower_bound A B c t hcA hcB ht
  have hd := continuousOn_logDeriv_of_floor B (A - B) _ c hc hfloor
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap (Fin n) ℝ (A - B)).toContinuousLinearMap)
  have hh : ContinuousOn (fun t : ℝ => (1 - t) *
      ((A - B) * logDeriv (B + t • (A - B)) (A - B)).trace.re)
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).continuousOn.mul
      (L.continuous.comp_continuousOn hd)
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le zero_le_one] using hh

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- Conditional Umegaki divergence for a nonempty finite family of arbitrary
positive definite quantum reference blocks. No commutation or normalization is
required; all unequal-trace corrections cancel between blocks and totals. -/
theorem conditional_relativeEntropy_eq_integral_bkm {n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (A B : ι → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef) :
    (∑ i, (A i * (CFC.log (A i) - CFC.log (B i))).trace.re) -
        ((∑ i, A i) * (CFC.log (∑ i, A i) - CFC.log (∑ i, B i))).trace.re =
      ∫ t in (0 : ℝ)..1, (1 - t) *
        ((∑ i, ((A i - B i) *
            logDeriv (B i + t • (A i - B i)) (A i - B i)).trace.re) -
          (((∑ i, A i) - ∑ i, B i) *
            logDeriv ((∑ i, B i) + t • ((∑ i, A i) - ∑ i, B i))
              ((∑ i, A i) - ∑ i, B i)).trace.re) := by
  classical
  let AR := ∑ i, A i
  let BR := ∑ i, B i
  let q : ι → ℝ → ℝ := fun i t => (1 - t) *
    ((A i - B i) * logDeriv (B i + t • (A i - B i)) (A i - B i)).trace.re
  let qr : ℝ → ℝ := fun t => (1 - t) *
    ((AR - BR) * logDeriv (BR + t • (AR - BR)) (AR - BR)).trace.re
  have hAR : AR.PosDef := Matrix.posDef_sum Finset.univ_nonempty (fun i _ => hA i)
  have hBR : BR.PosDef := Matrix.posDef_sum Finset.univ_nonempty (fun i _ => hB i)
  have hi (i : ι) : IntervalIntegrable (q i) volume 0 1 :=
    weighted_bkm_integrable (A i) (B i) (hA i) (hB i)
  have hr : IntervalIntegrable qr volume 0 1 := weighted_bkm_integrable AR BR hAR hBR
  have hs : IntervalIntegrable (fun t => ∑ i, q i t) volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
    ext t
    simp
  have he : (∫ t in (0 : ℝ)..1, (∑ i, q i t) - qr t) =
      (∑ i, ∫ t in (0 : ℝ)..1, q i t) - ∫ t in (0 : ℝ)..1, qr t := by
    rw [intervalIntegral.integral_sub hs hr,
      intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  have htrace : (∑ i, (A i - B i).trace.re) = (AR - BR).trace.re := by
    simp [AR, BR, Matrix.trace_sub, Matrix.trace_sum, Complex.sub_re,
      Complex.re_sum, Finset.sum_sub_distrib]
  have hsval : (∑ i, ∫ t in (0 : ℝ)..1, q i t) =
      (∑ i, (A i * (CFC.log (A i) - CFC.log (B i))).trace.re) -
        ∑ i, (A i - B i).trace.re := by
    simp only [q, ← relativeEntropy_eq_integral_bkm _ _ (hA _) (hB _),
      Finset.sum_sub_distrib]
  have hrval := relativeEntropy_eq_integral_bkm AR BR hAR hBR
  change _ = ∫ t in (0 : ℝ)..1, (1 - t) * _
  calc
    _ = (∑ i, ∫ t in (0 : ℝ)..1, q i t) - ∫ t in (0 : ℝ)..1, qr t := by
      rw [hsval, ← hrval, htrace]
      ring
    _ = ∫ t in (0 : ℝ)..1, (∑ i, q i t) - qr t := he.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [q, qr, AR, BR, mul_sub, Finset.mul_sum]

end D5.S3.Quantum.Divergence.UmegakiBKMPath
