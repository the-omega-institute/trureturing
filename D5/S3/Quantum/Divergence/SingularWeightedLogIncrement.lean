/- GID: D5/S3/Quantum/Divergence/SingularWeightedLogIncrement
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SingularWeightedLogIncrement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A supported weighted matrix log increment vanishes exactly at zero overlap. -/

import D5.S3.Divergence.AudenaertBinaryHolevoBound
import D5.S3.Quantum.Divergence.UmegakiSupportedNoise
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition

/-! The fixed resolvent tail controls strictness uniformly in the positive shift.

proof_shape: content
admission_basis: escape-witness
escape_witness: the sandwiched weighted resolvent difference vanishes at a positive
shift exactly when the unshifted reference annihilates the positive perturbation. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.SingularWeightedLogIncrement

open _root_.Matrix Filter MeasureTheory Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.AudenaertBinaryHolevoBound (matrix_log_resolvent_integral)
open D5.S3.Quantum.Divergence.UmegakiSupportedNoise (supported_log_shift_tendsto)
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity (zero_trace_mul_eq_zero)
open D5.S3.Quantum.Tomography.PurityPythagorasDecomposition (trace_mul_real_of_hermitian)

variable {n : ℕ}

private lemma resolvent_pairing {A C R : Matrix (Fin n) (Fin n) ℂ}
    {u v s : ℝ} (hC : C.PosSemidef) (hR : R.PosSemidef)
    (hu : 0 < u) (hl : u • C ≤ A) (hh : A ≤ v • C) (hs : 0 < s) :
    let D := (C + s • 1)⁻¹ - (C + R + s • 1)⁻¹
    0 ≤ (A * D).trace.re ∧ ((A * D).trace.re = 0 ↔ C * R = 0) := by
  let X := C + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let Y := C + R + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let D := X⁻¹ - Y⁻¹
  change 0 ≤ (A * D).trace.re ∧ ((A * D).trace.re = 0 ↔ C * R = 0)
  have hX : X.PosDef := Matrix.PosDef.posSemidef_add hC (Matrix.PosDef.one.smul hs)
  have hY : Y.PosDef := Matrix.PosDef.posSemidef_add (hC.add hR) (Matrix.PosDef.one.smul hs)
  have hXY : X ≤ Y := add_le_add_left (le_add_of_nonneg_right hR.nonneg) _
  have hD : D.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply sub_nonneg.mpr
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      CStarAlgebra.ringInverse_le_ringInverse hXY hX.isStrictlyPositive
  have hx := (Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit
  have hy := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  have hdiff : Y - X = R := by
    dsimp [Y, X]
    abel
  have hres : D = Y⁻¹ * R * X⁻¹ := by
    rw [← hdiff, mul_sub, sub_mul, Y.nonsing_inv_mul hy, one_mul,
      mul_assoc, X.mul_nonsing_inv hx, mul_one]
  have hcomm : X⁻¹ * C = C * X⁻¹ := by
    have hc : C = X - s • 1 := by simp [X]
    calc
      X⁻¹ * C = X⁻¹ * (X - s • 1) := congrArg (X⁻¹ * ·) hc
      _ = (X - s • 1) * X⁻¹ := by
        rw [mul_sub, sub_mul, X.nonsing_inv_mul hx, X.mul_nonsing_inv hx,
          Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
      _ = C * X⁻¹ := congrArg (· * X⁻¹) hc.symm
  have hDC : D * C = Y⁻¹ * (R * C) * X⁻¹ := by
    rw [hres, mul_assoc (Y⁻¹ * R), hcomm]
    simp only [mul_assoc]
  have hkill : D * C = 0 ↔ C * R = 0 := by
    have hstar (P Q : Matrix (Fin n) (Fin n) ℂ)
        (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hpq : P * Q = 0) : Q * P = 0 := by
      simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero]
        using congrArg Matrix.conjTranspose hpq
    constructor
    · intro h
      have hcancel := congrArg (fun M => Y * M * X) h
      change Y * (D * C) * X = Y * 0 * X at hcancel
      rw [hDC, ← mul_assoc Y, Y.mul_nonsing_inv_cancel_left _ hy,
        X.nonsing_inv_mul_cancel_right _ hx, mul_zero, zero_mul] at hcancel
      exact hstar R C hR.isHermitian hC.isHermitian hcancel
    · intro h
      rw [hDC, hstar C R hC.isHermitian hR.isHermitian h, mul_zero, zero_mul]
  have hnonneg : 0 ≤ (C * D).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hC hD
  have hzero : (C * D).trace.re = 0 ↔ C * R = 0 := by
    rw [Matrix.trace_mul_comm, ← hkill]
    refine ⟨fun h => zero_trace_mul_eq_zero D C hD hC ?_, fun h => by simp [h]⟩
    rw [trace_mul_real_of_hermitian D C hD.isHermitian hC.isHermitian, h, Complex.ofReal_zero]
  have hmono {P Q : Matrix (Fin n) (Fin n) ℂ} (h : P ≤ Q) :
      (P * D).trace.re ≤ (Q * D).trace.re := by
    have hp := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp h) hD
    change 0 ≤ ((Q - P) * D).trace.re at hp
    simpa only [sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hp
  have hlow : u * (C * D).trace.re ≤ (A * D).trace.re := by
    simpa only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] using hmono hl
  have hhigh : (A * D).trace.re ≤ v * (C * D).trace.re := by
    simpa only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] using hmono hh
  have ha := (mul_nonneg hu.le hnonneg).trans hlow
  refine ⟨ha, ?_⟩
  constructor
  · intro hz
    have hnonpos : u * (C * D).trace.re ≤ 0 := hz ▸ hlow
    exact hzero.mp (le_antisymm (nonpos_of_mul_nonpos_right hnonpos hu) hnonneg)
  · intro hz
    rw [hzero.mpr hz, mul_zero] at hhigh
    exact le_antisymm hhigh ha

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma shifted_gap_integral (A C B : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.PosSemidef) (hB : B.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    let f := fun s : ℝ => (A * ((C + s • 1)⁻¹ - (B + s • 1)⁻¹)).trace.re
    IntegrableOn f (Ioi δ) ∧
      (A * (CFC.log (B + δ • 1) - CFC.log (C + δ • 1))).trace.re =
        ∫ s in Ioi δ, f s := by
  let f := fun s : ℝ => (A * ((C + s • 1)⁻¹ - (B + s • 1)⁻¹)).trace.re
  let K (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
    (1 + t)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) - (M + t • 1)⁻¹
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (((Matrix.traceLinearMap (Fin n) ℝ ℂ).comp
      (LinearMap.mulLeft ℝ A)).toContinuousLinearMap)
  have hL (M : Matrix (Fin n) (Fin n) ℂ) : L M = (A * M).trace.re := rfl
  let Bδ := B + δ • (1 : Matrix (Fin n) (Fin n) ℂ)
  let Cδ := C + δ • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hKB := matrix_log_resolvent_integral Bδ
    (Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hδ))
  have hKC := matrix_log_resolvent_integral Cδ
    (Matrix.PosDef.posSemidef_add hC (Matrix.PosDef.one.smul hδ))
  change IntegrableOn (K Bδ) (Ioi 0) ∧ (∫ t in Ioi 0, K Bδ t) = CFC.log Bδ at hKB
  change IntegrableOn (K Cδ) (Ioi 0) ∧ (∫ t in Ioi 0, K Cδ t) = CFC.log Cδ at hKC
  have hInt := hKB.1.sub hKC.1
  let shift := Homeomorph.addRight δ
  have hshift : MeasurePreserving shift volume volume := measurePreserving_add_right volume δ
  have hpre : shift ⁻¹' Ioi δ = Ioi 0 := by
    ext t
    change δ < t + δ ↔ 0 < t
    simp
  have hkernel : (fun t => L (K Bδ t - K Cδ t)) = f ∘ shift := by
    funext t
    rw [hL]
    change (A * (K Bδ t - K Cδ t)).trace.re = f (t + δ)
    have hcancel {M N P : Matrix (Fin n) (Fin n) ℂ} : (M - N) - (M - P) = P - N := by
      abel
    simp only [K, hcancel, f, Bδ, Cδ, add_assoc, ← add_smul, add_comm δ t]
  have hcomp := L.integrable_comp hInt
  change IntegrableOn (fun t => L (K Bδ t - K Cδ t)) (Ioi 0) at hcomp
  rw [hkernel] at hcomp
  refine ⟨(hshift.integrableOn_comp_preimage shift.measurableEmbedding).mp
    (hpre.symm ▸ hcomp), ?_⟩
  change (A * (CFC.log Bδ - CFC.log Cδ)).trace.re = _
  calc
    _ = L (∫ t in Ioi 0, K Bδ t - K Cδ t) := by
      rw [integral_sub hKB.1 hKC.1, hKB.2, hKC.2, hL]
    _ = ∫ t in Ioi 0, L (K Bδ t - K Cδ t) := (L.integral_comp_comm hInt).symm
    _ = ∫ s in Ioi δ, f s := by
      rw [← hshift.setIntegral_preimage_emb shift.measurableEmbedding f (Ioi δ), hpre]
      exact congrArg (fun g : ℝ → ℝ => ∫ t in Ioi 0, g t) hkernel

/-- The weighted log increment at a possibly singular reference is nonnegative,
with equality precisely when the reference annihilates the perturbation. -/
theorem weighted_log_increment_nonneg_and_eq_zero_iff
    {A C ρ : Matrix (Fin n) (Fin n) ℂ} {u v e : ℝ}
    (hC : C.PosSemidef) (hρ : ρ.PosSemidef) (hu : 0 < u) (huv : u ≤ v) (he : 0 < e)
    (hl : u • C ≤ A) (hh : A ≤ v • C) :
    0 ≤ (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ∧
      ((A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re = 0 ↔ C * ρ = 0) := by
  let R := e • ρ
  let B := C + R
  have hR : R.PosSemidef := hρ.smul he.le
  have hB : B.PosSemidef := hC.add hR
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp ((hC.smul hu.le).nonneg.trans hl)
  have hCB : C ≤ B := le_add_of_nonneg_right hR.nonneg
  let AH : HermitianMat (Fin n) ℂ := ⟨A, hA.isHermitian⟩
  let CH : HermitianMat (Fin n) ℂ := ⟨C, hC.isHermitian⟩
  let BH : HermitianMat (Fin n) ℂ := ⟨B, hB.isHermitian⟩
  have hCA : CH.ker ≤ AH.ker :=
    HermitianMat.ker_le_of_le_smul (hu.trans_le huv).ne' (HermitianMat.zero_le_iff.mpr hA) hh
  have hBC : BH.ker ≤ CH.ker :=
    HermitianMat.ker_antitone (HermitianMat.zero_le_iff.mpr hC) hCB
  have hsC (x : Fin n → ℂ) (hx : C *ᵥ x = 0) : A *ᵥ x = 0 := by
    exact (HermitianMat.mem_ker_iff_mulVec_zero AH (WithLp.toLp 2 x)).mp
      (hCA ((HermitianMat.mem_ker_iff_mulVec_zero CH (WithLp.toLp 2 x)).mpr hx))
  have hsB (x : Fin n → ℂ) (hx : B *ᵥ x = 0) : A *ᵥ x = 0 := by
    exact (HermitianMat.mem_ker_iff_mulVec_zero AH (WithLp.toLp 2 x)).mp
      (hCA (hBC ((HermitianMat.mem_ker_iff_mulVec_zero BH (WithLp.toLp 2 x)).mpr hx)))
  let gap (δ : ℝ) := (A * (CFC.log (B + δ • 1) - CFC.log (C + δ • 1))).trace.re
  let Δ := (A * (CFC.log B - CFC.log C)).trace.re
  have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hlim : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 Δ) := by
    simpa only [gap, Δ, Matrix.mul_sub, Function.comp_def] using
      hcont.continuousAt.tendsto.comp
        ((supported_log_shift_tendsto hB hsB).sub (supported_log_shift_tendsto hC hsC))
  let f (s : ℝ) := (A * ((C + s • 1)⁻¹ - (B + s • 1)⁻¹)).trace.re
  have hf (s : ℝ) (hs : 0 < s) : 0 ≤ f s ∧ (f s = 0 ↔ C * ρ = 0) := by
    simpa only [f, B, R, Matrix.mul_smul, smul_eq_zero, he.ne', false_or] using
      resolvent_pairing hC hR hu hl hh hs
  have hrep (δ : ℝ) (hδ : 0 < δ) :
      IntegrableOn f (Ioi δ) ∧ gap δ = ∫ s in Ioi δ, f s :=
    shifted_gap_integral A C B hC hB hδ
  have hnonneg (δ : ℝ) (hδ : 0 < δ) : 0 ≤ᵐ[volume.restrict (Ioi δ)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hf s (hδ.trans hs)).1
  have hEventually : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with δ hδ hδ1
    exact ⟨hδ, hδ1.le⟩
  change 0 ≤ Δ ∧ (Δ = 0 ↔ C * ρ = 0)
  by_cases hzero : C * ρ = 0
  · have heq : Δ = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      filter_upwards [hEventually] with δ hδ
      rw [(hrep δ hδ.1).2]
      rw [← integral_zero ℝ ℝ (μ := volume.restrict (Ioi δ))] at ⊢
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact ((hf s (hδ.1.trans hs)).2.mpr hzero).symm
    exact ⟨heq.ge, iff_of_true heq hzero⟩
  · have htail : 0 < ∫ s in Ioi (1 : ℝ), f s := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae (hnonneg 1 zero_lt_one)
        (hrep 1 zero_lt_one).1).mpr ?_
      have hsupp : Function.support f ∩ Ioi (1 : ℝ) = Ioi 1 := by
        apply inter_eq_right.mpr
        intro s hs
        exact fun hz => hzero ((hf s (zero_lt_one.trans hs)).2.mp hz)
      rw [hsupp, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    have hbound : (∫ s in Ioi (1 : ℝ), f s) ≤ Δ := by
      apply ge_of_tendsto hlim
      filter_upwards [hEventually] with δ hδ
      rw [(hrep δ hδ.1).2]
      exact setIntegral_mono_set (hrep δ hδ.1).1 (hnonneg δ hδ.1)
        (Filter.Eventually.of_forall (Ioi_subset_Ioi hδ.2))
    exact ⟨(htail.trans_le hbound).le, iff_of_false (htail.trans_le hbound).ne' hzero⟩

end D5.S3.Quantum.Divergence.SingularWeightedLogIncrement
