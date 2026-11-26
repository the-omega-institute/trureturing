/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Right-hand Bell-kernel limit and padded conditional trace ratio witnesses. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
import D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer

/-! The right-hand positive-trace limit used for the Bell output kernel. -/

set_option autoImplicit false

open Filter Topology Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open RHLinalg (rtrace rtrace_add rtrace_sub trace_mul_nonneg_of_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (posTrace)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (effect_le_posTrace)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open private exists_effect_attaining_posTrace from
  D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper

namespace D5.S3.Quantum.Divergence.ConditionalExpansion

/-- The right derivative of the positive trace at `-B0` in the direction `X0`.
The fixed space of the orthogonal projection `P` is the kernel of `B0`. -/
theorem bell_kernel_limit {n : Type*} [Fintype n] [DecidableEq n]
    {B0 X0 P : Matrix n n ℂ} (hB : B0.PosSemidef) (hX : X0.PosSemidef)
    (hP : IsStarProjection P) (hker : ∀ v : n → ℂ, B0 *ᵥ v = 0 ↔ P *ᵥ v = v) :
    Tendsto (fun ε : ℝ => posTrace (ε • X0 - B0) / ε)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rtrace (P * X0))) := by
  classical
  let R := CFC.sqrt B0
  let W := spectralInverseSqrt B0
  let Q := spectralSupport B0
  have hPP : P * P = P := hP.isIdempotentElem
  have hPh : Pᴴ = P := hP.isSelfAdjoint.star_eq
  obtain ⟨hR, hW, hQ, -, -, -, hQB, -⟩ := spectral_sqrt_normalization B0 hB
  obtain ⟨hRW, hWR, -, -⟩ := spectral_sqrt_inverse_products B0 hB
  change Rᴴ = R at hR
  change Wᴴ = W at hW
  change Qᴴ = Q at hQ
  change Q * B0 = B0 at hQB
  change R * W = Q at hRW
  change W * R = Q at hWR
  have hRR : R * R = B0 := CFC.sqrt_mul_sqrt_self B0 hB.nonneg
  have hBP : B0 * P = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact (hker _).2 (by rw [Matrix.mulVec_mulVec, hPP])
  have hPB : P * B0 = 0 := by
    simpa only [Matrix.conjTranspose_mul, hPh, hB.isHermitian.eq, Matrix.conjTranspose_zero]
      using congrArg Matrix.conjTranspose hBP
  have hRP : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [Matrix.conjTranspose_mul, hR, Matrix.mul_assoc, ← Matrix.mul_assoc R R, hRR,
      hBP, Matrix.mul_zero]
  have hQP : Q * P = 0 := by rw [← hWR, Matrix.mul_assoc, hRP, Matrix.mul_zero]
  have hPQ : P * Q = 0 := by
    simpa only [Matrix.conjTranspose_mul, hPh, hQ, Matrix.conjTranspose_zero]
      using congrArg Matrix.conjTranspose hQP
  have hBQ : B0 * Q = B0 := by
    simpa only [Matrix.conjTranspose_mul, hQ, hB.isHermitian.eq]
      using congrArg Matrix.conjTranspose hQB
  have hsum : P + Q = 1 := by
    have hfix : P * (1 - Q) = 1 - Q := by
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      rw [← Matrix.mulVec_mulVec]
      apply (hker _).1
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hBQ, sub_self,
        Matrix.zero_mulVec]
    rw [Matrix.mul_sub, Matrix.mul_one, hPQ, sub_zero] at hfix
    exact (eq_sub_iff_add_eq).1 hfix
  -- The supported inverse square root bounds the complementary compression.
  let d := ‖W * X0 * W‖
  have hd : 0 ≤ d := norm_nonneg _
  have hWXW : W * X0 * W ≤ d • (1 : Matrix n n ℂ) := by
    have hp : (W * X0 * W).PosSemidef := by
      simpa only [hW] using hX.conjTranspose_mul_mul_same W
    rw [← Algebra.algebraMap_eq_smul_one]
    exact hp.isHermitian.isSelfAdjoint.le_algebraMap_norm_self _
  have hdom : Q * X0 * Q ≤ d • B0 := by
    have h := (Matrix.le_iff.mp hWXW).conjTranspose_mul_mul_same R
    rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hRR] at h
    have hcompress : R * (W * X0 * W) * R = Q * X0 * Q := by
      calc
        _ = (R * W) * X0 * (W * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hRW, hWR]
    rw [hcompress] at h
    exact Matrix.le_iff.mpr h
  let C := P * X0 * P
  have hC : C.PosSemidef := by
    simpa only [C, hPh] using hX.conjTranspose_mul_mul_same P
  have htrC : rtrace C = rtrace (P * X0) := by
    unfold C rtrace
    rw [Matrix.trace_mul_comm (P * X0) P, ← Matrix.mul_assoc, hPP]
  have rtrace_smul (a : ℝ) (A : Matrix n n ℂ) : rtrace (a • A) = a * rtrace A := by
    simp only [rtrace, Matrix.trace_smul, RCLike.smul_re]
  have trace_mono {A D M : Matrix n n ℂ} (hM : M.PosSemidef) (hle : A ≤ D) :
      rtrace (M * A) ≤ rtrace (M * D) := by
    have h : 0 ≤ rtrace (M * (D - A)) :=
      trace_mul_nonneg_of_posSemidef hM (Matrix.le_iff.mp hle)
    rwa [Matrix.mul_sub, rtrace_sub, sub_nonneg] at h
  let c := 2 * d + 1
  have hc : 0 < c := by dsimp [c]; linarith
  have bounds (ε : ℝ) (hε : 0 < ε) (hsmall : ε < c⁻¹) :
      rtrace (P * X0) ≤ posTrace (ε • X0 - B0) / ε ∧
      posTrace (ε • X0 - B0) / ε ≤ (1 + c * ε) * rtrace (P * X0) := by
    let t := c * ε
    have ht : 0 ≤ t := mul_nonneg hc.le hε.le
    have ht₁ : t ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsmall.le hc.le).trans_eq (mul_inv_cancel₀ hc.ne')
    have hY : (ε • X0 - B0).IsHermitian :=
      (hX.isHermitian.smul (IsSelfAdjoint.all ε)).sub hB.isHermitian
    refine ⟨?_, ?_⟩
    · have h := effect_le_posTrace hY hP.nonneg hP.le_one
      have hz : rtrace (0 : Matrix n n ℂ) = 0 := by simp [rtrace]
      rw [Matrix.mul_sub, Matrix.mul_smul, rtrace_sub, rtrace_smul, hPB, hz, sub_zero] at h
      exact (le_div_iff₀ hε).2 (by simpa only [mul_comm] using h)
    · obtain ⟨M, hM, hM₁, hopt⟩ := exists_effect_attaining_posTrace _ hY
      -- Expand the positive square `(tP - Q)ᴴ X0 (tP - Q)`.
      let S := t • P - Q
      have hS : Sᴴ = S := by
        simp only [S, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, hPh, hQ]
      have hcompare : t • X0 ≤ (t + t * t) • C + (1 + t) • (Q * X0 * Q) := by
        apply Matrix.le_iff.mpr
        have hexpand : (t + t * t) • C + (1 + t) • (Q * X0 * Q) - t • X0 = Sᴴ * X0 * S := by
          calc
            _ = (t + t * t) • C + (1 + t) • (Q * X0 * Q) - t • ((P + Q) * X0 * (P + Q)) := by
              rw [hsum, Matrix.one_mul, Matrix.mul_one]
            _ = _ := by
              rw [hS]
              simp only [S, C, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
                Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, add_smul, smul_smul, one_smul]
              abel
        rw [hexpand]
        exact hX.conjTranspose_mul_mul_same S
      have hcap : rtrace (M * C) ≤ rtrace (P * X0) := by
        have h := trace_mono hC hM₁
        rw [Matrix.mul_one, htrC] at h
        unfold rtrace at h ⊢
        rwa [Matrix.trace_mul_comm C M] at h
      have hpen := trace_mono hM.posSemidef hdom
      rw [Matrix.mul_smul, rtrace_smul] at hpen
      have hcoef : (1 + t) * d ≤ c := by
        calc
          _ ≤ 2 * d := mul_le_mul_of_nonneg_right (by linarith) hd
          _ ≤ c := by dsimp [c]; linarith
      have hpen' : (1 + t) * rtrace (M * (Q * X0 * Q)) ≤ c * rtrace (M * B0) := by
        calc
          _ ≤ (1 + t) * (d * rtrace (M * B0)) := mul_le_mul_of_nonneg_left hpen (by positivity)
          _ ≤ _ := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hcoef (trace_mul_nonneg_of_posSemidef hM.posSemidef hB)
      have hscore := trace_mono hM.posSemidef hcompare
      simp only [Matrix.mul_add, Matrix.mul_smul, rtrace_add, rtrace_smul] at hscore
      have hbound := hscore.trans
        (add_le_add (mul_le_mul_of_nonneg_left hcap (show 0 ≤ t + t * t by positivity)) hpen')
      rw [← hopt, Matrix.mul_sub, Matrix.mul_smul, rtrace_sub, rtrace_smul]
      apply (div_le_iff₀ hε).2
      apply le_of_mul_le_mul_left _ hc
      calc
        c * (ε * rtrace (M * X0) - rtrace (M * B0)) =
            t * rtrace (M * X0) - c * rtrace (M * B0) := by dsimp [t]; ring
        _ ≤ (t + t * t) * rtrace (P * X0) := sub_le_iff_le_add.mpr hbound
        _ = c * ((1 + c * ε) * rtrace (P * X0) * ε) := by dsimp [t]; ring
  have hevent : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
      rtrace (P * X0) ≤ posTrace (ε • X0 - B0) / ε ∧
      posTrace (ε • X0 - B0) / ε ≤ (1 + c * ε) * rtrace (P * X0) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (inv_pos.mpr hc))]
      with ε hε hsmall
    exact bounds ε hε hsmall
  have hcont : ContinuousAt (fun ε : ℝ => (1 + c * ε) * rtrace (P * X0)) 0 := by fun_prop
  have hu : Tendsto (fun ε : ℝ => (1 + c * ε) * rtrace (P * X0))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rtrace (P * X0))) := by
    simpa only [ContinuousWithinAt, mul_zero, add_zero, one_mul] using
      hcont.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (hevent.mono fun _ h => h.1) (hevent.mono fun _ h => h.2)

open BellCenteredConditionalTraceGap (bellProjector bell_padded_gap)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (amp gap)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open UnitaryReconstruction.LiuWildChoiObstruction (bell bell_norm outer pairMatrix)

/-- The conditional trace-distance ratio of an orthogonal density pair on `Option A`
can be at most the Bell output's weight in the kernel of the complementary output,
up to any positive tolerance. -/
theorem exists_bell_kernel_ratio_le {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (hd : 2 ≤ Fintype.card A)
    (η : ℝ) (hη : 0 < η) :
    let P := bellProjector A
    let B₀ := amp N (1 - P)
    let Pker := 1 - spectralSupport B₀
    ∃ ρ σ : DensityState (Option A × A),
      pairMatrix ρ * pairMatrix σ = 0 ∧
      0 < gap 1 (pairMatrix ρ) (pairMatrix σ) ∧
      gap 1 (amp N (pairMatrix ρ)) (amp N (pairMatrix σ)) /
          gap 1 (pairMatrix ρ) (pairMatrix σ) ≤ rtrace (Pker * amp N P) + η := by
  intro P B₀ Pker
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let X₀ := amp N P
  have hP : IsStarProjection P := by
    refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
    · change outer (bell A) * outer (bell A) = outer (bell A)
      rw [Matrix.vecMulVec_mul_vecMulVec, show star (bell A) ⬝ᵥ bell A = 1 from bell_norm,
        one_smul]
    · change (outer (bell A))ᴴ = outer (bell A)
      simp only [Matrix.conjTranspose_vecMulVec, star_star]
  have hB : B₀.PosSemidef := amp_psd N hP.one_sub.nonneg.posSemidef
  have hX : X₀.PosSemidef := amp_psd N hP.nonneg.posSemidef
  let S := spectralSupport B₀
  obtain ⟨hRadj, -, hSadj, hSidem, -, -, hSB, -⟩ := spectral_sqrt_normalization B₀ hB
  obtain ⟨-, hWR, -, -⟩ := spectral_sqrt_inverse_products B₀ hB
  have hS : IsStarProjection S := isStarProjection_iff'.mpr ⟨hSidem, hSadj⟩
  have hBS : B₀ * S = B₀ := by
    simpa only [Matrix.conjTranspose_mul, hSadj, hB.isHermitian.eq]
      using congrArg Matrix.conjTranspose hSB
  have hBker : B₀ * Pker = 0 := by
    change B₀ * (1 - S) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, hBS, sub_self]
  have hker (v : A × B → ℂ) : B₀ *ᵥ v = 0 ↔ Pker *ᵥ v = v := by
    constructor
    · intro hv
      have hRv : CFC.sqrt B₀ *ᵥ v = 0 := by
        apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt B₀) v).mp
        rw [hRadj, CFC.sqrt_mul_sqrt_self B₀ hB.nonneg]
        exact hv
      have hSv : S *ᵥ v = 0 := by
        change spectralSupport B₀ *ᵥ v = 0
        rw [← hWR, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_zero]
      change (1 - S) *ᵥ v = v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hSv, sub_zero]
    · intro hv
      rw [← hv, Matrix.mulVec_mulVec, hBker, Matrix.zero_mulVec]
  have hlim := bell_kernel_limit hB hX (show IsStarProjection Pker from hS.one_sub) hker
  let D : ℝ := (Fintype.card A : ℝ) ^ 2 - 1
  have hd' : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  have hD : 0 < D := by
    dsimp [D]
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hd' 2
    linarith
  have hη' : rtrace (Pker * X₀) < rtrace (Pker * X₀) + η := lt_add_of_pos_right _ hη
  have hclose : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
      posTrace (ε • X₀ - B₀) / ε < rtrace (Pker * X₀) + η :=
    hlim (Iio_mem_nhds hη')
  have hev : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
      0 < ε ∧ ε < D ∧ posTrace (ε • X₀ - B₀) / ε < rtrace (Pker * X₀) + η := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hD), hclose]
      with ε hε hεD h
    exact ⟨hε, hεD, h⟩
  obtain ⟨ε, hε, hεD, hbound⟩ := hev.exists
  let a : A := Classical.choice inferInstance
  let ω : DensityState A := pureState (Pi.single a 1) (by simp [dotProduct, Pi.single_apply])
  obtain ⟨-, hρ, hρt, hσ, hσt, horth, -, -, hgap, -, hratio, -, -⟩ :=
    bell_padded_gap N ω ε hε hεD.le
  refine ⟨⟨CStarMatrix.ofMatrix _, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hρ.nonneg, hρt⟩,
    ⟨CStarMatrix.ofMatrix _, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hσ.nonneg, hσt⟩,
    horth, hgap, hratio.trans_le hbound.le⟩

#print axioms bell_kernel_limit
#print axioms exists_bell_kernel_ratio_le

end D5.S3.Quantum.Divergence.ConditionalExpansion
