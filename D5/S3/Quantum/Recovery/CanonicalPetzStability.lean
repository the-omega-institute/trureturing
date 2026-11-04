/- GID: D5/S3/Quantum/Recovery/CanonicalPetzStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CanonicalPetzStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supported entropy loss bounds the trace error of a fixed completed Petz recovery channel. -/

import D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import D5.S3.Quantum.Recovery.PetzCoreTraceStability

/-! Quantitative trace stability for the same fixed completed Petz channel. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery

namespace D5.S3.Quantum.Recovery.CanonicalPetzStability

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

/-- A single completed reference Petz channel controls the actual trace error
by the fourth root of entropy loss, with explicit supported spectral constants. -/
theorem supported_entropy_defect_fixed_petz_trace_stability
    (Φ : QuantumChannel a b) (σ : DensityState a) :
    let K := (actual_kraus_representation Φ).kraus
    let H := cfc Real.sqrt (CStarMatrix.ofMatrix.symm σ.1)
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • CStarMatrix.ofMatrix.symm σ.1) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ (ρ : DensityState a) (support : SupportContained ρ σ),
        let M := supported_relative_modular_model Φ ρ σ support
        ∀ (m L : ℝ), 0 < m → 0 ≤ L →
          m • (1 : Matrix (M.data.J × M.data.I) (M.data.J × M.data.I) ℂ) ≤ M.data.A →
          m • (1 : Matrix (M.data.L × M.data.K) (M.data.L × M.data.K) ℂ) ≤ M.data.B →
          (∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L) →
          traceNorm (CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 -
            CStarMatrix.ofMatrix.symm ρ.1) ≤
            (16 / Real.pi) * Real.sqrt (L / m) *
              (finiteTraceLogRelativeEntropy ρ σ -
                finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^
                  (1 / 4 : ℝ) := by
  classical
  dsimp only
  obtain ⟨recovery, haction, hreference, _⟩ :=
    CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery Φ σ
  refine ⟨recovery, haction, hreference, ?_⟩
  intro ρ support
  let M := supported_relative_modular_model Φ ρ σ support
  intro m L hm hL0 hAm hBm hL
  let d := cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.A *ᵥ M.data.ξ -
    M.data.V *ᵥ (cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η)
  let Δ := finiteTraceLogRelativeEntropy ρ σ -
    finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
  let N := cfc Real.sqrt M.data.S * M.data.Ψ
    (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
      cfc Real.sqrt M.data.S
  have hL2 : Real.sqrt (star d ⬝ᵥ d).re ≤
      4 / (Real.pi * Real.sqrt m) * Δ ^ (1 / 4 : ℝ) := by
    simpa only [M, d, Δ] using
      entropy_defect_inverse_sqrt_stability Φ ρ σ support m hm hAm hBm
  have hcore : traceNorm (N - M.data.R) ≤
      4 * Real.sqrt L * Real.sqrt (star d ⬝ᵥ d).re := by
    simpa only [N, d] using
      PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error M L hL0 hL
  have hsum : (∑ c,
      cfc Real.sqrt M.data.S * ((actual_kraus_representation Φ).kraus c)ᴴ *
        spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q *
        (actual_kraus_representation Φ).kraus c * cfc Real.sqrt M.data.S) = N := by
    dsimp only [N]
    simp only [SupportedRelativeModularData.Ψ, M.kraus_eq,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  have hcomplement : Matrix.trace ((1 - spectralSupport M.data.Q) * M.data.T) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      PetzSchwarzRecovery.petz_output_support_projection M, sub_self, Matrix.trace_zero]
  have hrecover := haction M.data.T
  change CStarMatrix.ofMatrix.symm
    (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix M.data.T)) =
    (∑ c, cfc Real.sqrt M.data.S * ((actual_kraus_representation Φ).kraus c)ᴴ *
      spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q *
      (actual_kraus_representation Φ).kraus c * cfc Real.sqrt M.data.S) +
      Matrix.trace ((1 - spectralSupport M.data.Q) * M.data.T) • M.data.S at hrecover
  rw [hcomplement, zero_smul, add_zero, hsum] at hrecover
  have hmap : CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 = N :=
    hrecover
  change traceNorm (CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 -
    M.data.R) ≤ (16 / Real.pi) * Real.sqrt (L / m) * Δ ^ (1 / 4 : ℝ)
  rw [hmap]
  calc
    traceNorm (N - M.data.R) ≤ 4 * Real.sqrt L * Real.sqrt (star d ⬝ᵥ d).re := hcore
    _ ≤ 4 * Real.sqrt L *
        (4 / (Real.pi * Real.sqrt m) * Δ ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = (16 / Real.pi) * Real.sqrt (L / m) * Δ ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_div hL0]
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr hm).ne']
      <;> ring

#print axioms supported_entropy_defect_fixed_petz_trace_stability

end D5.S3.Quantum.Recovery.CanonicalPetzStability
