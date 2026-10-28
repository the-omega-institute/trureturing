/- GID: D5/S3/Quantum/Recovery/PetzCoreTraceStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzCoreTraceStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual supported Petz core has a trace error controlled by its physical inverse-square-root intertwining error. -/

import D5.S3.Quantum.Recovery.PetzSchwarzRecovery
import D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates

/-! The actual Petz core consumes the common Schwarz/trace supplier and the
physical weighted Parseval and Hilbert-Schmidt-to-trace bridges. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates

namespace D5.S3.Quantum.Recovery.PetzCoreTraceStability

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

/-- The input support projection is retained in the physical amplitude, so its
kernel columns vanish before the Hilbert-Schmidt-to-trace bridge is applied. -/
theorem petz_core_traceNorm_le_four_physical_hs
    (M : SupportedRelativeModularModel Φ ρ σ) :
    traceNorm
      (cfc Real.sqrt M.data.S * M.data.Ψ
        (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
        cfc Real.sqrt M.data.S - M.data.R) ≤
      4 * ‖physicalWeightedError M
        (cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η)‖ := by
  let H := cfc Real.sqrt M.data.S
  let W := spectralInverseSqrt M.data.Q
  let Y := W * cfc Real.sqrt M.data.T
  let C := H * M.data.Ψ Y * spectralSupport M.data.R
  let N := H * M.data.Ψ (W * M.data.T * W) * H
  have hspec : M.data.spectralX
      (cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η) = Y := by
    exact PetzSpectralCoordinates.spectral_petz_coordinate_matrix M.data
  obtain ⟨_, hCN, htrace⟩ := PetzSchwarzRecovery.petz_core_schwarz_and_trace M
  have htrR : M.data.R.trace = 1 := ρ.2.2
  have htrN : N.trace = 1 := htrace.trans htrR
  have hsqrt : CFC.sqrt M.data.R = cfc Real.sqrt M.data.R := by
    rw [CFC.sqrt_eq_real_sqrt _ M.data.hR.nonneg, cfcₙ_eq_cfc]
  have h := traceNorm_sub_le_four_hs_sqrt C M.data.R N M.data.hR htrR htrN hCN
  simpa only [C, N, H, W, Y, hsqrt, physicalWeightedError, hspec] using h

/-- Actual relative-modular spectral weights bound the trace error of the
actual Petz core. The coordinate size is the real Hermitian quadratic form,
with no use of the supremum norm on the underlying coordinate function type. -/
theorem petz_core_traceNorm_le_weighted_inverse_sqrt_error
    (M : SupportedRelativeModularModel Φ ρ σ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L) :
    let x := cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η
    let d := modularCoordinateError M x
    traceNorm
      (cfc Real.sqrt M.data.S * M.data.Ψ
        (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
        cfc Real.sqrt M.data.S - M.data.R) ≤
      4 * Real.sqrt L * Real.sqrt (star d ⬝ᵥ d).re := by
  let x := cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.B *ᵥ M.data.η
  let d := modularCoordinateError M x
  let q := (star d ⬝ᵥ d).re
  change _ ≤ 4 * Real.sqrt L * Real.sqrt q
  have hq : q = ∑ ji, ‖d ji‖ ^ 2 := by
    simpa only [q, Complex.ofReal_one, Matrix.diagonal_one, Matrix.one_mulVec, one_mul]
      using diagonal_quadratic_form (fun _ : M.data.J × M.data.I => (1 : ℝ)) d
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Finset.sum_nonneg (fun ji _ => sq_nonneg ‖d ji‖)
  have hsq : ‖physicalWeightedError M x‖ ^ 2 ≤ L * q := by
    simpa only [hq] using physical_hs_sq_le_coordinate_sq M x L hL
  have hroot : (Real.sqrt L * Real.sqrt q) ^ 2 = L * q := by
    rw [mul_pow, Real.sq_sqrt hL0, Real.sq_sqrt hq0]
  have hhs : ‖physicalWeightedError M x‖ ≤ Real.sqrt L * Real.sqrt q := by
    nlinarith [norm_nonneg (physicalWeightedError M x),
      mul_nonneg (Real.sqrt_nonneg L) (Real.sqrt_nonneg q)]
  calc
    _ ≤ 4 * ‖physicalWeightedError M x‖ := petz_core_traceNorm_le_four_physical_hs M
    _ ≤ 4 * Real.sqrt L * Real.sqrt q := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhs (by norm_num : (0 : ℝ) ≤ 4)

#print axioms petz_core_traceNorm_le_four_physical_hs
#print axioms petz_core_traceNorm_le_weighted_inverse_sqrt_error

end D5.S3.Quantum.Recovery.PetzCoreTraceStability
