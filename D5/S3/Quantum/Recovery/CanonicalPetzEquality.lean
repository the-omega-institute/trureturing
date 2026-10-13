/- GID: D5/S3/Quantum/Recovery/CanonicalPetzEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CanonicalPetzEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality of supported quantum relative entropy yields actual fixed-reference Petz recovery. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Divergence.LogEqualityResolventRigidity
import D5.S3.Quantum.Recovery.ReferencePetzChannel

noncomputable section
universe u v
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.LogEqualityResolventRigidity

namespace D5.S3.Quantum.Recovery.CanonicalPetzEquality

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

/-- The equality hypothesis is the actual canonical finite entropy, and all
relative modular quantities come from the same actual channel model. -/
theorem equality_intertwining (M : SupportedRelativeModularModel Φ ρ σ)
    (hEq : finiteTraceLogRelativeEntropy ρ σ =
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ))
    (f : ℝ → ℝ) :
    cfc f M.data.A *ᵥ M.data.ξ = M.data.V *ᵥ (cfc f M.data.B *ᵥ M.data.η) := by
  classical
  have hξ : (star M.data.ξ ⬝ᵥ M.data.ξ).re = 1 := by
    simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex, M.normξ] using
      RHLinalg.hermForm_one M.data.ξ
  have hη : (star M.data.η ⬝ᵥ M.data.η).re = 1 := by
    simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex, M.normη] using
      RHLinalg.hermForm_one M.data.η
  have hsaturation : (star (M.data.V *ᵥ M.data.η) ⬝ᵥ (M.data.V *ᵥ M.data.η)).re =
      (star M.data.η ⬝ᵥ M.data.η).re := by rw [M.mapsη, hξ, hη]
  have hlog : (star (M.data.V *ᵥ M.data.η) ⬝ᵥ
      (cfc Real.log M.data.A *ᵥ (M.data.V *ᵥ M.data.η))).re =
      (star M.data.η ⬝ᵥ (cfc Real.log M.data.B *ᵥ M.data.η)).re := by
    rw [M.mapsη]
    exact neg_injective (M.canonicalTraceR.symm.trans (hEq.trans M.canonicalTraceT))
  simpa only [M.mapsη] using log_equality_forces_functional_intertwining
    M.data.A M.data.B M.hA M.hB M.data.V M.hVnorm M.hVA M.data.η hsaturation hlog f

/-- The inverse-square-root spectral relation controls each positive input
support coordinate of the actual channel adjoint. -/
theorem inverse_sqrt_coordinates (M : SupportedRelativeModularModel Φ ρ σ)
    (hEq : finiteTraceLogRelativeEntropy ρ σ =
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ))
    (j : M.data.J) (i : M.data.I) :
    (Real.sqrt (M.data.sj j) : ℂ) *
        (star (M.data.v j) ⬝ᵥ (M.data.Ψ
          (M.data.spectralX (cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M.data.B *ᵥ M.data.η)) *ᵥ
            M.data.u i)) =
      (Real.sqrt (M.data.ri i) : ℂ) * (star (M.data.v j) ⬝ᵥ M.data.u i) := by
  classical
  have hc := congrFun (equality_intertwining M hEq (fun t : ℝ => (Real.sqrt t)⁻¹)) (j,i)
  rw [D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal,
    Matrix.mulVec_diagonal, M.coordinateAction] at hc
  change (((Real.sqrt (M.data.sj j / M.data.ri i))⁻¹ : ℝ) : ℂ) *
    ((Real.sqrt (M.data.ri i) : ℂ) * (star (M.data.v j) ⬝ᵥ M.data.u i)) = _ at hc
  rw [Real.sqrt_div (le_of_lt j.2), Complex.ofReal_inv, Complex.ofReal_div] at hc
  have hri : (Real.sqrt (M.data.ri i) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr i.2))
  have hsj : (Real.sqrt (M.data.sj j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr j.2))
  field_simp [hri, hsj] at hc
  simpa only [one_div] using hc.symm


#print axioms equality_intertwining
#print axioms inverse_sqrt_coordinates


/-- One completed channel is chosen from Φ and σ before quantifying over ρ. -/
private theorem fixed_reference_petz_channel (Φ : QuantumChannel a b) (σ : DensityState a) :
    let K := (actual_kraus_representation Φ).kraus
    let S := cfc Real.sqrt (CStarMatrix.ofMatrix.symm σ.1)
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let W := D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralInverseSqrt Q
    let P := D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, S * (K c)ᴴ * W * X * W * K c * S) +
            Matrix.trace ((1 - P) * X) • CStarMatrix.ofMatrix.symm σ.1) ∧
      recovery.mapState (Φ.mapState σ) = σ := by
  classical
  dsimp only
  let rep := actual_kraus_representation Φ
  have hQ : (∑ c, rep.kraus c * CStarMatrix.ofMatrix.symm σ.1 *
      (rep.kraus c)ᴴ) = CStarMatrix.ofMatrix.symm (Φ.mapState σ).1 := by
    rw [← rep.haction]
    rfl
  obtain ⟨recovery, haction, hreference⟩ :=
    D5.S3.Quantum.Recovery.ReferencePetzChannel.completed_reference_petz_channel
      rep.kraus rep.hkraus σ
  rw [hQ] at haction hreference
  refine ⟨recovery, haction, ?_⟩
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm
    (recovery.toCompletelyPositiveMap (Φ.mapState σ).1) = CStarMatrix.ofMatrix.symm σ.1
  exact hreference

/-- The converse consumes the existing DPI twice, rather than reproving it. -/
private theorem recovery_implies_entropy_equality
    (support : SupportContained ρ σ) (recovery : QuantumChannel b a)
    (hρ : recovery.mapState (Φ.mapState ρ) = ρ)
    (hσ : recovery.mapState (Φ.mapState σ) = σ) :
    finiteTraceLogRelativeEntropy ρ σ =
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
  classical
  let M := supported_relative_modular_model Φ ρ σ support
  have hin := extended_quantum_relative_entropy_channel_dpi Φ ρ σ
  have hout := extended_quantum_relative_entropy_channel_dpi recovery
    (Φ.mapState ρ) (Φ.mapState σ)
  rw [hρ, hσ] at hout
  have hEq := le_antisymm hout hin
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support support,
    extendedQuantumRelativeEntropy_eq_coe_of_support M.outputSupport] at hEq
  exact WithTop.coe_injective hEq

#print axioms fixed_reference_petz_channel
#print axioms recovery_implies_entropy_equality

-- The remaining whole-space support lifting, Schwarz saturation, fixed
-- channel recovery and full equivalence are not proved by this draft.

end D5.S3.Quantum.Recovery.CanonicalPetzEquality
