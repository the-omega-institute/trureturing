/- GID: D5/S3/Quantum/Recovery/BurriDecoderComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriDecoderComparison
   mirror-E: none(waiver:linked-issue-audit)
   anchors: []
   utility: none
   digest: Opposite strict Burri decoder comparisons in one canonical fidelity. -/

import D5.S3.Quantum.Recovery.CanonicalEntanglementFidelity
import D5.S3.Quantum.Recovery.BurriReplacementDecoder
import D5.S3.Quantum.Recovery.BurriReverseFidelity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Recovery.BurriDecoderComparison

theorem forward_vector : CanonicalEntanglementFidelity.vector BurriReplacementDecoder.rho = BurriReplacementDecoder.referenceVector := by
  funext ⟨r, i⟩
  dsimp only [CanonicalEntanglementFidelity.vector]
  rw [BurriReplacementDecoder.reference_root]
  by_cases h : r = i
  · subst i
    simp [BurriReplacementDecoder.referenceVector, Matrix.diagonal_apply]
  · simp [BurriReplacementDecoder.referenceVector, Matrix.diagonal_apply, h, Ne.symm h]

theorem forward_fidelity (channel : QuantumChannel BurriReplacementDecoder.A BurriReplacementDecoder.A) :
    CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho channel = BurriReplacementDecoder.entanglementFidelity channel := by
  simp only [CanonicalEntanglementFidelity.fidelity, CanonicalEntanglementFidelity.pure, forward_vector]
  rfl

/-- The reverse amplitude is channel first. Flipping it gives exactly the
common positive-root amplitude, without identifying the two input states. -/
theorem reverse_vector :
    CanonicalEntanglementFidelity.vector BurriReverseDecoder.rho = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector BurriReverseDecoder.A ∘ Prod.swap := by
  funext p
  exact BurriReverseFidelity.canonical_reference_amplitude p.2 p.1

theorem reverse_extension_factor_flip (channel : QuantumChannel BurriReverseDecoder.A BurriReverseDecoder.A)
    (T : Matrix (BurriReverseDecoder.A × BurriReverseDecoder.A) (BurriReverseDecoder.A × BurriReverseDecoder.A) ℂ) :
    CanonicalEntanglementFidelity.referenceExtension channel (T.submatrix Prod.swap Prod.swap) =
      (BurriReverseFidelity.tensorReference channel T).submatrix Prod.swap Prod.swap := by
  rfl

theorem reverse_fidelity (channel : QuantumChannel BurriReverseDecoder.A BurriReverseDecoder.A) :
    CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho channel = BurriReverseFidelity.entanglementFidelity channel := by
  have hp : CanonicalEntanglementFidelity.pure BurriReverseDecoder.rho =
      (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled BurriReverseDecoder.A).submatrix
        Prod.swap Prod.swap := by
    ext p q
    simp [CanonicalEntanglementFidelity.pure, reverse_vector,
      D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled, Matrix.vecMulVec_apply]
  unfold CanonicalEntanglementFidelity.fidelity
  rw [hp, reverse_vector, reverse_extension_factor_flip, CanonicalEntanglementFidelity.overlap_factor_flip]
  rfl

def forwardCompletedKraus (Uprime : Matrix BurriReplacementDecoder.P BurriReplacementDecoder.P ℂ) (e : BurriReplacementDecoder.E) : Matrix BurriReplacementDecoder.A BurriReplacementDecoder.B ℂ :=
  ((Uprime * BurriReplacementDecoder.W) * BurriReplacementDecoder.prepare).submatrix (fun k => (k, e)) id

/-- The two literal Appendix A instances have opposite strict comparisons in
one fidelity. Each comparison survives every complex positive-polar completion,
and the decoder action is certified on every physical input matrix. -/
theorem result :
    ((CanonicalEntanglementFidelity.pure BurriReplacementDecoder.rho).PosSemidef ∧ Matrix.trace (CanonicalEntanglementFidelity.pure BurriReplacementDecoder.rho) = 1 ∧
      partialTraceLeft (CanonicalEntanglementFidelity.pure BurriReplacementDecoder.rho) = BurriReplacementDecoder.rho) ∧
    ((CanonicalEntanglementFidelity.pure BurriReverseDecoder.rho).PosSemidef ∧ Matrix.trace (CanonicalEntanglementFidelity.pure BurriReverseDecoder.rho) = 1 ∧
      partialTraceLeft (CanonicalEntanglementFidelity.pure BurriReverseDecoder.rho) = BurriReverseDecoder.rho) ∧
    (CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho (BurriReplacementDecoder.petzChannel.comp BurriReplacementDecoder.noiseChannel) = 1 / 3 ∧
      CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho (BurriReplacementDecoder.swChannel.comp BurriReplacementDecoder.noiseChannel) = 11 / 27) ∧
    (CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho
        (BurriReplacementDecoder.petzChannel.comp BurriReplacementDecoder.noiseChannel) <
      CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho
        (BurriReplacementDecoder.swChannel.comp BurriReplacementDecoder.noiseChannel)) ∧
    (CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho
        (BurriReversePetz.petzChannel.comp BurriReverseFidelity.noiseChannel) = 27 / 31 ∧
      CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho
        (BurriReverseFidelity.swChannel.comp BurriReverseFidelity.noiseChannel) <
      CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho
        (BurriReversePetz.petzChannel.comp BurriReverseFidelity.noiseChannel)) ∧
    (∀ Uprime : Matrix BurriReplacementDecoder.P BurriReplacementDecoder.P ℂ, Uprime * Uprimeᴴ = 1 →
      (BurriReplacementDecoder.M * Uprime).PosSemidef →
      ∃ decoder : QuantumChannel BurriReplacementDecoder.B BurriReplacementDecoder.A,
        (∀ T : Matrix BurriReplacementDecoder.B BurriReplacementDecoder.B ℂ, CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
          ∑ e : BurriReplacementDecoder.E, forwardCompletedKraus Uprime e * T *
            (forwardCompletedKraus Uprime e)ᴴ) ∧
        CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho (BurriReplacementDecoder.petzChannel.comp BurriReplacementDecoder.noiseChannel) <
          CanonicalEntanglementFidelity.fidelity BurriReplacementDecoder.rho (decoder.comp BurriReplacementDecoder.noiseChannel)) ∧
    (∀ Uprime : Matrix BurriReverseDecoder.P BurriReverseDecoder.P ℂ, Uprime * Uprimeᴴ = 1 →
      (BurriReverseSource.M * Uprime).PosSemidef →
      ∃ decoder : QuantumChannel BurriReverseDecoder.B BurriReverseDecoder.A,
        (∀ T : Matrix BurriReverseDecoder.B BurriReverseDecoder.B ℂ, CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
          ∑ e : BurriReverseDecoder.E, BurriReverseFidelity.completedKraus Uprime e * T *
            (BurriReverseFidelity.completedKraus Uprime e)ᴴ) ∧
        CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho (decoder.comp BurriReverseFidelity.noiseChannel) <
          CanonicalEntanglementFidelity.fidelity BurriReverseDecoder.rho (BurriReversePetz.petzChannel.comp BurriReverseFidelity.noiseChannel)) := by
  refine ⟨CanonicalEntanglementFidelity.canonical_purification _ BurriReplacementDecoder.rho_positive BurriReplacementDecoder.rho_trace,
    CanonicalEntanglementFidelity.canonical_purification _ BurriReversePetz.reference_positive BurriReversePetz.reference_trace,
    ⟨(forward_fidelity _).trans BurriReplacementDecoder.actual_strict_fidelity.1,
      (forward_fidelity _).trans BurriReplacementDecoder.actual_strict_fidelity.2.1⟩,
    ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [forward_fidelity] using BurriReplacementDecoder.actual_strict_fidelity.2.2.2
  · rw [reverse_fidelity, BurriReverseFidelity.actual_entanglement_fidelity
      BurriReversePetz.petzChannel BurriReverseDecoder.slice BurriReversePetz.petz_channel_action]
    exact BurriReverseOverlap.slice_overlap
  · simpa only [reverse_fidelity] using BurriReverseFidelity.actual_strict_fidelity
  · intro Uprime hu hp
    have hD : forwardCompletedKraus Uprime = BurriReplacementDecoder.swKraus := by
      funext e
      ext k b
      simpa only [forwardCompletedKraus, BurriReplacementDecoder.W, Matrix.mul_one,
        Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
        using BurriReplacementDecoder.source_decoder_completion_independent Uprime hu hp e k b
    refine ⟨BurriReplacementDecoder.swChannel, ?_, ?_⟩
    · rw [hD]
      exact (BurriReplacementDecoder.actual_channels).2.1.choose_spec
    · simp only [forward_fidelity]
      exact BurriReplacementDecoder.actual_strict_fidelity.2.2.2
  · intro Uprime hu hp
    obtain ⟨decoder, haction, hlt⟩ := BurriReverseFidelity.actual_strict_fidelity_all_completions Uprime hu hp
    exact ⟨decoder, haction, by simpa only [reverse_fidelity] using hlt⟩

#print axioms forward_fidelity
#print axioms reverse_fidelity
#print axioms result

end D5.S3.Quantum.Recovery.BurriDecoderComparison
