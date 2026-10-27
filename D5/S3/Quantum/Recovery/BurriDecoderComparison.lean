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

namespace C := CanonicalEntanglementFidelity
namespace F := BurriReplacementDecoder
namespace R := BurriReverseDecoder
namespace RF := BurriReverseFidelity
namespace RP := BurriReversePetz

theorem forward_vector : C.vector F.rho = F.referenceVector := by
  funext ⟨r, i⟩
  dsimp only [C.vector]
  rw [F.reference_root]
  by_cases h : r = i
  · subst i
    simp [F.referenceVector, Matrix.diagonal_apply]
  · simp [F.referenceVector, Matrix.diagonal_apply, h, Ne.symm h]

theorem forward_fidelity (channel : QuantumChannel F.A F.A) :
    C.fidelity F.rho channel = F.entanglementFidelity channel := by
  simp only [C.fidelity, C.pure, forward_vector]
  rfl

/-- The old reverse amplitude is channel first. Flipping it gives exactly the
common positive-root amplitude, without identifying the two input states. -/
theorem reverse_vector :
    C.vector R.rho = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector R.A ∘ Prod.swap := by
  funext p
  exact RF.canonical_reference_amplitude p.2 p.1

theorem reverse_extension_factor_flip (channel : QuantumChannel R.A R.A)
    (T : Matrix (R.A × R.A) (R.A × R.A) ℂ) :
    C.referenceExtension channel (T.submatrix Prod.swap Prod.swap) =
      (RF.tensorReference channel T).submatrix Prod.swap Prod.swap := by
  rfl

theorem reverse_fidelity (channel : QuantumChannel R.A R.A) :
    C.fidelity R.rho channel = RF.entanglementFidelity channel := by
  have hp : C.pure R.rho =
      (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled R.A).submatrix
        Prod.swap Prod.swap := by
    ext p q
    simp [C.pure, reverse_vector,
      D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled, Matrix.vecMulVec_apply]
  unfold C.fidelity
  rw [hp, reverse_vector, reverse_extension_factor_flip, C.overlap_factor_flip]
  rfl

def forwardCompletedKraus (Uprime : Matrix F.P F.P ℂ) (e : F.E) : Matrix F.A F.B ℂ :=
  ((Uprime * F.W) * F.prepare).submatrix (fun k => (k, e)) id

/-- The two literal Appendix A instances have opposite strict comparisons in
one fidelity. Each comparison survives every complex positive-polar completion,
and the decoder action is certified on every physical input matrix. -/
theorem result :
    ((C.pure F.rho).PosSemidef ∧ Matrix.trace (C.pure F.rho) = 1 ∧
      partialTraceLeft (C.pure F.rho) = F.rho) ∧
    ((C.pure R.rho).PosSemidef ∧ Matrix.trace (C.pure R.rho) = 1 ∧
      partialTraceLeft (C.pure R.rho) = R.rho) ∧
    (C.fidelity F.rho (F.petzChannel.comp F.noiseChannel) = 1 / 3 ∧
      C.fidelity F.rho (F.swChannel.comp F.noiseChannel) = 11 / 27) ∧
    (∀ Uprime : Matrix F.P F.P ℂ, Uprime * Uprimeᴴ = 1 →
      (F.M * Uprime).PosSemidef →
      ∃ decoder : QuantumChannel F.B F.A,
        (∀ T : Matrix F.B F.B ℂ, CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
          ∑ e : F.E, forwardCompletedKraus Uprime e * T *
            (forwardCompletedKraus Uprime e)ᴴ) ∧
        C.fidelity F.rho (F.petzChannel.comp F.noiseChannel) <
          C.fidelity F.rho (decoder.comp F.noiseChannel)) ∧
    (∀ Uprime : Matrix R.P R.P ℂ, Uprime * Uprimeᴴ = 1 →
      (BurriReverseSource.M * Uprime).PosSemidef →
      ∃ decoder : QuantumChannel R.B R.A,
        (∀ T : Matrix R.B R.B ℂ, CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
          ∑ e : R.E, RF.completedKraus Uprime e * T *
            (RF.completedKraus Uprime e)ᴴ) ∧
        C.fidelity R.rho (decoder.comp RF.noiseChannel) <
          C.fidelity R.rho (RP.petzChannel.comp RF.noiseChannel)) := by
  refine ⟨C.canonical_purification _ F.rho_positive F.rho_trace,
    C.canonical_purification _ RP.reference_positive RP.reference_trace,
    ⟨(forward_fidelity _).trans F.actual_strict_fidelity.1,
      (forward_fidelity _).trans F.actual_strict_fidelity.2.1⟩, ?_, ?_⟩
  · intro Uprime hu hp
    have hD : forwardCompletedKraus Uprime = F.swKraus := by
      funext e
      ext k b
      simpa only [forwardCompletedKraus, F.W, Matrix.mul_one,
        Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
        using F.source_decoder_completion_independent Uprime hu hp e k b
    refine ⟨F.swChannel, ?_, ?_⟩
    · rw [hD]
      exact (F.actual_channels).2.1.choose_spec
    · simp only [forward_fidelity]
      exact F.actual_strict_fidelity.2.2.2
  · intro Uprime hu hp
    obtain ⟨decoder, haction, hlt⟩ := RF.actual_strict_fidelity_all_completions Uprime hu hp
    exact ⟨decoder, haction, by simpa only [reverse_fidelity] using hlt⟩

#print axioms forward_fidelity
#print axioms reverse_fidelity
#print axioms result

end D5.S3.Quantum.Recovery.BurriDecoderComparison
