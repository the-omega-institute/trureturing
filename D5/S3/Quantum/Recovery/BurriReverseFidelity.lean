/- GID: D5/S3/Quantum/Recovery/BurriReverseFidelity
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReverseFidelity
   mirror-E: none(waiver:unfinished-independent-fidelity-review)
   anchors: []
   utility: none
   digest: Canonical entanglement fidelity for the actual reverse-instance channels. -/

import D5.S3.Quantum.Recovery.BurriReverseCompletion

/-! The channel acts on the first tensor factor and the reference is the second. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.BurriReverseDecoder
open D5.S3.Quantum.Recovery.BurriReversePolar
open D5.S3.Quantum.Recovery.BurriReverseOverlap
open D5.S3.Quantum.Recovery.BurriReversePetz
open D5.S3.QuantumBounds.PeritoTsirelson
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Recovery.BurriReverseFidelity

def noiseChannel : QuantumChannel A B := physical_channel.choose
def swChannel : QuantumChannel B A := recovery_channels.1.choose

/-- The actual channel tensored with the identity on the second, reference factor. -/
def tensorReference (channel : QuantumChannel A A)
    (T : Matrix (A × A) (A × A) ℂ) : Matrix (A × A) (A × A) ℂ :=
  fun p q => CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun i j => T (i, p.2) (j, q.2)))) p.1 q.1

def entanglementFidelity (channel : QuantumChannel A A) : ℝ :=
  (star (maxEntangledVector A) ⬝ᵥ
    tensorReference channel (maxEntangled A) *ᵥ maxEntangledVector A).re

theorem canonical_reference_amplitude (i j : A) :
    cfc Real.sqrt rho i j = maxEntangledVector A (i, j) := by
  rw [reference_root]
  by_cases h : i = j <;>
    simp [Matrix.one_apply, maxEntangledVector, Fintype.card_fin, h, one_div]

theorem canonical_reference_purification :
    (maxEntangled A).PosSemidef ∧ Matrix.trace (maxEntangled A) = 1 ∧
      partialTraceRight (maxEntangled A) = rho := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, (max_entangled_density A).2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, maxEntangled, maxEntangledVector,
      Fintype.card_fin, rho, Matrix.one_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_two, ← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem tensor_reference_kraus {s : Type*} [Fintype s]
    (channel : QuantumChannel A A) (K : s → Matrix A A ℂ)
    (h : ∀ T : Matrix A A ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ k : s, K k * T * (K k)ᴴ)
    (T : Matrix (A × A) (A × A) ℂ) :
    tensorReference channel T = ∑ k : s,
      Matrix.kronecker (K k) (1 : Matrix A A ℂ) * T *
        (Matrix.kronecker (K k) (1 : Matrix A A ℂ))ᴴ := by
  ext ⟨i, r⟩ ⟨j, t⟩
  dsimp only [tensorReference]
  rw [h]
  fin_cases r <;> fin_cases t <;>
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul]

theorem composite_channel_action (decoder : QuantumChannel B A) (D : E → Matrix A B ℂ)
    (hD : ∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
      (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ e : E, D e * T * (D e)ᴴ) (T : Matrix A A ℂ) :
    CStarMatrix.ofMatrix.symm
      ((decoder.comp noiseChannel).toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ ef : E × E, composite D ef * T * (composite D ef)ᴴ := by
  change CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap
    (noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T))) = _
  have hn : noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T) =
      CStarMatrix.ofMatrix (∑ e : E, noiseKraus e * T * (noiseKraus e)ᴴ) :=
    congrArg CStarMatrix.ofMatrix (physical_channel.choose_spec T)
  rw [hn, hD]
  simp only [composite, Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem actual_recovered_purification (decoder : QuantumChannel B A) (D : E → Matrix A B ℂ)
    (hD : ∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
      (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ e : E, D e * T * (D e)ᴴ) :
    tensorReference (decoder.comp noiseChannel) (maxEntangled A) =
      recoveredPurification D := by
  rw [tensor_reference_kraus _ (composite D) (composite_channel_action decoder D hD)]
  unfold recoveredPurification
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ ef : E × E, _) = ∑ j, _
  exact (labels.sum_comp (fun ef : E × E =>
    Matrix.kronecker (composite D ef) (1 : Matrix A A ℂ) * maxEntangled A *
      (Matrix.kronecker (composite D ef) (1 : Matrix A A ℂ))ᴴ)).symm

theorem actual_entanglement_fidelity (decoder : QuantumChannel B A) (D : E → Matrix A B ℂ)
    (hD : ∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
      (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ e : E, D e * T * (D e)ᴴ) :
    entanglementFidelity (decoder.comp noiseChannel) = fidelity D := by
  unfold entanglementFidelity fidelity
  rw [actual_recovered_purification decoder D hD]

theorem actual_strict_fidelity :
    entanglementFidelity (swChannel.comp noiseChannel) <
      entanglementFidelity (petzChannel.comp noiseChannel) := by
  rw [actual_entanglement_fidelity _ _ recovery_channels.1.choose_spec,
    actual_entanglement_fidelity _ _ petz_channel_action]
  exact canonical_overlap_gap

def completedKraus (Uprime : Matrix P P ℂ) (e : E) : Matrix A B ℂ :=
  ((Uprime * W) * prepare).submatrix (fun k => (k, e)) id

/-- Every admissible complex completion defines the same physical recovery and
therefore satisfies the strict comparison with ordinary Petz. -/
theorem actual_strict_fidelity_all_completions (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1)
    (hp : (BurriReverseSource.M * Uprime).PosSemidef) :
    ∃ decoder : QuantumChannel B A,
      (∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, completedKraus Uprime e * T * (completedKraus Uprime e)ᴴ) ∧
      entanglementFidelity (decoder.comp noiseChannel) <
        entanglementFidelity (petzChannel.comp noiseChannel) := by
  have hD : completedKraus Uprime = swKraus (cosine 4) (cosine 2) (sine 4) (sine 2) := by
    funext e
    ext k b
    exact BurriReverseCompletion.source_decoder_completion_independent Uprime hu hp e k b
  rw [hD]
  exact ⟨swChannel, recovery_channels.1.choose_spec, actual_strict_fidelity⟩

#print axioms canonical_reference_purification
#print axioms tensor_reference_kraus
#print axioms actual_recovered_purification
#print axioms actual_strict_fidelity
#print axioms actual_strict_fidelity_all_completions

end D5.S3.Quantum.Recovery.BurriReverseFidelity
