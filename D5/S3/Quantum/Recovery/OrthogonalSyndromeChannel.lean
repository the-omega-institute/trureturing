/- GID: D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/OrthogonalSyndromeChannel
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Orthogonal syndrome channels expose a multiplicative logical algebra. -/

import D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
import D5.S3.Quantum.Recovery.KrausCompletion

/-!
# Orthogonal syndrome channels and logical algebra

Library-first: reuse the pre-existing `OrthogonalSyndromes`, `syndromeEncoding`,
`syndromeDecoding`, and their recovery theorem. The new obligations are support,
complete-positive extension, and the logical multiplication law. The canonical
channel predicate remains owned by `FiniteStateChannel`; Kraus realisation is
reused from `FiniteKrausChannel`. No alternate quantum channel abstraction is
introduced. The construction is the usual orthogonal-syndrome realisation of
exact quantum error correction, not a new correction criterion.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {s n d : Type*} [Fintype s] [DecidableEq s]
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]

/-- Every syndrome carries the same logical matrix, without probability weights. -/
def logicalRepresentation (S : s → Matrix n d ℂ) (A : Matrix d d ℂ) :
    Matrix n n ℂ := ∑ i, S i * A * (S i)ᴴ

/-- The union of all orthogonal syndrome supports. -/
def codeSupport (S : s → Matrix n d ℂ) : Matrix n n ℂ :=
  logicalRepresentation S 1

private theorem product_block (S : s → Matrix n d ℂ) (hS : OrthogonalSyndromes S)
    (A B : Matrix d d ℂ) (i j : s) :
    (S i * A * (S i)ᴴ) * (S j * B * (S j)ᴴ) =
      if i = j then S i * (A * B) * (S i)ᴴ else 0 := by
  calc
    _ = S i * A * ((S i)ᴴ * S j) * B * (S j)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hS i j]
      by_cases hij : i = j
      · subst j
        simp [Matrix.mul_assoc]
      · simp [hij]

/-- Orthogonality makes the physical logical algebra multiplicative. -/
theorem logical_representation_mul (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A B : Matrix d d ℂ) :
    logicalRepresentation S A * logicalRepresentation S B =
      logicalRepresentation S (A * B) := by
  simp only [logicalRepresentation, Matrix.sum_mul, Matrix.mul_sum]
  simp_rw [product_block S hS A B]
  simp

/-- The same observable acts on every physical syndrome copy. -/
theorem logical_representation_on_copy (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A : Matrix d d ℂ) (j : s) :
    logicalRepresentation S A * S j = S j * A := by
  simp only [logicalRepresentation, Matrix.sum_mul, Matrix.mul_assoc]
  rw [Finset.sum_eq_single j]
  · rw [hS j j]
    simp
  · intro i hi hij
    rw [hS i j]
    simp [hij]
  · simp

/-- Construct a full CPTP decoder; its complement reset vanishes on every encoded matrix. -/
theorem full_syndrome_decoder (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (v : d) :
    ∃ decoder : QuantumChannel n d,
      (∀ X : Matrix n n ℂ,
        CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        syndromeDecoding S X +
          Matrix.trace ((1 - codeSupport S) * X) • Matrix.single v v 1) ∧
      (∀ sigma : Matrix s s ℂ, Matrix.trace sigma = 1 → ∀ rho : Matrix d d ℂ,
        CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (syndromeEncoding S sigma rho))) = rho) := by
  have hP : (codeSupport S)ᴴ = codeSupport S := by
    simp only [codeSupport, logicalRepresentation, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc]
  have hPP : codeSupport S * codeSupport S = codeSupport S := by
    simpa [codeSupport] using logical_representation_mul S hS
      (1 : Matrix d d ℂ) 1
  have hK : (∑ i, ((S i)ᴴ)ᴴ * (S i)ᴴ) = codeSupport S := by
    simp [codeSupport, logicalRepresentation]
  obtain ⟨decoder, hd⟩ := finite_kraus_quantum_channel
    (completeKraus (fun i => (S i)ᴴ) (codeSupport S) v)
    (complete_kraus_normalised (fun i => (S i)ᴴ) (codeSupport S) v hP hPP hK)
  have haction : ∀ X : Matrix n n ℂ,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      syndromeDecoding S X +
        Matrix.trace ((1 - codeSupport S) * X) • Matrix.single v v 1 := by
    intro X
    rw [hd X, complete_kraus_action (fun i => (S i)ᴴ) (codeSupport S) v hP hPP]
    simp only [syndromeDecoding, Matrix.conjTranspose_conjTranspose]
  refine ⟨decoder, haction, ?_⟩
  intro sigma hsigma rho
  rw [haction]
  have hcopy (j : s) : codeSupport S * S j = S j := by
    simpa [codeSupport] using logical_representation_on_copy S hS
      (1 : Matrix d d ℂ) j
  have hsupport : codeSupport S * syndromeEncoding S sigma rho =
      syndromeEncoding S sigma rho := by
    simp only [syndromeEncoding, Matrix.mul_sum, Matrix.mul_smul,
      ← Matrix.mul_assoc, hcopy]
  have hz : (1 - codeSupport S) * syndromeEncoding S sigma rho = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hsupport, sub_self]
  rw [hz, Matrix.trace_zero, zero_smul, add_zero]
  rw [orthogonal_syndrome_recovery S hS, hsigma, one_smul]

/-- A Gram factor of the syndrome density supplies concrete encoding Kraus maps. -/
def encodingKraus (S : s → Matrix n d ℂ) (B : Matrix s s ℂ) (j : s) :
    Matrix n d ℂ := ∑ i, B i j • S i

private theorem encoding_kraus_column_gram (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ) (j : s) :
    (encodingKraus S B j)ᴴ * encodingKraus S B j =
      (∑ i, star (B i j) * B i j) • (1 : Matrix d d ℂ) := by
  simp only [encodingKraus, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [hS i i]
    simp [mul_comm]
  · intro k hk hki
    rw [hS k i]
    simp [hki]
  · simp

/-- The Gram factor's trace is exactly the encoding normalisation. -/
theorem encoding_kraus_gram (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ) :
    (∑ j, (encodingKraus S B j)ᴴ * encodingKraus S B j) =
      Matrix.trace (B * Bᴴ) • (1 : Matrix d d ℂ) := by
  simp_rw [encoding_kraus_column_gram S hS B]
  rw [← Finset.sum_smul]
  congr 1
  change (∑ j, ∑ i, star (B i j) * B i j) =
    ∑ i, ∑ j, B i j * star (B i j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The Kraus sum is the pre-existing coherent syndrome encoding, not just a diagonal mixture. -/
theorem encoding_kraus_action (S : s → Matrix n d ℂ) (B : Matrix s s ℂ)
    (rho : Matrix d d ℂ) :
    (∑ j, encodingKraus S B j * rho * (encodingKraus S B j)ᴴ) =
      syndromeEncoding S (B * Bᴴ) rho := by
  simp only [encodingKraus, syndromeEncoding, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_smul]
  change (∑ j, ∑ k, ∑ i,
      (star (B k j) * B i j) • (S i * rho * (S k)ᴴ)) =
    ∑ i, ∑ k, ∑ j,
      (B i j * star (B k j)) • (S i * rho * (S k)ᴴ)
  calc
    _ = ∑ j, ∑ i, ∑ k,
        (star (B k j) * B i j) • (S i * rho * (S k)ᴴ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k,
        (star (B k j) * B i j) • (S i * rho * (S k)ᴴ) := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j,
        (star (B k j) * B i j) • (S i * rho * (S k)ᴴ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]

/-- Positive syndrome densities admit the Gram construction via the library's C-star factorisation. -/
theorem positive_syndrome_encoder (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (sigma : Matrix s s ℂ)
    (hpos : sigma.PosSemidef) (htrace : Matrix.trace sigma = 1) :
    ∃ encoder : QuantumChannel d n, ∀ rho : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
      syndromeEncoding S sigma rho := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix s s ℂ, sigma = Bᴴ * B := by
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr hpos
  have ht : Matrix.trace (Bᴴ * (Bᴴ)ᴴ) = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose, ← hB] using htrace
  have hK : (∑ j, (encodingKraus S Bᴴ j)ᴴ * encodingKraus S Bᴴ j) = 1 := by
    rw [encoding_kraus_gram S hS Bᴴ, ht, one_smul]
  obtain ⟨encoder, he⟩ := finite_kraus_quantum_channel (encodingKraus S Bᴴ) hK
  refine ⟨encoder, fun rho => ?_⟩
  rw [he rho, encoding_kraus_action]
  simpa only [Matrix.conjTranspose_conjTranspose, ← hB]

#print axioms logical_representation_mul
#print axioms logical_representation_on_copy
#print axioms full_syndrome_decoder
#print axioms encoding_kraus_gram
#print axioms encoding_kraus_action
#print axioms positive_syndrome_encoder

end D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
