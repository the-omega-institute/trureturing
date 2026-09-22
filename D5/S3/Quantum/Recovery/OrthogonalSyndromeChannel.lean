/- GID: D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/OrthogonalSyndromeChannel
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   digest: Orthogonal syndrome encoding and its explicit full-space decoder are canonical CPTP channels and expose a multiplicative logical algebra. -/

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

/-- The logical representation preserves the actual matrix adjoint. -/
theorem logical_representation_star (S : s → Matrix n d ℂ) (A : Matrix d d ℂ) :
    (logicalRepresentation S A)ᴴ = logicalRepresentation S Aᴴ := by
  simp only [logicalRepresentation, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

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

/-- Any one syndrome copy recovers the complete logical observable. -/
theorem logical_representation_restrict (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A : Matrix d d ℂ) (j : s) :
    (S j)ᴴ * logicalRepresentation S A * S j = A := by
  calc
    _ = (S j)ᴴ * (logicalRepresentation S A * S j) := Matrix.mul_assoc _ _ _
    _ = (S j)ᴴ * (S j * A) := by rw [logical_representation_on_copy S hS]
    _ = ((S j)ᴴ * S j) * A := (Matrix.mul_assoc _ _ _).symm
    _ = A := by rw [hS j j]; simp

/-- The physical observable algebra loses no logical operator when a syndrome copy exists. -/
theorem logical_representation_injective (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (j : s) :
    Function.Injective (logicalRepresentation S) := by
  intro A B hAB
  have h := congrArg (fun X => (S j)ᴴ * X * S j) hAB
  simpa only [logical_representation_restrict S hS] using h

/-- Logical multiplication is intertwined even for coherent syndrome matrices. -/
theorem logical_action_on_encoding (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A rho : Matrix d d ℂ) (sigma : Matrix s s ℂ) :
    logicalRepresentation S A * syndromeEncoding S sigma rho =
      syndromeEncoding S sigma (A * rho) := by
  simp only [syndromeEncoding, Matrix.mul_sum, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  calc
    _ = (logicalRepresentation S A * S j) * rho * (S k)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = S j * (A * rho) * (S k)ᴴ := by
      rw [logical_representation_on_copy S hS]
      simp only [Matrix.mul_assoc]

/-- The total support is an orthogonal projection. -/
theorem code_support_projection (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) :
    (codeSupport S)ᴴ = codeSupport S ∧ codeSupport S * codeSupport S = codeSupport S := by
  constructor
  · simpa [codeSupport] using logical_representation_star S (1 : Matrix d d ℂ)
  · simpa [codeSupport] using logical_representation_mul S hS (1 : Matrix d d ℂ) 1

/-- Each syndrome copy lies in the explicitly constructed support. -/
theorem code_support_on_copy (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (j : s) : codeSupport S * S j = S j := by
  simp only [codeSupport, logicalRepresentation, Matrix.mul_one, Matrix.sum_mul,
    Matrix.mul_assoc]
  classical
  rw [Finset.sum_eq_single j]
  · rw [hS j j]
    simp
  · intro i hi hij
    rw [hS i j]
    simp [hij]
  · simp

/-- This support statement includes coherent, off-diagonal syndrome matrices. -/
theorem code_support_on_encoding (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (sigma : Matrix s s ℂ) (rho : Matrix d d ℂ) :
    codeSupport S * syndromeEncoding S sigma rho = syndromeEncoding S sigma rho := by
  simp only [syndromeEncoding, Matrix.mul_sum, Matrix.mul_smul,
    ← Matrix.mul_assoc, code_support_on_copy S hS]

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
  obtain ⟨hP, hPP⟩ := code_support_projection S hS
  have hK : (∑ i, ((S i)ᴴ)ᴴ * (S i)ᴴ) = codeSupport S := by
    simp [codeSupport, logicalRepresentation]
  obtain ⟨decoder, hd⟩ := complete_quantum_channel
    (fun i => (S i)ᴴ) (codeSupport S) v hP hPP hK
  have haction : ∀ X : Matrix n n ℂ,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      syndromeDecoding S X +
        Matrix.trace ((1 - codeSupport S) * X) • Matrix.single v v 1 := by
    intro X
    simpa only [syndromeDecoding, Matrix.conjTranspose_conjTranspose] using hd X
  refine ⟨decoder, haction, ?_⟩
  intro sigma hsigma rho
  rw [haction]
  have hz : (1 - codeSupport S) * syndromeEncoding S sigma rho = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, code_support_on_encoding S hS, sub_self]
  rw [hz, Matrix.trace_zero, zero_smul, add_zero]
  exact trace_one_syndrome_recovery S hS sigma hsigma rho

/-- A Gram factor of the syndrome density supplies concrete encoding Kraus maps. -/
def encodingKraus (S : s → Matrix n d ℂ) (B : Matrix s s ℂ) (j : s) :
    Matrix n d ℂ := ∑ i, B i j • S i

private theorem encoding_kraus_column_gram (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ) (j : s) :
    (encodingKraus S B j)ᴴ * encodingKraus S B j =
      (∑ i, star (B i j) * B i j) • (1 : Matrix d d ℂ) := by
  simp only [encodingKraus, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [hS]
  simp [Finset.sum_smul]

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
    Matrix.mul_smul, smul_smul, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

/-- A unit-trace syndrome Gram matrix defines a canonical CPTP encoding. -/
theorem gram_syndrome_encoder (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ)
    (hB : Matrix.trace (B * Bᴴ) = 1) :
    ∃ encoder : QuantumChannel d n, ∀ rho : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
      syndromeEncoding S (B * Bᴴ) rho := by
  have hK : (∑ j, (encodingKraus S B j)ᴴ * encodingKraus S B j) = 1 := by
    rw [encoding_kraus_gram S hS B, hB, one_smul]
  obtain ⟨encoder, he⟩ := finite_kraus_quantum_channel (encodingKraus S B) hK
  refine ⟨encoder, fun rho => ?_⟩
  rw [he rho, encoding_kraus_action]

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
  obtain ⟨encoder, he⟩ := gram_syndrome_encoder S hS Bᴴ ht
  refine ⟨encoder, fun rho => ?_⟩
  simpa only [Matrix.conjTranspose_conjTranspose, ← hB] using he rho

/-- Both canonical channels are constructed, and their actual composition is the identity on every logical matrix. -/
theorem reversible_syndrome_channels (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (v : d) (sigma : Matrix s s ℂ)
    (hpos : sigma.PosSemidef) (htrace : Matrix.trace sigma = 1) :
    ∃ encoder : QuantumChannel d n, ∃ decoder : QuantumChannel n d,
      ∀ rho : Matrix d d ℂ,
        decoder.toCompletelyPositiveMap
          (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
        CStarMatrix.ofMatrix rho := by
  obtain ⟨encoder, he⟩ := positive_syndrome_encoder S hS sigma hpos htrace
  obtain ⟨decoder, _, hd⟩ := full_syndrome_decoder S hS v
  refine ⟨encoder, decoder, fun rho => ?_⟩
  have hencode : encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho) =
      CStarMatrix.ofMatrix (syndromeEncoding S sigma rho) := by
    apply CStarMatrix.ofMatrix.symm.injective
    exact he rho
  rw [hencode]
  apply CStarMatrix.ofMatrix.symm.injective
  exact hd sigma htrace rho

#print axioms logical_representation_mul
#print axioms logical_representation_star
#print axioms logical_representation_on_copy
#print axioms logical_representation_restrict
#print axioms logical_representation_injective
#print axioms logical_action_on_encoding
#print axioms code_support_projection
#print axioms code_support_on_copy
#print axioms code_support_on_encoding
#print axioms full_syndrome_decoder
#print axioms encoding_kraus_gram
#print axioms encoding_kraus_action
#print axioms gram_syndrome_encoder
#print axioms positive_syndrome_encoder
#print axioms reversible_syndrome_channels

end D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
