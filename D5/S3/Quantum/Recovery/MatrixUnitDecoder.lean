/- GID: D5/S3/Quantum/Recovery/MatrixUnitDecoder
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/MatrixUnitDecoder
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   digest: Logical matrix units construct basis-free decoder Kraus operators, their support projection, and the full canonical CPTP decoder. -/

import D5.S3.Quantum.Recovery.KrausCompletion

/-!
# Decoder from logical matrix units

No syndrome eigenbasis is an input. The only algebraic input is a finite star
representation's actual matrix-unit multiplication law. Its support is computed
as the sum of its diagonal units. The existing Kraus completion constructs the
full canonical quantum channel. This does not assert that a parameterized
support bundle has a global vector frame or prove a Chern-class statement.
-/

noncomputable section
open scoped Matrix BigOperators

namespace D5.S3.Quantum.Recovery.MatrixUnitDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {d n : Type*} [Fintype d] [DecidableEq d]
  [Fintype n] [DecidableEq n]

/-- The unit of the represented corner algebra. -/
def unitSupport (F : d → d → Matrix n n ℂ) : Matrix n n ℂ := ∑ i, F i i

/-- The b-th physical row of the first logical row of matrix units. -/
def decoderKraus (F : d → d → Matrix n n ℂ) (v : d) (b : n) : Matrix d n ℂ :=
  fun i c => F v i b c

/-- The computed corner unit is a Hermitian projection. -/
theorem unit_support_projection (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) :
    (unitSupport F)ᴴ = unitSupport F ∧ unitSupport F * unitSupport F = unitSupport F := by
  constructor
  · simp only [unitSupport, Matrix.conjTranspose_sum, hstar]
  · simp only [unitSupport, Matrix.sum_mul, Matrix.mul_sum, hmul]
    simp

/-- Every represented matrix unit is supported on both sides. -/
theorem unit_support_action (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (i j : d) : unitSupport F * F i j = F i j ∧ F i j * unitSupport F = F i j := by
  constructor
  · simp [unitSupport, Matrix.sum_mul, hmul]
  · simp [unitSupport, Matrix.mul_sum, hmul]

/-- The explicitly constructed decoder has exactly the represented support effect. -/
theorem decoder_kraus_gram (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d) :
    (∑ b, (decoderKraus F v b)ᴴ * decoderKraus F v b) = unitSupport F := by
  ext x y
  change (∑ b, ∑ i, star (F v i b x) * F v i b y) = ∑ i, F i i x y
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ((F v i)ᴴ * F v i) x y := rfl
    _ = (F i v * F v i) x y := by rw [hstar]
    _ = F i i x y := by rw [hmul]; simp

/-- The decoder reads each logical entry by a trace pairing with the reversed matrix unit. -/
theorem decoder_trace_pairing (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d)
    (X : Matrix n n ℂ) (i j : d) :
    (∑ b, decoderKraus F v b * X * (decoderKraus F v b)ᴴ) i j =
      Matrix.trace (F j i * X) := by
  calc
    _ = Matrix.trace (F v i * X * (F v j)ᴴ) := by
      simp only [decoderKraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag_apply]
    _ = Matrix.trace (F j i * X) := by
      rw [hstar, Matrix.trace_mul_comm (F v i * X) (F j v),
        ← Matrix.mul_assoc, hmul]
      simp

/-- The full-space CPTP decoder is constructed without selecting a syndrome frame. -/
theorem matrix_unit_decoder_channel (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d) :
    ∃ decoder : QuantumChannel n d, ∀ X : Matrix n n ℂ, ∀ i j : d,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) i j =
      Matrix.trace (F j i * X) +
        Matrix.trace ((1 - unitSupport F) * X) * (Matrix.single v v (1 : ℂ)) i j := by
  obtain ⟨hP, hPP⟩ := unit_support_projection F hmul hstar
  obtain ⟨decoder, hdecoder⟩ := complete_quantum_channel
    (decoderKraus F v) (unitSupport F) v hP hPP (decoder_kraus_gram F hmul hstar v)
  refine ⟨decoder, fun X i j => ?_⟩
  have h := congrArg (fun M : Matrix d d ℂ => M i j) (hdecoder X)
  simpa [decoder_trace_pairing F hmul hstar v X i j] using h

/-- Commutant weights have a scalar logical trace pairing, even without a chosen factorization. -/
theorem commutant_trace_pairing (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (v : d) (Q : Matrix n n ℂ)
    (hcomm : ∀ i j, Q * F i j = F i j * Q) (i j : d) :
    Matrix.trace (F i j * Q) = if i = j then Matrix.trace (F v v * Q) else 0 := by
  calc
    _ = Matrix.trace ((F i v * F v j) * Q) := by rw [hmul]; simp
    _ = Matrix.trace (F v j * (Q * F i v)) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((F v j * F i v) * Q) := by rw [hcomm, Matrix.mul_assoc]
    _ = _ := by
      rw [hmul]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h]

/-- Reconstruct a logical matrix in the represented corner algebra. -/
def representedMatrix (F : d → d → Matrix n n ℂ) (A : Matrix d d ℂ) :
    Matrix n n ℂ := ∑ i, ∑ j, A i j • F i j

private theorem represented_one (F : d → d → Matrix n n ℂ) :
    representedMatrix F (1 : Matrix d d ℂ) = unitSupport F := by
  simp [representedMatrix, unitSupport, Matrix.one_apply, ite_smul]

/-- Matrix-unit multiplication reconstructs the full multiplicative logical representation. -/
theorem represented_matrix_mul (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (A B : Matrix d d ℂ) :
    representedMatrix F A * representedMatrix F B = representedMatrix F (A * B) := by
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (F i j * F k l) := by
      simp only [representedMatrix, Matrix.sum_mul, Matrix.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    _ = ∑ i, ∑ j, ∑ l, (A i j * B j l) • F i l := by
      simp_rw [hmul]
      simp [smul_ite]
    _ = ∑ i, ∑ l, ∑ j, (A i j * B j l) • F i l := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = representedMatrix F (A * B) := by
      simp only [representedMatrix, Matrix.mul_apply, Finset.sum_smul]

/-- The reconstructed representation preserves the matrix adjoint. -/
theorem represented_matrix_star (F : d → d → Matrix n n ℂ)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (A : Matrix d d ℂ) :
    (representedMatrix F A)ᴴ = representedMatrix F Aᴴ := by
  simp only [representedMatrix, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    hstar, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

private theorem represented_sum {s : Type*} [Fintype s]
    (F : d → d → Matrix n n ℂ) (A : s → Matrix d d ℂ) :
    representedMatrix F (∑ a, A a) = ∑ a, representedMatrix F (A a) := by
  simp only [representedMatrix, Matrix.sum_apply, Finset.sum_smul]
  calc
    (∑ i, ∑ j, ∑ a, A a i j • F i j) = ∑ i, ∑ a, ∑ j, A a i j • F i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, A a i j • F i j := by rw [Finset.sum_comm]

private theorem weighted_pairing (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (v : d) (Q : Matrix n n ℂ) (hcomm : ∀ i j, Q * F i j = F i j * Q)
    (htrace : Matrix.trace (F v v * Q) = 1) (A : Matrix d d ℂ) (i j : d) :
    Matrix.trace (F j i * (Q * representedMatrix F A)) = A i j := by
  calc
    _ = ∑ a, ∑ b, A a b * Matrix.trace ((F j i * F a b) * Q) := by
      simp only [representedMatrix, Matrix.mul_sum, Matrix.mul_smul,
        Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      congr 1
      calc
        F j i * Q * F a b = F j i * (Q * F a b) := Matrix.mul_assoc _ _ _
        _ = (F j i * F a b) * Q := by rw [hcomm, Matrix.mul_assoc]
    _ = ∑ b, A i b * Matrix.trace (F j b * Q) := by
      simp_rw [hmul]
      simp [ite_mul]
    _ = ∑ b, A i b * (if j = b then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [commutant_trace_pairing F hmul v Q hcomm j b, htrace]
    _ = A i j := by simp

/-- The actual full decoder recovers any supported commutant-weighted logical matrix. No syndrome basis or preselected syndrome state is needed. -/
theorem decoder_recovers_commutant_weight (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d) (Q : Matrix n n ℂ)
    (hcomm : ∀ i j, Q * F i j = F i j * Q)
    (hsupport : unitSupport F * Q = Q) (htrace : Matrix.trace (F v v * Q) = 1) :
    ∃ decoder : QuantumChannel n d, ∀ A : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Q * representedMatrix F A))) = A := by
  obtain ⟨decoder, hd⟩ := matrix_unit_decoder_channel F hmul hstar v
  refine ⟨decoder, fun A => ?_⟩
  have hz : (1 - unitSupport F) * (Q * representedMatrix F A) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hsupport, sub_self, Matrix.zero_mul]
  ext i j
  rw [hd, weighted_pairing F hmul v Q hcomm htrace, hz, Matrix.trace_zero, zero_mul, add_zero]

/-- A normalized logical instrument has an explicit normalized physical realization; the complement is one failure Kraus operator. -/
theorem represented_instrument_normalized {s : Type*} [Fintype s]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i)
    (L : s → Matrix d d ℂ) (hL : (∑ a, (L a)ᴴ * L a) = 1) :
    (∑ a, (representedMatrix F (L a))ᴴ * representedMatrix F (L a)) +
      (1 - unitSupport F)ᴴ * (1 - unitSupport F) = (1 : Matrix n n ℂ) := by
  obtain ⟨hP, hPP⟩ := unit_support_projection F hmul hstar
  have hnorm : (∑ a, (representedMatrix F (L a))ᴴ * representedMatrix F (L a)) =
      unitSupport F := by
    simp_rw [represented_matrix_star F hstar, represented_matrix_mul F hmul]
    rw [← represented_sum, hL, represented_one]
  rw [hnorm]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
  abel

#print axioms unit_support_projection
#print axioms unit_support_action
#print axioms decoder_kraus_gram
#print axioms decoder_trace_pairing
#print axioms matrix_unit_decoder_channel
#print axioms commutant_trace_pairing

#print axioms represented_matrix_mul
#print axioms represented_matrix_star
#print axioms decoder_recovers_commutant_weight
#print axioms represented_instrument_normalized

end D5.S3.Quantum.Recovery.MatrixUnitDecoder
