/- GID: D5/S3/Quantum/Information/CommutingEncodingReflectionClass
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncodingReflectionClass
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting product and reflection encodings give the same qubit state class. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm

/-! Commuting qubit product encodings and their local-reflection replacements. -/

open scoped BigOperators
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj tensor_unitary)

namespace D5.S3.Quantum.Information.CommutingEncodingReflectionClass

/-- A complete orthonormal orbit under pairwise commuting product unitaries. -/
def IsCommutingProductEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) ∧
  (∀ a b, ∑ x, star ((tensorOp (U a) *ᵥ ψ) x) * (tensorOp (U b) *ᵥ ψ) x =
    if a = b then 1 else 0)

/-- A commuting product encoding whose individual qubit factors are Hermitian involutions. -/
def IsCommutingReflectionEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsCommutingProductEncoding ψ U ∧
  (∀ a j, (U a j).IsHermitian ∧ U a j * U a j = 1)

/-- Arbitrary local unitary factors give the same commuting encoding class as reflections. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ψ : (Fin n → Fin 2) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
    ((∃ U, IsCommutingProductEncoding ψ U) ↔
      (∃ U, IsCommutingReflectionEncoding ψ U))

private lemma tensor_factors_proportional {n : ℕ}
    (X Y : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h : tensorOp X = tensorOp Y) (hne : tensorOp X ≠ 0) :
    ∀ j, ∃ c : ℂ, Y j = c • X j := by
  sorry

private lemma local_commutation_signs {n : ℕ}
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a)) :
    ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j) := by
  sorry

private lemma spectral_frame_of_local_signs {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a))
    (hs : ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j)) :
    ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  sorry

private lemma uniform_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (eig : ι → ι → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (ho : ∀ a b, ∑ x, star (c x * eig a x) * (c x * eig b x) =
      if a = b then 1 else 0) :
    ∀ x, (Fintype.card ι : ℂ) * (star (c x) * c x) = 1 := by
  sorry

private lemma flat_of_diagonal_encoding {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (hd : ∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) :
    ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1 := by
  sorry

private lemma character_orthogonality {n : ℕ} (a b : Fin n → Fin 2) :
    (∑ x : Fin n → Fin 2,
      (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) *
        (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val))) =
      if a = b then (2 ^ n : ℂ) else 0 := by
  sorry

private lemma reflection_encoding_of_flat_frame {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hR : ∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1)
    (hd : ∀ a, Fᴴ * tensorOp (R a) * F =
      diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)))
    (hf : ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1) :
    ∃ U, IsCommutingReflectionEncoding ψ U := by
  sorry

private lemma product_encoding_to_reflections {n : ℕ} (hn : 1 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U) :
    ∃ R, IsCommutingReflectionEncoding ψ R := by
  obtain ⟨F, eig, R, hF, heig, hd, hR, hRd⟩ :=
    spectral_frame_of_local_signs hn U hU.1 hU.2.1
      (local_commutation_signs U hU.1 hU.2.1)
  exact reflection_encoding_of_flat_frame ψ F hF R hR hRd
    (flat_of_diagonal_encoding ψ U hU F hF eig heig hd)

private lemma reflection_encoding_to_product {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingReflectionEncoding ψ U) : IsCommutingProductEncoding ψ U :=
  hU.1

/-- Commuting product encodings admit commuting local-reflection replacements. -/
theorem result : claim := by
  intro n hn ψ _hψ
  constructor
  · rintro ⟨U, hU⟩
    exact product_encoding_to_reflections hn ψ U hU
  · rintro ⟨U, hU⟩
    exact ⟨U, reflection_encoding_to_product ψ U hU⟩

end D5.S3.Quantum.Information.CommutingEncodingReflectionClass
