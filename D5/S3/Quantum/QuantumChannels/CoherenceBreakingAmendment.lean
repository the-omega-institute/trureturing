/- GID: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: One permutation-phase unitary amends every incoherent channel of index at least two. -/

import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation

/-! # Amendment of incoherent channels with finite coherence-breaking index -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel)

namespace D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment

/-- Each Kraus column has support in at most one basis direction. -/
def IsIncoherentKraus {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ s j, ∃ k, ∀ i, i ≠ k → K s i j = 0

/-- The channel associated to a finite Kraus family. -/
def channel {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ s, K s * X * (K s)ᴴ

/-- Every density matrix is mapped to a diagonal matrix. -/
def IsCoherenceBreaking {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ ρ, ρ.PosSemidef → ρ.trace = 1 → ∀ i j, i ≠ j → Φ ρ i j = 0

/-- Conjugation by the specified matrix. -/
def unitaryConj {d : ℕ} (U X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := U * X * Uᴴ

/-- The same conjugation is inserted between every pair of consecutive channels. -/
def amended {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :=
  channel K ∘ (unitaryConj U ∘ channel K)^[n - 1]

/-- The finite-index amendment conjecture, with a single unitary in every slot. -/
def claim : Prop :=
  ∀ (d r : ℕ) (K : Fin r → Matrix (Fin d) (Fin d) ℂ),
    IsKrausChannel K → IsIncoherentKraus K →
    ∀ n : ℕ, 2 ≤ n → IsCoherenceBreaking (channel K)^[n] →
      (∀ k, 1 ≤ k → k < n → ¬ IsCoherenceBreaking (channel K)^[k]) →
      ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ¬ IsCoherenceBreaking (amended K U n)

private def offDiag {d : ℕ} :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) where
  toFun X i j := if i = j then 0 else X i j
  map_add' X Y := by
    ext i j
    change (if i = j then 0 else X i j + Y i j) =
      (if i = j then 0 else X i j) + (if i = j then 0 else Y i j)
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    change (if i = j then 0 else c * X i j) =
      c * (if i = j then 0 else X i j)
    by_cases h : i = j <;> simp [h]

private def conjugation {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) where
  toFun := unitaryConj U
  map_add' X Y := by simp only [unitaryConj.eq_1, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [unitaryConj.eq_1, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

private def channelLinear {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) where
  toFun := channel K
  map_add' X Y := by
    simp only [channel.eq_1, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [channel.eq_1, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
      RingHom.id_apply]

private def residual {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) := offDiag ∘ₗ channelLinear K

/-- Every incoherent channel with finite coherence-breaking index at least two is amendable. -/
theorem result : claim := by
  sorry

end D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
