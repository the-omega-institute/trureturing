/- GID: D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim; result=D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result; claim=D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim
   digest: An extreme eight-outcome POVM on complex seven-space has ranks (3,3,2,2,2,2,2,2). -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix

/-- Extremality in the convex set of finite POVMs. -/
def IsExtreme {n : ℕ} (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ) : Prop :=
  IsPOVM M ∧
    ∀ A B : Fin n → Matrix (Fin 7) (Fin 7) ℂ,
      IsPOVM A → IsPOVM B →
      (∀ j, M j = (1 / 2 : ℂ) • (A j + B j)) → A = M ∧ B = M

/-- The non-rank-one part of the rank vector of a POVM. -/
def bigRanks {n : ℕ} (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ) : Multiset ℕ :=
  (Finset.univ.val.map (fun j => (M j).rank)).filter (fun r => 2 ≤ r)

def claim : Prop :=
  ∀ (n : ℕ) (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ),
    IsPOVM M → IsExtreme M →
      bigRanks M ≠ ({3, 3, 2, 2, 2, 2, 2, 2} : Multiset ℕ)

private def vector (a₀ a₁ a₂ f₀ f₁ f₂ g : ℂ) : Fin 7 → ℂ :=
  ![a₀, a₁, a₂, f₀, f₁, f₂, g]

private def blocks : Fin 8 → Finset (Fin 7 → ℂ) := ![
  {vector 1 0 0 0 0 0 0, vector 0 1 0 0 0 0 0, vector 0 0 1 0 0 0 0},
  {vector 0 0 0 1 0 0 0, vector 0 0 0 0 1 0 0, vector 0 0 0 0 0 1 0},
  {vector 1 0 0 1 0 0 0, vector 0 1 0 0 1 0 0},
  {vector 1 0 0 Complex.I 0 0 0, vector 0 1 0 0 Complex.I 0 0},
  {vector 1 0 0 1 0 0 1, vector 0 0 1 0 0 1 0},
  {vector 1 0 0 Complex.I 0 0 1, vector 0 0 1 0 0 Complex.I 0},
  {vector 0 1 0 0 1 0 1, vector 0 0 1 0 0 1 1},
  {vector 0 1 0 0 Complex.I 0 1, vector 0 0 1 0 0 Complex.I 1}
]

private def effect (j : Fin 8) : Matrix (Fin 7) (Fin 7) ℂ :=
  ∑ b : blocks j, Matrix.vecMulVec b.1 (star b.1)

private def frame : Matrix (Fin 7) (Fin 7) ℂ := ∑ j, effect j

private theorem frame_posDef : frame.PosDef := by sorry

private theorem normalizer_exists :
    ∃ R : Matrix (Fin 7) (Fin 7) ℂ, IsUnit R.det ∧ R * frame * Rᴴ = 1 := by
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.mp
    frame_posDef.isStrictlyPositive) with ⟨b, hb, hframe⟩
  refine ⟨b⁻¹, ?_, ?_⟩
  · exact Matrix.isUnit_iff_isUnit_det _ |>.mp (Matrix.isUnit_nonsing_inv_iff.mpr hb)
  · rw [hframe, Matrix.conjTranspose_nonsing_inv]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left]
    · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv]
      exact Matrix.one_mul _
    · exact hb.det.isUnit

private def normalizer : Matrix (Fin 7) (Fin 7) ℂ :=
  Classical.choose normalizer_exists

private theorem normalizer_unit : IsUnit normalizer.det := by
  exact (Classical.choose_spec normalizer_exists).1

private theorem normalizer_identity : normalizer * frame * normalizerᴴ = 1 := by
  exact (Classical.choose_spec normalizer_exists).2

private def witness (j : Fin 8) : Matrix (Fin 7) (Fin 7) ℂ :=
  normalizer * effect j * normalizerᴴ

private theorem effect_posSemidef (j : Fin 8) : (effect j).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro b hb
  exact Matrix.posSemidef_vecMulVec_self_star b.1

private theorem witness_posSemidef (j : Fin 8) : (witness j).PosSemidef := by
  exact (effect_posSemidef j).mul_mul_conjTranspose_same normalizer

private theorem witness_sum : ∑ j, witness j = 1 := by
  simp only [witness]
  simp_rw [Matrix.mul_assoc]
  rw [← Matrix.mul_sum, ← Matrix.sum_mul, show (∑ j, effect j) = frame from rfl]
  simpa only [Matrix.mul_assoc] using normalizer_identity

private theorem witness_povm : IsPOVM witness := by
  exact ⟨witness_posSemidef, witness_sum⟩

private theorem effect_rank (j : Fin 8) : (effect j).rank = (blocks j).card := by sorry

private theorem witness_rank (j : Fin 8) : (witness j).rank = (effect j).rank := by
  have hstar : IsUnit normalizerᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact normalizer_unit.star
  rw [witness, Matrix.mul_assoc,
    Matrix.rank_mul_eq_right_of_isUnit_det normalizer (effect j * normalizerᴴ)
      normalizer_unit,
    Matrix.rank_mul_eq_left_of_isUnit_det normalizerᴴ (effect j) hstar]

private theorem witness_bigRanks :
    bigRanks witness = ({3, 3, 2, 2, 2, 2, 2, 2} : Multiset ℕ) := by sorry

private theorem within_block_product_independent :
    LinearIndependent ℂ
      (fun p : Σ j : Fin 8, (blocks j × blocks j) =>
        Matrix.vecMulVec p.2.1.1 (star p.2.2.1)) := by sorry

private theorem normalized_product_independent :
    LinearIndependent ℂ
      (fun p : Σ j : Fin 8, (blocks j × blocks j) =>
        normalizer * Matrix.vecMulVec p.2.1.1 (star p.2.2.1) * normalizerᴴ) := by sorry

private theorem decomposition_eq_of_product_independence
    (A B : Fin 8 → Matrix (Fin 7) (Fin 7) ℂ)
    (hA : IsPOVM A) (hB : IsPOVM B)
    (hmid : ∀ j, witness j = (1 / 2 : ℂ) • (A j + B j)) :
    A = witness ∧ B = witness := by sorry

private theorem witness_extreme : IsExtreme witness := by sorry

theorem result : ¬ claim := by
  intro h
  exact h 8 witness witness_povm witness_extreme witness_bigRanks

end D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix
