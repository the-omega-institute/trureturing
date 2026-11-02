/- GID: D5/S3/Quantum/Measurement/ProportionalRefinement
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ProportionalRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proportional refinements conserve quadratic budgets and contract quartic budgets. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Measurement.ProportionalRefinement

variable {κ : Type*} [Fintype κ]

/- The squared modulus is the weight carried by a proportional piece. -/
def weight (t : ℂ) : ℝ := ‖t‖ ^ 2

private theorem weight_nonneg (t : ℂ) : 0 ≤ weight t := sq_nonneg _

private theorem weight_sum_sq_le_one (t : κ → ℂ) (h : ∑ ℓ, weight (t ℓ) = 1) :
    ∑ ℓ, weight (t ℓ) ^ 2 ≤ 1 := by
  have hsq : ∑ ℓ, weight (t ℓ) ^ 2 ≤ (∑ ℓ, weight (t ℓ)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun ℓ _ => weight_nonneg (t ℓ))
  simpa [h] using hsq

/-- Quadratic quantities are conserved by a normalized proportional refinement. -/
theorem quadratic_budgets
    (t : κ → ℂ) (h : ∑ ℓ, weight (t ℓ) = 1)
    (δ τ ratio : ℝ) :
    (∑ ℓ, weight (t ℓ) * δ = δ) ∧
      (∑ ℓ, weight (t ℓ) * τ = τ) ∧
      (∑ ℓ, weight (t ℓ) * ratio = ratio) := by
  constructor
  · rw [← Finset.sum_mul, h, one_mul]
  constructor
  · rw [← Finset.sum_mul, h, one_mul]
  · rw [← Finset.sum_mul, h, one_mul]

/-- The concrete squared distance budget `min (p,q)` is also conserved. -/
theorem min_coordinate_budget_preserved
    (t : κ → ℂ) (h : ∑ ℓ, weight (t ℓ) = 1)
    (p q : ℝ) :
    ∑ ℓ, min (weight (t ℓ) * p) (weight (t ℓ) * q) = min p q := by
  calc
    ∑ ℓ, min (weight (t ℓ) * p) (weight (t ℓ) * q) =
        ∑ ℓ, weight (t ℓ) * min p q := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          simpa [mul_comm] using
            (min_mul_of_nonneg p q (weight_nonneg (t ℓ))).symm
    _ = (∑ ℓ, weight (t ℓ)) * min p q := by rw [Finset.sum_mul]
    _ = min p q := by rw [h, one_mul]
/-- The two quartic budgets are multiplied by the same fourth-power weight. -/
theorem quartic_budgets
    (t : κ → ℂ) (h : ∑ ℓ, weight (t ℓ) = 1)
    (p q d₄ : ℝ) :
    (∑ ℓ, (weight (t ℓ) * p) * (weight (t ℓ) * q) =
        (∑ ℓ, weight (t ℓ) ^ 2) * (p * q)) ∧
      (∑ ℓ, (weight (t ℓ) ^ 2) * d₄ =
        (∑ ℓ, weight (t ℓ) ^ 2) * d₄) ∧
      ∑ ℓ, weight (t ℓ) ^ 2 ≤ 1 := by
  constructor
  · calc
      ∑ ℓ, (weight (t ℓ) * p) * (weight (t ℓ) * q) =
          ∑ ℓ, (weight (t ℓ) ^ 2) * (p * q) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            ring
      _ = (∑ ℓ, weight (t ℓ) ^ 2) * (p * q) := by rw [Finset.sum_mul]
  · constructor
    · rw [Finset.sum_mul]
    · exact weight_sum_sq_le_one t h

/- The same calculation works for a rectangular Kraus operator. -/
theorem actual_channel_preserved_rectangular
    {out inp : Type*} [Fintype inp] (t : κ → ℂ)
    (h : ∑ ℓ, weight (t ℓ) = 1)
    (K : Matrix out inp ℂ) (X : Matrix inp inp ℂ) :
    ∑ ℓ, (t ℓ • K) * X * (t ℓ • K)ᴴ = K * X * Kᴴ := by
  calc
    ∑ ℓ, (t ℓ • K) * X * (t ℓ • K)ᴴ =
        ∑ ℓ, weight (t ℓ) • (K * X * Kᴴ) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          have hscalar : (starRingEnd ℂ) (t ℓ) * t ℓ =
              (weight (t ℓ) : ℂ) := by
            have hnorm : Complex.normSq (t ℓ) = weight (t ℓ) := by
              simpa [weight] using (Complex.sq_norm (t ℓ)).symm
            rw [mul_comm, Complex.mul_conj, hnorm]
          simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul, hscalar]
    _ = (∑ ℓ, weight (t ℓ)) • (K * X * Kᴴ) := by
      rw [Finset.sum_smul]
    _ = K * X * Kᴴ := by rw [h, one_smul]

/-- Proportional pieces preserve the rank-one completeness contribution. -/
def outer {m : Type*} (b : m → ℂ) : Matrix m m ℂ :=
  fun i j => b i * (starRingEnd ℂ) (b j)

theorem completeness_preserved
    {m : Type*} (t : κ → ℂ) (h : ∑ ℓ, weight (t ℓ) = 1)
    (b : m → ℂ) :
    ∀ i j, ∑ ℓ, (t ℓ * b i) * (starRingEnd ℂ) (t ℓ * b j) =
      b i * (starRingEnd ℂ) (b j) := by
  intro i j
  calc
    ∑ ℓ, (t ℓ * b i) * (starRingEnd ℂ) (t ℓ * b j) =
        ∑ ℓ, ((starRingEnd ℂ) (t ℓ) * t ℓ) *
          (b i * (starRingEnd ℂ) (b j)) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            simp only [map_mul]
            ring
    _ = ∑ ℓ, weight (t ℓ) * (b i * (starRingEnd ℂ) (b j)) := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hscalar : (starRingEnd ℂ) (t ℓ) * t ℓ = (weight (t ℓ) : ℂ) := by
        have hnorm : Complex.normSq (t ℓ) = weight (t ℓ) := by
          simpa [weight] using (Complex.sq_norm (t ℓ)).symm
        rw [mul_comm, Complex.mul_conj, hnorm]
      rw [hscalar]
    _ = (∑ ℓ, weight (t ℓ)) * (b i * (starRingEnd ℂ) (b j)) := by
      have hcast : (↑(∑ ℓ, weight (t ℓ)) : ℂ) =
          ∑ ℓ, (weight (t ℓ) : ℂ) := by
        simpa using
          (map_sum Complex.ofRealHom (fun ℓ : κ => weight (t ℓ)) Finset.univ)
      rw [hcast, Finset.sum_mul]
    _ = b i * (starRingEnd ℂ) (b j) := by
      rw [h]
      norm_num

end D5.S3.Quantum.Measurement.ProportionalRefinement
