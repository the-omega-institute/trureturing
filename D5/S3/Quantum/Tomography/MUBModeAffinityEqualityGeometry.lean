/- GID: D5/S3/Quantum/Tomography/MUBModeAffinityEqualityGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeAffinityEqualityGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonnegative three-mode probability vector of collision two-thirds has a unique coordinate strictly above two-thirds. -/

import D5.S3.Quantum.Tomography.MUBModeAffinityEquality

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeAffinityEqualityGeometry

open D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

/-- Collision `2 / 3` forces at least one mode weight strictly above `2 / 3`.
The proof uses the equality case of the elementary bound
`p_k^2 ≤ (2 / 3) p_k` under the contrary hypothesis. -/
theorem exists_mode_gt_two_thirds
    (p : Fin 3 → ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hsum : p 0 + p 1 + p 2 = 1)
    (hcollision : threeModeCollision p = (2 / 3 : ℝ)) :
    (2 / 3 : ℝ) < p 0 ∨
      (2 / 3 : ℝ) < p 1 ∨
      (2 / 3 : ℝ) < p 2 := by
  by_contra h
  simp only [not_or, not_lt] at h
  have h0nonneg :
      0 ≤ p 0 * ((2 / 3 : ℝ) - p 0) :=
    mul_nonneg (hp 0) (sub_nonneg.mpr h.1)
  have h1nonneg :
      0 ≤ p 1 * ((2 / 3 : ℝ) - p 1) :=
    mul_nonneg (hp 1) (sub_nonneg.mpr h.2.1)
  have h2nonneg :
      0 ≤ p 2 * ((2 / 3 : ℝ) - p 2) :=
    mul_nonneg (hp 2) (sub_nonneg.mpr h.2.2)
  have htotal :
      p 0 * ((2 / 3 : ℝ) - p 0) +
        p 1 * ((2 / 3 : ℝ) - p 1) +
        p 2 * ((2 / 3 : ℝ) - p 2) = 0 := by
    unfold threeModeCollision at hcollision
    nlinarith
  have h0zero : p 0 * ((2 / 3 : ℝ) - p 0) = 0 := by
    nlinarith
  have h1zero : p 1 * ((2 / 3 : ℝ) - p 1) = 0 := by
    nlinarith
  have h2zero : p 2 * ((2 / 3 : ℝ) - p 2) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp h0zero with h00 | h02
  · rcases mul_eq_zero.mp h1zero with h10 | h12
    · rcases mul_eq_zero.mp h2zero with h20 | h22 <;> nlinarith
    · rcases mul_eq_zero.mp h2zero with h20 | h22 <;> nlinarith
  · rcases mul_eq_zero.mp h1zero with h10 | h12
    · rcases mul_eq_zero.mp h2zero with h20 | h22 <;> nlinarith
    · rcases mul_eq_zero.mp h2zero with h20 | h22 <;> nlinarith

/-- At most one coordinate of a probability triple can exceed `2 / 3`. -/
theorem mode_gt_two_thirds_unique
    (p : Fin 3 → ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hsum : p 0 + p 1 + p 2 = 1)
    {i j : Fin 3}
    (hi : (2 / 3 : ℝ) < p i)
    (hj : (2 / 3 : ℝ) < p j) :
    i = j := by
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso; nlinarith [hp 2]
  · exfalso; nlinarith [hp 1]
  · exfalso; nlinarith [hp 2]
  · rfl
  · exfalso; nlinarith [hp 0]
  · exfalso; nlinarith [hp 1]
  · exfalso; nlinarith [hp 0]
  · rfl

/-- A collision-equality probability triple has a unique dominant mode. -/
theorem existsUnique_mode_gt_two_thirds
    (p : Fin 3 → ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hsum : p 0 + p 1 + p 2 = 1)
    (hcollision : threeModeCollision p = (2 / 3 : ℝ)) :
    ∃! k : Fin 3, (2 / 3 : ℝ) < p k := by
  rcases exists_mode_gt_two_thirds p hp hsum hcollision with h0 | h1 | h2
  · refine ⟨0, h0, ?_⟩
    intro j hj
    exact mode_gt_two_thirds_unique p hp hsum h0 hj
  · refine ⟨1, h1, ?_⟩
    intro j hj
    exact (mode_gt_two_thirds_unique p hp hsum h1 hj).symm
  · refine ⟨2, h2, ?_⟩
    intro j hj
    exact (mode_gt_two_thirds_unique p hp hsum h2 hj).symm

#print axioms exists_mode_gt_two_thirds
#print axioms mode_gt_two_thirds_unique
#print axioms existsUnique_mode_gt_two_thirds

end D5.S3.Quantum.Tomography.MUBModeAffinityEqualityGeometry
