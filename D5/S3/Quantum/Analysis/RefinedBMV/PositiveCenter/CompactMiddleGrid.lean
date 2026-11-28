/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleGrid
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Assemble all middle-gap boxes into the original kernel sign. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-! The four lower-coordinate intervals and seven gap intervals used in the sign proof. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

private def lowerU : Fin 4 → ℚ := ![1 / 2, 1, 2, 3]
private def upperU : Fin 4 → ℚ := ![1, 2, 3, 4]
private def lowerD : Fin 7 → ℚ := ![1, 5 / 4, 3 / 2, 2, 5 / 2, 3, 7 / 2]
private def upperD : Fin 7 → ℚ := ![5 / 4, 3 / 2, 2, 5 / 2, 3, 7 / 2, 4]

def middleGridBox (i : Fin 4) (j : Fin 7) : CompactMiddleBox :=
  CompactMiddleBox.ofIntervals (lowerU i) (upperU i) (lowerD j) (upperD j)

private theorem cover_u {u : ℝ} (hl : 1 / 2 ≤ u) (hr : u ≤ 4) :
    ∃ i : Fin 4, (lowerU i : ℝ) ≤ u ∧ u ≤ (upperU i : ℝ) := by
  by_cases h₁ : u ≤ 1
  · use 0
    norm_num [lowerU, upperU]
    exact ⟨hl, h₁⟩
  by_cases h₂ : u ≤ 2
  · use 1
    norm_num [lowerU, upperU]
    exact ⟨le_of_not_ge h₁, h₂⟩
  by_cases h₃ : u ≤ 3
  · use 2
    norm_num [lowerU, upperU]
    exact ⟨le_of_not_ge h₂, h₃⟩
  use 3
  norm_num [lowerU, upperU]
  exact ⟨le_of_not_ge h₃, hr⟩

private theorem cover_d {d : ℝ} (hl : 1 ≤ d) (hr : d ≤ 4) :
    ∃ j : Fin 7, (lowerD j : ℝ) ≤ d ∧ d ≤ (upperD j : ℝ) := by
  by_cases h₁ : d ≤ 5 / 4
  · use 0
    norm_num [lowerD, upperD]
    exact ⟨hl, h₁⟩
  by_cases h₂ : d ≤ 3 / 2
  · use 1
    norm_num [lowerD, upperD]
    exact ⟨le_of_not_ge h₁, h₂⟩
  by_cases h₃ : d ≤ 2
  · use 2
    norm_num [lowerD, upperD]
    exact ⟨le_of_not_ge h₂, h₃⟩
  by_cases h₄ : d ≤ 5 / 2
  · use 3
    norm_num [lowerD, upperD]
    exact ⟨le_of_not_ge h₃, h₄⟩
  by_cases h₅ : d ≤ 3
  · use 4
    norm_num [lowerD, upperD]
    exact ⟨le_of_not_ge h₄, h₅⟩
  by_cases h₆ : d ≤ 7 / 2
  · use 5
    norm_num [lowerD, upperD]
    exact ⟨le_of_not_ge h₅, h₆⟩
  use 6
  norm_num [lowerD, upperD]
  exact ⟨le_of_not_ge h₆, hr⟩

/-- The middle-gap sign follows from the rational checks on the twenty-eight boxes. -/
theorem logKernel_mixed_neg_of_middle_grid_checks {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4) (hd₀ : 1 ≤ v - u) (hd₁ : v - u ≤ 4)
    (checks : ∀ i j, (middleGridBox i j).Checks ∧ ∀ a b, (middleGridBox i j).EndpointTests a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨i, hi₀, hi₁⟩ := cover_u hu₀ hu₁
  obtain ⟨j, hj₀, hj₁⟩ := cover_d hd₀ hd₁
  have hi : lowerU i < upperU i := by fin_cases i <;> norm_num [lowerU, upperU]
  have hj : lowerD j < upperD j := by fin_cases j <;> norm_num [lowerD, upperD]
  obtain ⟨s, t, z, hb, hU, hD, hH⟩ := CompactMiddleBox.boxCoordinates hp hi hj hi₀ hi₁ hj₀ hj₁
  exact (middleGridBox i j).mixed_neg_of_checks hp hu₀ hu₁ hd₀ hb hU hD hH
    (checks i j).1 (checks i j).2

end RefinedBMV.PositiveCenter.CompactTaylorModel
