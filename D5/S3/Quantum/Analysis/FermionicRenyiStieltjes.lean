/- GID: D5/S3/Quantum/Analysis/FermionicRenyiStieltjes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FermionicRenyiStieltjes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive Stieltjes representation for the fermionic Gaussian Renyi function. -/

import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

/-! The sum of two powers is obtained by dividing the difference of their squares
by their difference. Applying the bosonic representation at orders `2 * α` and `α`
therefore gives the fermionic representation, including the pure-mode endpoint. -/

namespace D5.S3.Quantum.Analysis.FermionicRenyiStieltjes

open Real Set MeasureTheory

noncomputable section

/-- Single-mode fermionic Gaussian Renyi entropy. -/
def fermionicRenyiFunction (α σ : ℝ) : ℝ :=
  (1 - α)⁻¹ * Real.log (((1 + σ) / 2) ^ α + ((1 - σ) / 2) ^ α)

/-- Density of the positive logarithmic representation on `(0, 1)`. -/
def fermionicWeight (α u : ℝ) : ℝ :=
  (2 * α * Real.sin (Real.pi * α) * (1 - u ^ 2) ^ (α - 1)) /
    (Real.pi * (1 - α) * ((1 + u) ^ (2 * α) + (1 - u) ^ (2 * α) +
      2 * (1 - u ^ 2) ^ α * Real.cos (Real.pi * α)))

private lemma weight_denominator_pos {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 < (1 + u) ^ (2 * α) + (1 - u) ^ (2 * α) +
      2 * (1 - u ^ 2) ^ α * Real.cos (Real.pi * α) := by
  sorry

/-- The fermionic density is strictly positive throughout `[0, 1)`. -/
theorem weight_pos {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < fermionicWeight α u := by
  sorry

private def scaledWeight (β u : ℝ) : ℝ :=
  (β - 1) * BosonicRenyiStieltjes.renyiWeight β u

private lemma weight_decomposition {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu : u ∈ Ioo 0 1) :
    fermionicWeight α u =
      (scaledWeight (2 * α) u - scaledWeight α u) / (1 - α) := by
  sorry

private lemma scaled_weight_integrable {β : ℝ} (hb0 : 0 < β) (hb2 : β < 2) :
    IntegrableOn (scaledWeight β) (Ioo 0 1) := by
  sorry

private lemma scaled_weight_mass {β : ℝ} (hb0 : 0 < β) (hb2 : β < 2) :
    (∫ u in Ioo (0 : ℝ) 1, scaledWeight β u) = (β - 1) / 2 := by
  sorry

/-- The fermionic density is integrable on `(0, 1)`. -/
theorem weight_integrable {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    IntegrableOn (fermionicWeight α) (Ioo 0 1) := by
  sorry

private lemma scaled_stieltjes {β s : ℝ} (hb0 : 0 < β) (hb2 : β < 2)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun u => scaledWeight β u * Real.log (1 - u ^ 2 * s ^ 2))
      (Ioo 0 1) ∧
    Real.log (((1 + s) / 2) ^ β - ((1 - s) / 2) ^ β) =
      Real.log β + Real.log s - (β - 1) * Real.log 2 +
        ∫ u in Ioo (0 : ℝ) 1, scaledWeight β u * Real.log (1 - u ^ 2 * s ^ 2) := by
  sorry

private lemma representation_pos {α s : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun u => fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2))
      (Ioo 0 1) ∧
    fermionicRenyiFunction α s = Real.log 2 +
      ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2) := by
  sorry

/-- Positive logarithmic Stieltjes representation, including both pure-mode endpoints. -/
theorem stieltjes_representation {α σ : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hs : |σ| ≤ 1) :
    IntegrableOn (fun u => fermionicWeight α u * Real.log (1 - u ^ 2 * σ ^ 2))
      (Ioo 0 1) ∧
    fermionicRenyiFunction α σ = Real.log 2 +
      ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * Real.log (1 - u ^ 2 * σ ^ 2) := by
  sorry

end

end D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
