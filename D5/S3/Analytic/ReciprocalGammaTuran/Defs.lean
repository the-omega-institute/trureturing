/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: Reciprocal Gamma coefficients and the coefficient positivity clause for log concave sequences. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.ReciprocalGammaTuran.Defs

/-- Reciprocal Gamma, extended by zero at the nonpositive integers. -/
noncomputable def rgamma (x : ℝ) : ℝ := (Real.Gamma x)⁻¹

/-- Nontrivial nonnegative log concave sequences without internal zeros. -/
def AdmissibleSeq (g : ℕ → ℝ) : Prop :=
  (∃ n, g n ≠ 0) ∧ (∀ n, 0 ≤ g n) ∧
    (∀ n : ℕ, 1 ≤ n → g (n - 1) * g (n + 1) ≤ g n ^ 2) ∧
    (∀ a b c, a < b → b < c → g a ≠ 0 → g c ≠ 0 → g b ≠ 0)

/-- The Cauchy coefficient of the shifted Turanian. -/
noncomputable def turanCoeff (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    g k * g (m - k) *
      (rgamma (k + μ + α) * rgamma (m - k + μ + β) -
        rgamma (k + μ) * rgamma (m - k + μ + α + β))

/-- The coefficient positivity clause for all admissible parameter shifts. -/
def claim : Prop :=
  ∀ (g : ℕ → ℝ), AdmissibleSeq g → ∀ μ α β : ℝ,
    0 < α → 0 < β → -1 ≤ μ → 0 ≤ μ + α → 0 ≤ μ + β →
      ∀ m : ℕ, 0 < turanCoeff g μ α β m

/-- The pole convention agrees with Mathlib's Gamma function. -/
theorem rgamma_neg_nat (n : ℕ) : rgamma (-(n : ℝ)) = 0 := by
  simp [rgamma, Real.Gamma_neg_nat_eq_zero]

/-- The constant unit sequence satisfies all four sequence conditions. -/
theorem admissible_one : AdmissibleSeq (fun _ => 1) := by
  refine ⟨⟨0, by norm_num⟩, ?_, ?_, ?_⟩
  · intro n; norm_num
  · intro n hn; norm_num
  · intro a b c hab hbc ha hc; norm_num

end D5.S3.Analytic.ReciprocalGammaTuran.Defs
