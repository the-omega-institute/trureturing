/- GID: D5/S0/Asymptotics/MetallicMinimum
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetallicMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden ratio uniquely minimizes positive integer metallic values. -/

import D5.S0.Asymptotics.MetallicFamily

/- Library-search audit trail (2026-09-01):
   * Ledger, receipt, keyword, neighboring-atom, and generalized-statement
     searches found no existing theorem with both the lower bound and equality classification.
   * The repository definition `metallicValue` is reused; the related anchor theorem has
     only a private parameter-one calculation and a different conclusion.
   * Pinned Mathlib supplies `Real.goldenRatio` and `Real.sqrt_le_sqrt`, but no packaged result.
   * Installed non-Mathlib Lean packages had no matching formula or fusion-dimension result;
     remote GitHub search through NyxID was unavailable because every GitHub binding was unready.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Asymptotics.MetallicMinimum

open D5.S0.Asymptotics.MetallicFamily

/-- The parameter-one metallic value realizes the golden ratio. Among all
positive integer parameters it is the least value, and equality occurs only
at parameter one. -/
theorem metallic_value_minimal_nontrivial :
    metallicValue 1 = Real.goldenRatio ∧
      ∀ n : ℕ, 0 < n →
        Real.goldenRatio ≤ metallicValue n ∧
          (metallicValue n = Real.goldenRatio ↔ n = 1) := by
  have hone : metallicValue 1 = Real.goldenRatio := by
    rw [metallicValue, Real.goldenRatio]
    norm_num
  refine ⟨hone, ?_⟩
  intro n hn
  have hn_nat : 1 ≤ n := by omega
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
  have hradicand : (5 : ℝ) ≤ (n : ℝ) ^ 2 + 4 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hsqrt : Real.sqrt 5 ≤ Real.sqrt ((n : ℝ) ^ 2 + 4) :=
    Real.sqrt_le_sqrt hradicand
  constructor
  · rw [metallicValue, Real.goldenRatio]
    nlinarith
  · constructor
    · intro heq
      rw [metallicValue, Real.goldenRatio] at heq
      have hn_real_le : (n : ℝ) ≤ 1 := by nlinarith
      have hn_le : n ≤ 1 := by exact_mod_cast hn_real_le
      omega
    · intro heq
      subst n
      exact hone

#print axioms metallic_value_minimal_nontrivial

end D5.S0.Asymptotics.MetallicMinimum
