/- GID: D5/S0/Diagonal/Probability/LinearMarginConcentration
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/LinearMarginConcentration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diagonal listings satisfy the corrected linear-margin bound and typical-density limit. -/

import D5.S0.Diagonal.TypicalDensity

/- Library-search audit trail (2026-08-25):
   * Exact repository hits `linear_margin_bound`,
     `linear_margin_bound_tendsto_zero`,
     `margin_failure_probability_tendsto_zero`, and
     `typical_density_failure_probability_tendsto_zero` prove the four public
     clauses and are applied directly.
   * No frozen declaration packages all four clauses of the source theorem, so
     binding any one hit would under-cover the named conjunction.
   * Pinned Mathlib contains binomial distributions and generic moment-generating
     function Chernoff bounds, but no theorem on the repository's canonical
     diagonal-listing Hamming-distance carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

universe u v

namespace D5.S0.Diagonal.Probability.LinearMarginConcentration

open MarginBound MarginVanishing TypicalDensity

/-- The corrected finite KL bound, its vanishing limit, asymptotically linear escape,
and concentration of the minimum-distance density at the nonzero-choice density. -/
theorem linear_margin_concentration {Y : Type u} [Fintype Y] (f : Y → Y) (alpha : ℝ)
    (hY : 2 ≤ Fintype.card Y) (halpha : 0 < alpha)
    (halpha_lt : alpha < ((Fintype.card Y : ℝ) - 1) / Fintype.card Y) :
    (∀ {A : Type v} [Fintype A],
        2 ≤ Fintype.card A →
        alpha * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) - 1) <
            ((Fintype.card Y : ℝ) - 1) / Fintype.card Y →
        marginFailureProbability (A := A) f alpha ≤
          linearMarginBound (Fintype.card Y) alpha (Fintype.card A)) ∧
      Tendsto (linearMarginBound (Fintype.card Y) alpha) atTop (nhds 0) ∧
      Tendsto (fun a : ℕ => marginFailureProbability (A := Fin a) f alpha)
        atTop (nhds 0) ∧
      ∀ alphaHi : ℝ,
        ((Fintype.card Y : ℝ) - 1) / Fintype.card Y < alphaHi →
        alphaHi < 1 →
        Tendsto
          (fun a : ℕ =>
            typicalDensityFailureProbability (A := Fin a) f alpha alphaHi)
          atTop (nhds 0) := by
  refine ⟨?_, linear_margin_bound_tendsto_zero (Fintype.card Y) alpha hY halpha halpha_lt,
    margin_failure_probability_tendsto_zero f alpha hY halpha halpha_lt, ?_⟩
  · intro A inst hA hqp
    simpa only [linearMarginBound] using
      linear_margin_bound (A := A) f alpha hA hY halpha hqp
  · intro alphaHi halphaHi_gt halphaHi_one
    exact typical_density_failure_probability_tendsto_zero
      f alpha alphaHi hY halpha halpha_lt halphaHi_gt halphaHi_one

/- The source restrictions are jointly satisfiable on a two-point value carrier. -/
example :
    2 ≤ Fintype.card Bool ∧
      0 < (1 / 4 : ℝ) ∧
        (1 / 4 : ℝ) < ((Fintype.card Bool : ℝ) - 1) / Fintype.card Bool := by
  norm_num

/- The finite value carrier is inhabited. -/
example : Bool := false

#print axioms linear_margin_concentration

end D5.S0.Diagonal.Probability.LinearMarginConcentration
