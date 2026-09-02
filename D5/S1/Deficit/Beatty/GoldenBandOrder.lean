/- GID: D5/S1/Deficit/Beatty/GoldenBandOrder
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/GoldenBandOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The structural zero and pole lie strictly inside the golden band. -/

import D5.S1.Deficit.Beatty.GoldenObserverRoute

/- Library-search audit trail (2026-09-02):
   * Exact D5 searches for `golden_band_order`, the three-inequality chain,
     and its two interior comparisons found no theorem covering this claim.
   * The sole exact lower-bound expression hit was the frozen Hearts premise;
     it does not state the conjunction and is not imported here.
   * Pinned Mathlib supplies `Real.one_lt_goldenRatio`,
     `Real.goldenRatio_lt_two`, `one_div_lt_one_div_of_lt`, and `pow_pos`.
     The theorem below is the atom-specific assembly of those order facts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.GoldenBandOrder

open D5.S1.Deficit.Beatty.GoldenObserverRoute

/- These are the only additional constants needed by the theorem. Their
definitions are transcribed verbatim from `D5/X_Frontier/Hearts.lean`; `phi`
is imported from `GoldenObserverRoute`, so this module creates no second copy. -/

/-- The structural pole contributed by the cubic golden rescaling. -/
noncomputable def structuralPole : ℝ := 1 / phi ^ 3

/-- The structural zero on the pulled-back critical line. -/
noncomputable def structuralZero : ℝ := 1 / (2 * phi ^ 2)

/-- The structural zero and pole lie in strict order inside the golden band. -/
theorem golden_band_order :
    1 / (2 * phi ^ 3) < structuralZero ∧
    structuralZero < structuralPole ∧
    structuralPole < 1 / phi ^ 2 := by
  have h1 : (1 : ℝ) < phi := by
    change (1 : ℝ) < Real.goldenRatio
    exact Real.one_lt_goldenRatio
  have h2 : phi < (2 : ℝ) := by
    change Real.goldenRatio < (2 : ℝ)
    exact Real.goldenRatio_lt_two
  have hp : (0 : ℝ) < phi := lt_trans one_pos h1
  have hp2 : (0 : ℝ) < phi ^ 2 := pow_pos hp 2
  have hp3 : (0 : ℝ) < phi ^ 3 := pow_pos hp 3
  unfold structuralZero structuralPole
  refine ⟨?_, ?_, ?_⟩
  · apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  · apply one_div_lt_one_div_of_lt hp3
    nlinarith
  · apply one_div_lt_one_div_of_lt hp2
    nlinarith

-- The theorem has no hypotheses; `True.intro` witnesses that empty premise.
example : True := True.intro

-- The real domain named by the atom is inhabited independently of the result.
example : ℝ := 0

#print axioms golden_band_order

end D5.S1.Deficit.Beatty.GoldenBandOrder
