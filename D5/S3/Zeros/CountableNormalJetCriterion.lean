/- GID: D5/S3/Zeros/CountableNormalJetCriterion
   generality: I
   mirror-B: D5/B/S3/Zeros/CountableNormalJetCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous normal-jet positivity is detected at rational ordinates. -/

import D5.S3.Zeros.NormalJetFormula
import Mathlib.Topology.Algebra.Order.Archimedean

/- Library-search audit trail (2026-09-04):
   * D5 searches for countable normal-jet, rational-ordinate, and dense
     positivity criteria found `NormalJetFormula.normal_jet_formula`, but no
     theorem reducing all real ordinates to rational ordinates.
   * The related `CountableRationalFluxCriterion` detects isolated zeros with
     rational rectangles; it does not concern normal jets or extend a closed
     positivity condition from a dense subset.
   * Pinned Mathlib supplies `Rat.denseRange_cast` and
     `DenseRange.induction_on`; these are used directly below.
   * No D5 or pinned-Mathlib theorem identifies `RiemannHypothesis` with
     nonnegativity of every real normal jet. That analytic criterion is
     therefore an explicit premise rather than an unproved assertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.CountableNormalJetCriterion

open D5.S3.Zeros.NormalJetFormula

/-- A continuous real function is nonnegative everywhere exactly when it is
nonnegative at every rational point. -/
theorem continuous_nonnegative_iff_rat (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ t : ℝ, 0 ≤ f t) ↔ ∀ q : ℚ, 0 ≤ f (q : ℝ) := by
  constructor
  · intro h q
    exact h q
  · intro h t
    refine Rat.denseRange_cast.induction_on t ?_ h
    exact isClosed_le continuous_const hf

/-- Assuming the real normal-jet characterization of RH, continuity makes the
criterion countable. Its negation has a rational finite certificate whose
displayed finite sum uses only critical-xi derivatives through order `2 * m`. -/
theorem countable_normal_jet_criterion
    (realCriterion :
      RiemannHypothesis ↔ ∀ t : ℝ, ∀ m : ℕ, 0 ≤ normalJet t m)
    (normalJetContinuous :
      ∀ m : ℕ, Continuous (fun t : ℝ => normalJet t m)) :
    (RiemannHypothesis ↔
      ∀ q : ℚ, ∀ m : ℕ, 0 ≤ normalJet (q : ℝ) m) ∧
    (¬RiemannHypothesis ↔
      ∃ q : ℚ, ∃ m : ℕ,
        (∑ j ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j criticalXi (q : ℝ) *
              iteratedDeriv (2 * m - j) criticalXi (q : ℝ)) < 0) := by
  have denseCriterion :
      (∀ t : ℝ, ∀ m : ℕ, 0 ≤ normalJet t m) ↔
        ∀ q : ℚ, ∀ m : ℕ, 0 ≤ normalJet (q : ℝ) m := by
    constructor
    · intro h q m
      exact h q m
    · intro h t m
      exact (continuous_nonnegative_iff_rat
        (fun x : ℝ => normalJet x m) (normalJetContinuous m)).2
          (fun q => h q m) t
  have countableCriterion :
      RiemannHypothesis ↔
        ∀ q : ℚ, ∀ m : ℕ, 0 ≤ normalJet (q : ℝ) m :=
    realCriterion.trans denseCriterion
  refine ⟨countableCriterion, ?_⟩
  constructor
  · intro hNotRh
    have hFails : ¬ ∀ q : ℚ, ∀ m : ℕ, 0 ≤ normalJet (q : ℝ) m :=
      (not_congr countableCriterion).mp hNotRh
    push Not at hFails
    obtain ⟨q, m, hNegative⟩ := hFails
    refine ⟨q, m, ?_⟩
    rw [← (normal_jet_formula (q : ℝ)).1 m]
    exact hNegative
  · rintro ⟨q, m, hNegative⟩ hRh
    have hNonnegative := countableCriterion.mp hRh q m
    rw [← (normal_jet_formula (q : ℝ)).1 m] at hNegative
    exact (not_lt_of_ge hNonnegative) hNegative

/-- The dense criterion has a concrete positive instance. -/
example :
    (∀ t : ℝ, 0 ≤ t ^ 2) ↔ ∀ q : ℚ, 0 ≤ (q : ℝ) ^ 2 := by
  apply continuous_nonnegative_iff_rat (fun t : ℝ => t ^ 2)
  fun_prop

/-- The rational test is not vacuous: the identity function fails it at `-1`. -/
example : ¬(∀ q : ℚ, 0 ≤ (q : ℝ)) := by
  push Not
  exact ⟨-1, by norm_num⟩

#print axioms continuous_nonnegative_iff_rat
#print axioms countable_normal_jet_criterion

end D5.S3.Zeros.CountableNormalJetCriterion
