/- GID: D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction
   generality: G
   mirror-B: D5/B/S3/Analytic/Characterizations/ZeroRegionDescentObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Half-plane threshold positivity is automatically monotone only
   toward narrower regions, and strict threshold shrinkage alone does not
   imply Wang-style descent. -/

import Mathlib.Tactic

/-!
# Obstruction to formal Wang-style zero-region descent

A positivity assertion on the half-plane `1 / 2 + a < re s` automatically
propagates when the threshold increases. Propagation to a smaller threshold is
genuine additional information: an explicit real-part measurement and the
strict contraction `a / 2` refute any purely order-theoretic descent rule.
-/

/- Library-search and duplication audit trail (2026-09-02):
   * Repository searches for zero-region thresholds, Wang descent, strict
     half-plane descent, and generalized positivity-threshold propagation
     found no equivalent theorem. Receipt and digest indices had no coverage.
   * Shape searches covered predicate antitonicity, iterated strict descent,
     and counterexamples to shrinking positivity regions.
   * Searches of commits on `origin/lane/math/*` beyond `origin/dev` found no
     matching declaration. The in-flight square-order descent theorem concerns
     maximum-modulus order under rescaling, not half-plane positivity.
   * Pinned Mathlib supplies the ordered-field and complex real-part facts;
     there is no packaged theorem for this source-specific threshold predicate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Characterizations.ZeroRegionDescentObstruction

/-- Positivity of a real measurement on the open half-plane to the right of
`1 / 2 + a`. -/
def ThresholdPositivity (measurement : Complex -> Real) (a : Real) : Prop :=
  forall s, (1 / 2 : Real) + a < s.re -> 0 < measurement s

/-- The automatic implication goes toward a larger threshold, hence a
narrower half-plane. -/
theorem threshold_positivity_mono
    (measurement : Complex -> Real) {a b : Real} (hab : a <= b) :
    ThresholdPositivity measurement a ->
      ThresholdPositivity measurement b := by
  intro ha s hs
  apply ha s
  linarith

/-- Strict shrinkage of the numerical threshold does not supply the missing
analytic gain. There are an explicit measurement and strict contraction for
which positivity holds at `a = 1 / 2` but neither at zero nor after the first
descent step. -/
theorem wang_style_descent_requires_analytic_input :
    exists (measurement : Complex -> Real) (descent : Real -> Real),
      ThresholdPositivity measurement (1 / 2) ∧
        (Not (ThresholdPositivity measurement 0)) ∧
        (forall a, 0 < a -> descent a < a) ∧
        Not (ThresholdPositivity measurement (1 / 2) ->
          ThresholdPositivity measurement (descent (1 / 2))) := by
  let measurement : Complex -> Real := fun s => s.re - 1
  let descent : Real -> Real := fun a => a / 2
  have hhalf : ThresholdPositivity measurement (1 / 2) := by
    intro s hs
    dsimp [measurement]
    norm_num at hs
    linarith
  have hzero : Not (ThresholdPositivity measurement 0) := by
    intro h
    have hbad := h ((3 / 4 : Real) : Complex) (by norm_num)
    norm_num [measurement] at hbad
  have hstrict : forall a, 0 < a -> descent a < a := by
    intro a ha
    dsimp [descent]
    linarith
  have hfirst : Not (ThresholdPositivity measurement (1 / 2) ->
      ThresholdPositivity measurement (descent (1 / 2))) := by
    intro himp
    have hquarter := himp hhalf
    have hbad := hquarter ((7 / 8 : Real) : Complex) (by
      norm_num [descent])
    norm_num [measurement] at hbad
  exact ⟨measurement, descent, hhalf, hzero, hstrict, hfirst⟩

#print axioms threshold_positivity_mono
#print axioms wang_style_descent_requires_analytic_input

end D5.S3.Analytic.Characterizations.ZeroRegionDescentObstruction
