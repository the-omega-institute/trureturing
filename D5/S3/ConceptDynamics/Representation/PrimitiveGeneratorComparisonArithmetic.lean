/- GID: D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational arithmetic core of the primitive-generator versus double-anchor count comparison. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic

/- The source count formulas are interpreted in `ℚ`, which preserves their order and
   makes the arithmetic core independent of a particular integer division encoding. -/
def generatorComparisonCount (m d : ℚ) : ℚ :=
  m * d - m * (m + 1) / 2

def pairComparisonCount (d : ℚ) : ℚ := 2 * d

private lemma comparison_factor_nonneg {n m d : ℚ}
    (hn : 4 ≤ n) (hmn2 : m ≤ n + 2)
    (hd : n * (n + 1) / 2 ≤ d) :
    0 ≤ d - (m + n + 1) / 2 := by
  nlinarith

/- The two count expressions satisfy both lower bounds in Theorem 240.1, and the
   resulting difference is strictly positive. The hypotheses include the prefix
   bound `m ≤ n + 2` from Definition 231.1. -/
theorem explicit_comparison_strict_reduction {n m d : ℚ}
    (hn : 4 ≤ n) (hmn : n ≤ m) (hmn2 : m ≤ n + 2)
    (hd : n * (n + 1) / 2 ≤ d) :
    (n - 2) * d - n * (n + 1) / 2 ≤
        generatorComparisonCount m d - pairComparisonCount d ∧
      n * (n + 1) * (n - 3) / 2 ≤
        generatorComparisonCount m d - pairComparisonCount d ∧
      0 < generatorComparisonCount m d - pairComparisonCount d := by
  dsimp [generatorComparisonCount, pairComparisonCount]
  have hf := comparison_factor_nonneg hn hmn2 hd
  have hprod : 0 ≤ (m - n) * (d - (m + n + 1) / 2) :=
    mul_nonneg (sub_nonneg.mpr hmn) hf
  constructor
  · nlinarith
  constructor
  · have hbase : n * (n + 1) * (n - 3) / 2 ≤
        (n - 2) * d - n * (n + 1) / 2 := by
      nlinarith
    nlinarith
  · nlinarith

#print axioms explicit_comparison_strict_reduction

end D5.S3.ConceptDynamics.Representation.PrimitiveGeneratorComparisonArithmetic
