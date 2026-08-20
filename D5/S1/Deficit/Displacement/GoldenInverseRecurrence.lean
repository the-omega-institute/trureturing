/- GID: D5/S1/Deficit/Displacement/GoldenInverseRecurrence
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Inverse golden-ratio quadratic identity and its Nat-indexed recurrence. -/

import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/-
Search receipt (2026-08-18, pinned sources):
* Pinned mathlib was searched throughout `.lake/packages/mathlib/Mathlib` for inverse-golden,
  golden-ratio inverse, quadratic, and indexed-power forms.  The inspected source
  `.lake/packages/mathlib/Mathlib/NumberTheory/Real/GoldenRatio.lean:48` gives
  `Real.inv_goldenRatio`; lines 79, 83, and 87 give the existing direct-φ power
  recurrence, `Real.goldenRatio_sq`, and `Real.goldenConj_sq`, respectively; lines
  90 and 96 give positivity and the `1 < Real.goldenRatio` bound.  No searched
  mathlib declaration states either the inverse quadratic identity or its indexed
  inverse-power recurrence.
* The repository was searched throughout `D5` for the target expressions and names.
  The five inspected private copies are
  `D5/S1/Words/ZeckendorfBeattyBridge.lean:21-24`,
  `D5/S1/Words/Powers/GoldenCubePeriodsSupport.lean:26-29`,
  `D5/S1/Deficit/ZeckendorfDisplacementReading.lean:18-21`,
  `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.lean:20-23`, and
  `D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.lean:17-20`.
  Those are private duplicates.  The repository search found no public declaration
  of the inverse identity or the indexed recurrence.  It did find private
  same-family derivations, including the generic recurrence at
  `D5/S1/Words/Powers/GoldenCubePeriodsSupport.lean:31-35` and the equivalent
  inverse-power subtraction lemma at `:277-288`; these are private and were not
  counted as public declarations.
* The pinned Lean core at
  `/Users/lexa/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean` was searched
  for the same tokens.  It contains only generic inverse notation at
  `Init/Prelude.lean:1543-1547`, and no golden-ratio candidate.
The inspected candidate list above is NOT claimed to be exhaustive.
-/

namespace D5.S1.Deficit.Displacement.GoldenInverseRecurrence

theorem inv_goldenRatio_sq_add_inv_goldenRatio :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

theorem inv_goldenRatio_pow_add_pow_succ (n : Nat) :
    Real.goldenRatio⁻¹ ^ (n + 2) + Real.goldenRatio⁻¹ ^ (n + 1) =
      Real.goldenRatio⁻¹ ^ n := by
  calc
    Real.goldenRatio⁻¹ ^ (n + 2) + Real.goldenRatio⁻¹ ^ (n + 1) =
        Real.goldenRatio⁻¹ ^ n * Real.goldenRatio⁻¹ ^ 2 +
          Real.goldenRatio⁻¹ ^ n * Real.goldenRatio⁻¹ := by
      rw [pow_add, pow_add, pow_one]
    _ = Real.goldenRatio⁻¹ ^ n *
          (Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹) := by ring
    _ = Real.goldenRatio⁻¹ ^ n := by
      rw [inv_goldenRatio_sq_add_inv_goldenRatio, mul_one]

#print axioms inv_goldenRatio_sq_add_inv_goldenRatio
#print axioms inv_goldenRatio_pow_add_pow_succ

end D5.S1.Deficit.Displacement.GoldenInverseRecurrence
