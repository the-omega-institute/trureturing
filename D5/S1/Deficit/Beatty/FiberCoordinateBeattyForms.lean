/- GID: D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/FiberCoordinateBeattyForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The floor and displacement forms of both golden fiber coordinates agree, yielding the
   fiber equation and the counterexample to the proposed ceiling start; the real interval and
   parity description, capacity pair, corrected first-index identification, monotonicity of b,
   and interval support are not covered. -/

import D5.S1.Deficit.ZeckendorfDisplacementReading
import D5.S1.Words.GoldenFiberCoordinates

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'fiber_coordinates_eq_displacement_forms' D5 Golden/Frozen/accepted`
     returned no matches.
   * Searches for `fiberA`, `fiberB`, `fiberCoordinateA`, and `fiberCoordinateB` found the public
     theorems `D5.S1.Words.GoldenFiberCoordinates.golden_fiber_coordinates` and
     `D5.S1.Eigenstructure.GoldenFiberCoordinates.golden_fiber_coordinates`, but neither directly
     equates the two coordinate presentations or states the fiber membership criterion.
   * `GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq` publicly equates the corrected floor
     expression with its compressed form, but does not identify either expression as a least
     member of a fiber. No relevant private declaration supplies a public-cover candidate.
   * The bridge below reuses `displacement_decode_eq_beatty_floor`; its remaining proof is integer
     linear arithmetic. The counterexample uses `Real.goldenRatio_sq` and floor/ceil laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.FiberCoordinateBeattyForms

open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words.GoldenFiberCoordinates

/-- The fiber labelled by `a`, expressed through the established first floor coordinate. -/
noncomputable def goldenFiber (a : ℤ) : Set ℕ :=
  {v | fiberA v = a}

/-- Both floor-defined fiber coordinates equal their linear displacement-reading forms. -/
theorem fiber_coordinates_eq_displacement_forms (v : ℕ) :
    fiberA v = 2 * (displacementDecode v : ℤ) - 3 * (v : ℤ) ∧
      fiberB v = 2 * (v : ℤ) - (displacementDecode v : ℤ) := by
  have hdecode := displacement_decode_eq_beatty_floor v
  constructor
  · rw [fiberA, goldenShift, ← hdecode]
  · rw [fiberB, goldenShift, ← hdecode]

/-- Membership in the fiber labelled by `a` is exactly the doubled displacement equation. -/
theorem mem_goldenFiber_iff (a : ℤ) (v : ℕ) :
    v ∈ goldenFiber a ↔
      2 * (displacementDecode v : ℤ) = 3 * (v : ℤ) + a := by
  change fiberA v = a ↔ _
  rw [(fiber_coordinates_eq_displacement_forms v).1]
  omega

/-- At `a = 1`, the proposed ceiling start differs from the corrected floor-plus-one expression. -/
theorem ceiling_start_formula_fails_at_one :
    ⌈(1 : ℝ) * Real.goldenRatio - Real.goldenRatio ^ 2⌉ ≠
      ⌊(1 : ℝ) * Real.goldenRatio - Real.goldenRatio ^ 2⌋ + 1 := by
  rw [Real.goldenRatio_sq]
  norm_num

example :
    fiberA 1 = 2 * (displacementDecode 1 : ℤ) - 3 ∧
      fiberB 1 = 2 - (displacementDecode 1 : ℤ) := by
  simpa using fiber_coordinates_eq_displacement_forms 1

#print axioms fiber_coordinates_eq_displacement_forms

end D5.S1.Deficit.FiberCoordinateBeattyForms
