/- GID: D5/S3/Arith/Wythoff/ColumnResiduePairs
   generality: I
   mirror-B: D5/B/S3/Arith/Wythoff/ColumnResiduePairs
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: The first two columns of the Wythoff array attain every residue pair modulo each positive integer. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Wythoff.ColumnResiduePairs

/-- The Wythoff array, with rows and columns numbered from one. Column zero
is the lower Wythoff sequence; columns one and two have Morrison's floor
definitions, and all later columns follow the Fibonacci recurrence. -/
noncomputable def W (n : ℕ) : ℕ → ℤ
  | 0 => ⌊(n : ℝ) * Real.goldenRatio⌋
  | 1 => ⌊(⌊(n : ℝ) * Real.goldenRatio⌋ : ℝ) * Real.goldenRatio⌋
  | 2 => ⌊(⌊(n : ℝ) * Real.goldenRatio⌋ : ℝ) * Real.goldenRatio ^ 2⌋
  | k + 3 => W n (k + 2) + W n (k + 1)

end D5.S3.Arith.Wythoff.ColumnResiduePairs
