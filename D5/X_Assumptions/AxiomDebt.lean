/- GID: D5/X_Assumptions/AxiomDebt
   generality: G
   mirror-B: none(waiver:axiom-debt-registry-is-the-semantic-mirror)
   mirror-E: none(waiver:classical-theorem-without-numerical-evidence-dependency)
   anchors: [GICT-v3.6-I.2-theorem-2.9, sos1957threegap]
   digest: Register the classical three-gap theorem while pinned mathlib has no formalization. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Real.Irrational

namespace D5.X_Assumptions.AxiomDebt

/-- The first `N` fractional parts of the rotation by `alpha`. -/
noncomputable def fractionalOrbit (alpha : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image fun n : ℕ => Int.fract ((n : ℝ) * alpha)

/-- The orbit representatives in increasing order in `[0, 1)`. -/
noncomputable def sortedFractionalOrbit (alpha : ℝ) (N : ℕ) : List ℝ :=
  (fractionalOrbit alpha N).sort

/-- Successive linear gaps together with the wrap-around gap on the unit circle. -/
def cyclicGaps : List ℝ → List ℝ
  | [] => []
  | x :: xs =>
      (x :: xs).zipWith (fun a b => b - a) xs ++
        [1 - (x :: xs).getLast (List.cons_ne_nil x xs) + x]

/-- The set of distinct cyclic gap lengths in the first `N` points of a rotation. -/
noncomputable def fractionalGapValues (alpha : ℝ) (N : ℕ) : Finset ℝ :=
  (cyclicGaps (sortedFractionalOrbit alpha N)).toFinset

/--
The classical three-gap theorem (Steinhaus conjecture; Sós 1957): an irrational
rotation cuts the unit circle into intervals of at most three distinct lengths.

AxiomDebt case `D5-T0019`. The pinned mathlib tree contains no three-gap or
three-distance theorem; the librarian upstream-formalization issue is tracked by
the same case. This is a classical-result tail, not a repository-specific premise.
-/
axiom three_gap_classic (alpha : ℝ) (hirrational : Irrational alpha) (N : ℕ) :
    (fractionalGapValues alpha N).card ≤ 3

end D5.X_Assumptions.AxiomDebt
