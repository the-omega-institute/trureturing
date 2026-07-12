/- GID: D5/X_Assumptions/AxiomDebt
   generality: G
   mirror-B: none(waiver:axiom-debt-registry-is-the-semantic-mirror)
   mirror-E: none(waiver:classical-theorem-without-numerical-evidence-dependency)
   anchors: [GICT-v3.6-I.2-theorem-2.9, sos1957threegap]
   digest: Register classical three-gap and Fourier-Laplace entire-extension debts. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace D5.X_Assumptions.AxiomDebt

open scoped ContDiff

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

/-
FROZEN TAIL D5-T0018-C: pinned mathlib supplies smooth compactly supported
functions and real Fourier theory, but no direct theorem exposing the entire
complex Fourier-Laplace extension. The transform below is fixed, not free.
-/

/--
Classical compact-support Fourier-Laplace theorem: the angular-frequency
transform of a smooth compactly supported function is entire.

AxiomDebt case `D5-T0018-C`. This is the level-C Paley-Wiener input only; no
Weil explicit-formula identity or positivity claim is included.
-/
axiom fourier_laplace_entire_classic
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g) (hcompact : HasCompactSupport g) :
    Differentiable ℂ fun z : ℂ =>
      ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x

end D5.X_Assumptions.AxiomDebt
