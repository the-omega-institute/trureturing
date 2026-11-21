/- GID: D5/S3/Quantum/Analysis/RefinedBMVUniformExpansion
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact multivariate expansion of the refined BMV discriminant. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-! # Sparse expansion of the refined BMV discriminant -/

namespace RefinedBMV.DividedDifference.SparseExpansion

/-- Exponents in the variable order `p, X, Y, U, V`. -/
structure Exponents where
  p : ℕ
  x : ℕ
  y : ℕ
  u : ℕ
  v : ℕ
  deriving DecidableEq, Ord, Repr

structure Term where
  exponents : Exponents
  coefficient : ℤ
  deriving Repr

def Term.eval {R : Type*} [CommRing R] (p X Y U V : R) (a : Term) : R :=
  (a.coefficient : R) *
    (p ^ a.exponents.p * X ^ a.exponents.x * Y ^ a.exponents.y *
      U ^ a.exponents.u * V ^ a.exponents.v)

def evalTerms {R : Type*} [CommRing R] (p X Y U V : R) (ts : List Term) : R :=
  (ts.map (Term.eval p X Y U V)).sum

/-- The formula in `RefinedBMV.DividedDifference.clearedQuartic`, parameterized by its
operations so the same expression computes both the expansion and its ring value. -/
def quarticFormula {S : Type*} [Add S] [Sub S] [Mul S] [Pow S ℕ]
    [OfNat S 1] [OfNat S 2] [OfNat S 4] (p X Y U V : S) : S :=
  let n := (p + 1) * (p + 2)
  let d := 2 * ((Y - X) - (Y - 1) * X^2 * U^3 + (X - 1) * Y^2 * V^3) -
    n * U * V * ((X - 1) * (Y - 1) * (Y - X))
  let f := 2 * (Y^2 * V^3 - (p + 2) * Y + p + 1) - n * V * (Y - 1)^2
  let g := 2 * (Y^2 * V^3 - (p + 2) * X * Y * U^3 + (p + 1) * X^2 * U^3) -
    n * U^2 * V * (Y - X)^2
  let r := 2 * (1 - (p + 2) * X * U^3 + (p + 1) * X^2 * U^3) -
    n * U^2 * (X - 1)^2
  let h := 2 * (1 - (p + 2) * Y * V^3 + (p + 1) * Y^2 * V^3) -
    n * V^2 * (Y - 1)^2
  let q := f * g * (X - 1)^2
  let w := r * h * (Y - X)^2
  4 * q * w - (d^2 - q - w)^2

end RefinedBMV.DividedDifference.SparseExpansion
