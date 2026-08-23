/- GID: D5/S1/Depth/ContinuedFractions/CompleteQuotientBound
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/CompleteQuotientBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lagrange B step 1 proves discriminant invariance under unimodular Mobius pullback. -/

import D5.S1.Depth.ContinuedFractions.PeriodicImpliesQuadratic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'unimodular_transform_preserves_discriminant' D5
     Golden/Frozen/accepted` had no public or private theorem hit.
   * Repository searches for `completeQuotient|discriminant|BoundedComplete` found the
     public complete-quotient model in `PeriodicImpliesQuadratic`, concrete discriminant
     calculations, and no Mobius discriminant-invariance theorem; no private hit covers it.
   * Pinned Mathlib searches for discriminants with `Mobius`, `linear fractional`,
     `unimodular`, and `BinaryQuadraticForm` found no reusable declaration.
   * The requested approximation search found `GenContFract.abs_sub_convs_le`, with bound
     `|v - convs n| <= 1 / (dens n * dens (n + 1))`; step 1 below does not need it.
   * `QuadraticImpliesPeriodic` from PR #2903 is absent from this worktree, so this module
     reuses `MobiusInt` from direction A and proves only the independent step 1 algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Depth.ContinuedFractions.CompleteQuotientBound

open D5.S1.Depth.ContinuedFractions.PeriodicImpliesQuadratic

/-- Integer coefficients of a quadratic equation `a * X^2 + b * X + c = 0`. -/
structure QuadraticCoefficients where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

/-- The discriminant `b^2 - 4ac` of an integral quadratic equation. -/
def QuadraticCoefficients.discriminant (f : QuadraticCoefficients) : ℤ :=
  f.b ^ 2 - 4 * f.a * f.c

/-- Pull quadratic coefficients back along the relation represented by `M`.

If `M.Rel x y` and `f` annihilates `y`, these are the coefficients obtained after
substituting `y = (M.b - M.d * x) / (M.c * x - M.a)` and clearing the square of the
denominator. -/
def QuadraticCoefficients.pullback (f : QuadraticCoefficients) (M : MobiusInt) :
    QuadraticCoefficients where
  a := f.a * M.d ^ 2 - f.b * M.d * M.c + f.c * M.c ^ 2
  b :=
    -2 * f.a * M.b * M.d + f.b * (M.b * M.c + M.a * M.d) -
      2 * f.c * M.a * M.c
  c := f.a * M.b ^ 2 - f.b * M.a * M.b + f.c * M.a ^ 2

/-- A Mobius pullback scales the discriminant by the square of its determinant. -/
theorem pullback_discriminant (f : QuadraticCoefficients) (M : MobiusInt) :
    (f.pullback M).discriminant = M.det ^ 2 * f.discriminant := by
  simp only [QuadraticCoefficients.pullback, QuadraticCoefficients.discriminant,
    MobiusInt.det]
  ring

/-- A unimodular Mobius transfer preserves the discriminant of an integral quadratic
equation. -/
theorem unimodular_transform_preserves_discriminant (f : QuadraticCoefficients)
    (M : MobiusInt) (hM : M.det = 1 ∨ M.det = -1) :
    (f.pullback M).discriminant = f.discriminant := by
  rw [pullback_discriminant]
  rcases hM with hM | hM <;> rw [hM] <;> ring

example :
    (QuadraticCoefficients.pullback ⟨1, -1, -1⟩ (MobiusInt.step 1)).discriminant = 5 := by
  norm_num [QuadraticCoefficients.pullback, QuadraticCoefficients.discriminant,
    MobiusInt.step]

#print axioms unimodular_transform_preserves_discriminant

end D5.S1.Depth.ContinuedFractions.CompleteQuotientBound
