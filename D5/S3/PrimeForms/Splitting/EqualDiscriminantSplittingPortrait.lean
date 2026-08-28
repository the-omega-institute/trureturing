/- GID: D5/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal quadratic-form discriminants give equal splitting symbols at every index. -/

import D5.S3.PrimeForms.EisensteinDiscriminant
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/- Library-search audit trail (2026-08-26):
   * Exact current-tree searches for equal-discriminant splitting portraits and
     Legendre/Jacobi symbols applied to a form discriminant found no D5 theorem.
     `GlobalDiscriminantSplitKernelChain` is premise-driven and generic, so it is
     not an exact statement of this source construction.
   * Exact family hit `EisensteinDiscriminant.BinaryQuadraticForm` supplies the
     canonical integer-coefficient form carrier and its discriminant; both are
     imported rather than redeclared.
   * Pinned Mathlib's `jacobiSym` is the all-natural-index extension of the
     Legendre splitting symbol and agrees with `legendreSym` at prime indices.
     The public theorem applies it directly, with no duplicate split-readout def.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.EqualDiscriminantSplittingPortrait

open D5.S3.PrimeForms.EisensteinDiscriminant

/-- Binary quadratic forms with equal discriminants have the same discriminant
splitting symbol at every natural index, hence in particular at every prime. -/
theorem equal_discriminant_splitting_portrait
    (Q Q' : BinaryQuadraticForm)
    (hDiscriminant : Q.discriminant = Q'.discriminant) :
    ∀ p : Nat,
      jacobiSym Q.discriminant p = jacobiSym Q'.discriminant p := by
  intro p
  exact congrArg (fun discriminant : Int => jacobiSym discriminant p) hDiscriminant

#print axioms equal_discriminant_splitting_portrait

end D5.S3.PrimeForms.Splitting.EqualDiscriminantSplittingPortrait
