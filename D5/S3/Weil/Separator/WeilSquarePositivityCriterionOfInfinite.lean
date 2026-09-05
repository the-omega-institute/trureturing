/- GID: D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite
   mirror-E: none(waiver:kernel-verified-equivalence-only)
   anchors: []
   digest: Under zero infinitude, RH iff Weil-square positivity for every or some ZeroData. -/

import D5.S3.Weil.Separator.WeilSquarePositivityCriterion
import D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite

/-!
# Weil-square positivity criteria under infinitely many zeros

Assuming that the set of nontrivial zeta zeros is infinite, the frozen
nonemptiness bridge supplies `ZeroData`. The fixed-`ZeroData` Weil-square
criterion then makes RH equivalent both to positivity for every such data and
to positivity for at least one such data.

The infinitude assumption is the unproved M1-b obligation. The construction of
`ZeroData` behind M1-a is noncomputable, and the right-hand sides use this
repository's Weil-square positivity predicate. These conditional equivalences
are not a proof of RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.WeilSquarePositivityCriterionOfInfinite

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil

noncomputable section

/-- Under infinitude of the nontrivial zeros, RH is equivalent to Weil-square
positivity for every `ZeroData`. -/
theorem rh_iff_forall_zeroData_weilSquarePositivity
    (hInf : {rho : ℂ | IsNontrivialZero rho}.Infinite) :
    RiemannHypothesis ↔
      ∀ Z : ZeroData, ∀ (g : WeilTestFunction)
        (hZero : SymmetricConvergent Z (convolutionSquare g)),
        0 ≤ (zeroSum Z (convolutionSquare g) hZero).re := by
  constructor
  · intro hRH Z
    exact
      (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mp hRH
  · intro hPos
    obtain ⟨Z⟩ :=
      (ZetaBridge.ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite).mpr hInf
    exact
      (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mpr
        (hPos Z)

/-- Under infinitude of the nontrivial zeros, RH is equivalent to Weil-square
positivity for some `ZeroData`. -/
theorem rh_iff_exists_zeroData_weilSquarePositivity
    (hInf : {rho : ℂ | IsNontrivialZero rho}.Infinite) :
    RiemannHypothesis ↔
      ∃ Z : ZeroData, ∀ (g : WeilTestFunction)
        (hZero : SymmetricConvergent Z (convolutionSquare g)),
        0 ≤ (zeroSum Z (convolutionSquare g) hZero).re := by
  constructor
  · intro hRH
    obtain ⟨Z⟩ :=
      (ZetaBridge.ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite).mpr hInf
    exact
      ⟨Z,
        (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mp hRH⟩
  · rintro ⟨Z, hPos⟩
    exact
      (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mpr hPos

-- Any supplied ZeroData witnesses the infinitude hypothesis through M1-a.
example (Z : ZeroData) : {rho : ℂ | IsNontrivialZero rho}.Infinite :=
  (ZetaBridge.ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite).mp ⟨Z⟩

-- Conversely, the stated infinitude hypothesis supplies the quantified domain.
example (hInf : {rho : ℂ | IsNontrivialZero rho}.Infinite) : Nonempty ZeroData :=
  (ZetaBridge.ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite).mpr hInf

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example : Nonempty ℂ := ⟨0⟩

#print axioms rh_iff_forall_zeroData_weilSquarePositivity
#print axioms rh_iff_exists_zeroData_weilSquarePositivity

end

end D5.S3.Weil.Separator.WeilSquarePositivityCriterionOfInfinite
