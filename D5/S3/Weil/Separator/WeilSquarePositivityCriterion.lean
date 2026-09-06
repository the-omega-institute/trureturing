/- GID: D5/S3/Weil/Separator/WeilSquarePositivityCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/WeilSquarePositivityCriterion
   mirror-E: none(waiver:kernel-verified-criterion-only)
   anchors: []
   digest: Weil-square zero-sum positivity is equivalent to RH relative to supplied zero data. -/

import D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaBridge.RhImpliesWeilPositivity

/-!
# Weil-square positivity criterion

For a supplied `ZeroData`, positivity of this repository's `zeroSum` on every
`convolutionSquare` of a `WeilTestFunction` excludes every zero in the open
right half-strip. The frozen right-half-strip reduction then gives RH, while
the frozen RH-to-positivity theorem supplies the converse.

This criterion is relative to a `ZeroData`; its existence remains the open
M1-b obligation. Its positivity statement uses the repository's definitions,
not a literal transcription of Weil's explicit-formula criterion. Therefore
the result is not an unconditional proof of RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.WeilSquarePositivityCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge

noncomputable section

/-- Positivity of all convolution-square zero sums for supplied zero data
implies the Riemann hypothesis. -/
theorem weilSquarePositivity_implies_rh
    (Z : ZeroData)
    (hPos : ∀ (g : WeilTestFunction)
      (hZero : SymmetricConvergent Z (convolutionSquare g)),
      0 ≤ (zeroSum Z (convolutionSquare g) hZero).re) :
    RiemannHypothesis := by
  apply RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro rho hZero hHalf hLtOne
  have hPositive : 0 < rho.re := by
    linarith
  have hNontrivial : IsNontrivialZero rho := by
    exact ⟨by simpa [classicalZeta] using hZero, hPositive, hLtOne⟩
  obtain ⟨n, hn⟩ := Z.zero_exhaustive hNontrivial
  have hOff : (Z.zero n).re ≠ criticalAbscissa := by
    rw [hn, criticalAbscissa]
    exact ne_of_gt hHalf
  obtain ⟨g, hConvergent, hNegative⟩ :=
    OffLineZeroNegativeWeilSquare.offLineZero_yields_negative_weil_square
      Z n hOff
  exact (not_lt_of_ge (hPos g hConvergent)) hNegative

/-- For supplied zero data, RH is equivalent to nonnegativity of every
convolution-square zero sum. -/
theorem rh_iff_weilSquarePositivity (Z : ZeroData) :
    RiemannHypothesis ↔
      ∀ (g : WeilTestFunction)
        (hZero : SymmetricConvergent Z (convolutionSquare g)),
        0 ≤ (zeroSum Z (convolutionSquare g) hZero).re := by
  constructor
  · intro hRH
    exact
      RhImpliesWeilPositivity.riemannHypothesis_implies_o6WeilPositivityStatement
        hRH Z
  · exact weilSquarePositivity_implies_rh Z

-- The positivity hypothesis is witnessable from the frozen forward direction.
example (Z : ZeroData) (hRH : RiemannHypothesis) :
    ∀ (g : WeilTestFunction)
      (hZero : SymmetricConvergent Z (convolutionSquare g)),
      0 ≤ (zeroSum Z (convolutionSquare g) hZero).re :=
  RhImpliesWeilPositivity.riemannHypothesis_implies_o6WeilPositivityStatement
    hRH Z

-- The theorem's supplied domains have checked inhabitants.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms weilSquarePositivity_implies_rh
#print axioms rh_iff_weilSquarePositivity

end

end D5.S3.Weil.Separator.WeilSquarePositivityCriterion
