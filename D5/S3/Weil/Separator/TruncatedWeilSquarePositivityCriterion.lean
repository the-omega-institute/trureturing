/- GID: D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion
   mirror-E: none(waiver:kernel-verified-finite-sum-criterion-only)
   anchors: []
   digest: Finite truncated Weil-square positivity characterizes RH for supplied zero data. -/

import D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData

/-!
# Truncated Weil-square positivity criterion

Relative to a supplied `ZeroData`, nonnegativity of every finite symmetric
truncated Weil-square zero sum is equivalent to the Riemann hypothesis. This
module does not assert that `ZeroData` exists; that is the open M1-b obligation.

The cutoff `truncatedZeroSum` ranges over the finite set `symmetricIndices T`,
whose indices are exactly the zeros with `spectralRadius <= T`, so no
convergence hypothesis is needed. The positivity statement is this repository's
criterion, not Weil's literal criterion, and the conditional equivalence is not
an unconditional proof of RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TruncatedWeilSquarePositivityCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge

noncomputable section

/-- Nonnegativity of every finite symmetric truncated Weil-square zero sum for
supplied zero data implies the Riemann hypothesis. -/
theorem truncatedWeilSquarePositivity_implies_rh
    (Z : ZeroData)
    (hPos : ∀ (T : ℝ) (g : WeilTestFunction),
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re) :
    RiemannHypothesis := by
  apply RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro rho hZero hHalf hLtOne
  have hNontrivial : IsNontrivialZero rho := by
    exact ⟨by simpa [classicalZeta] using hZero, by linarith, hLtOne⟩
  obtain ⟨n, hn⟩ := Z.zero_exhaustive hNontrivial
  let T := spectralRadius (Z.zero n)
  have hnT : n ∈ Z.symmetricIndices T := by
    rw [Z.mem_symmetricIndices]
    exact le_refl _
  have hOff : (Z.zero n).re ≠ criticalAbscissa := by
    rw [hn, criticalAbscissa]
    exact ne_of_gt hHalf
  obtain ⟨g, hNegative⟩ :=
    OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square
      Z n T hnT hOff
  exact (not_lt_of_ge (hPos T g)) hNegative

/-- The Riemann hypothesis makes every finite symmetric truncated Weil-square
zero sum nonnegative for supplied zero data. -/
theorem rh_implies_truncatedWeilSquarePositivity
    (hRH : RiemannHypothesis) (Z : ZeroData) :
    ∀ (T : ℝ) (g : WeilTestFunction),
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re := by
  intro T g
  classical
  have hfilter :
      (Z.symmetricIndices T).filter
          (fun n => (Z.zero n).re = criticalAbscissa) =
        Z.symmetricIndices T := by
    apply Finset.filter_true_of_mem
    intro n _
    exact RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh hRH Z n
  have hnonnegative :=
    (ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative
      Z g T).2
  rw [hfilter] at hnonnegative
  simpa only [truncatedZeroSum] using hnonnegative

/-- For supplied zero data, RH is equivalent to nonnegativity of every finite
symmetric truncated Weil-square zero sum. -/
theorem rh_iff_truncatedWeilSquarePositivity (Z : ZeroData) :
    RiemannHypothesis ↔ ∀ (T : ℝ) (g : WeilTestFunction),
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re := by
  constructor
  · exact fun hRH => rh_implies_truncatedWeilSquarePositivity hRH Z
  · exact truncatedWeilSquarePositivity_implies_rh Z

-- The positivity hypothesis is witnessable from the frozen forward machinery.
example (hRH : RiemannHypothesis) (Z : ZeroData) :
    ∀ (T : ℝ) (g : WeilTestFunction),
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re :=
  rh_implies_truncatedWeilSquarePositivity hRH Z

-- Every quantified domain in the public statements has a checked inhabitant.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty ℝ := ⟨0⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms truncatedWeilSquarePositivity_implies_rh
#print axioms rh_implies_truncatedWeilSquarePositivity
#print axioms rh_iff_truncatedWeilSquarePositivity

end

end D5.S3.Weil.Separator.TruncatedWeilSquarePositivityCriterion
