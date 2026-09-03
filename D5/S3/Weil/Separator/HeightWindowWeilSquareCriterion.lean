/- GID: D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/HeightWindowWeilSquareCriterion
   mirror-E: none(waiver:kernel-verified-height-window-criterion-only)
   anchors: []
   digest: Critical-line zeros in each spectral window are equivalent to truncated positivity. -/

import D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
import D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData

/-!
# Height-window Weil-square criterion

Relative to supplied `ZeroData`, all stored zeros in a fixed spectral-radius
window lie on the critical line exactly when every truncated convolution-square
zero sum is nonnegative. Requiring the critical-line condition at every height
is equivalent to the Riemann hypothesis through the frozen right-half-strip
reduction.

The window is `‖Z.gamma n‖ ≤ T`, not a bound on the imaginary part of a zero.
The positivity is this repository's `truncatedZeroSum` positivity, not a literal
statement of Weil's classical criterion. No `ZeroData` existence is asserted;
the M1-b obligation remains open. Consequently these relative equivalences are
not an unconditional proof of RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.HeightWindowWeilSquareCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge

noncomputable section

/-- In a fixed spectral-radius window, critical-line location is equivalent to
nonnegativity of every truncated Weil square. -/
theorem heightWindow_rh_iff_truncatedWeilSquarePositivity
    (Z : ZeroData) (T : ℝ) :
    (∀ n ∈ Z.symmetricIndices T, (Z.zero n).re = criticalAbscissa) ↔
      ∀ g : WeilTestFunction,
        0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re := by
  constructor
  · intro hLine g
    classical
    have hCritical :=
      (ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative Z g T).2
    rw [Finset.filter_true_of_mem hLine] at hCritical
    simpa only [truncatedZeroSum] using hCritical
  · intro hPos n hn
    by_contra hOff
    obtain ⟨g, hNegative⟩ :=
      OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square
        Z n T hn hOff
    exact (not_lt_of_ge (hPos g)) hNegative

/-- RH is equivalent to critical-line location in every spectral-radius
window, relative to supplied zero data. -/
theorem rh_iff_forall_heightWindow (Z : ZeroData) :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∀ n ∈ Z.symmetricIndices T,
        (Z.zero n).re = criticalAbscissa := by
  constructor
  · intro hRH T n _
    exact RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh hRH Z n
  · intro hWindow
    apply RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro rho hZero hHalf hLtOne
    obtain ⟨n, hn⟩ := Z.zero_exhaustive
      ⟨by simpa [classicalZeta] using hZero, by linarith, hLtOne⟩
    have hLine := hWindow ‖Z.gamma n‖ n ((Z.mem_symmetricIndices).2 (le_refl _))
    rw [hn, criticalAbscissa] at hLine
    linarith

-- The critical-line side is witnessable under the frozen RH bridge.
example (hRH : RiemannHypothesis) (Z : ZeroData) (T : ℝ) :
    ∀ n ∈ Z.symmetricIndices T, (Z.zero n).re = criticalAbscissa := by
  intro n _
  exact RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh hRH Z n

-- The theorem transports a checked critical-line hypothesis to positivity.
example (Z : ZeroData) (T : ℝ)
    (hLine : ∀ n ∈ Z.symmetricIndices T,
      (Z.zero n).re = criticalAbscissa) :
    ∀ g : WeilTestFunction,
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re :=
  (heightWindow_rh_iff_truncatedWeilSquarePositivity Z T).1 hLine

-- The supplied domains have checked inhabitants relative to the input data.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example : Nonempty ℝ := ⟨0⟩

#print axioms heightWindow_rh_iff_truncatedWeilSquarePositivity
#print axioms rh_iff_forall_heightWindow

end

end D5.S3.Weil.Separator.HeightWindowWeilSquareCriterion
