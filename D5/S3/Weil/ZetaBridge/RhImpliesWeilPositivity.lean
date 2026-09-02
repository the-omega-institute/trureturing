/- GID: D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/RhImpliesWeilPositivity
   mirror-E: none(waiver:conditional-positivity-bridge-only)
   anchors: []
   digest: RH implies the transcribed O-6 Weil positivity statement for supplied zero data. -/

import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.RhImpliesWeilPositivity

open Filter
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine

noncomputable section

/-!
# RH implies the transcribed O-6 Weil positivity statement

This module composes the frozen R-E critical-line bridge with the frozen
finite convolution-square positivity and symmetric-limit machinery. The
route volume named a nonexistent finite-sum theorem and proposed a limit
lemma requiring an extra Archimedean convergence hypothesis; the proof uses
`critical_line_truncated_sum_real_nonnegative`, `truncatedZeroSum_tendsto`,
and closedness of the nonnegative ray instead.

The theorem holds even when `ZeroData` is empty. It is not advertised as a
non-vacuous Weil positivity result.
-/

/-- This is the verbatim unfolding of Hearts `o6WeilPositivityStatement`.
Hearts is an OPEN `X_Frontier` source, not a frozen declaration, and the
import-direction rule forbids a freezable module from importing
`D5.X_Frontier.Hearts`; therefore the proposition body is transcribed here
while the atom's theorem name is preserved verbatim. -/
theorem riemannHypothesis_implies_o6WeilPositivityStatement :
    RiemannHypothesis →
      ∀ (Z : ZeroData) (g : WeilTestFunction)
        (hZero : SymmetricConvergent Z (convolutionSquare g)),
        0 ≤ (zeroSum Z (convolutionSquare g) hZero).re := by
  intro hRH Z g hZero
  classical
  have hfilter (T : ℝ) :
      (Z.symmetricIndices T).filter
          (fun n => (Z.zero n).re = criticalAbscissa) =
        Z.symmetricIndices T := by
    apply Finset.filter_true_of_mem
    intro n _
    exact zeroData_zero_on_critical_line_of_rh hRH Z n
  have hnonneg (T : ℝ) :
      0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re := by
    have hcritical :=
      (critical_line_truncated_sum_real_nonnegative Z g T).2
    rw [hfilter T] at hcritical
    simpa only [truncatedZeroSum] using hcritical
  have hlim :
      Tendsto
        (fun T : ℝ => (truncatedZeroSum Z (convolutionSquare g) T).re)
        atTop
        (nhds (zeroSum Z (convolutionSquare g) hZero).re) :=
    (Complex.continuous_re.tendsto _).comp
      (truncatedZeroSum_tendsto Z (convolutionSquare g) hZero)
  exact isClosed_Ici.mem_of_tendsto hlim
    (Filter.Eventually.of_forall hnonneg)

-- The conditional hypotheses are jointly witnessable by their binders.
example (hRH : RiemannHypothesis) (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z (convolutionSquare g)) :
    RiemannHypothesis ∧ SymmetricConvergent Z (convolutionSquare g) :=
  ⟨hRH, hZero⟩

-- The supplied zero-data domain is inhabited independently of the conclusion.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

-- The test-function domain has a closed canonical inhabitant.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms riemannHypothesis_implies_o6WeilPositivityStatement

end

end D5.S3.Weil.ZetaBridge.RhImpliesWeilPositivity
