/- GID: D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/OffLineZeroNegativeWeilSquare
   mirror-E: none(waiver:kernel-verified-final-separator-bindings)
   anchors: []
   digest: Off-line zeros yield negative full and truncated Weil-square sums without hIm. -/

import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
import D5.S3.Weil.ZetaBridge.OffLineZeroNegativeTruncatedWeilSquare

/-!
# Off-line zero negative Weil square

The stored nontriviality field and the frozen nonreality theorem discharge the
imaginary-part hypothesis in both frozen separators. This is the final
separator form for any off-line zero stored by `ZeroData`; it does not prove
that O-6 implies the Riemann hypothesis and does not assert that `ZeroData` is
inhabited.
-/

/- Library-search audit trail (2026-09-03):
   * Exact target-name searches in D5 and exact statement-shape searches in
     pinned Mathlib missed.
   * D5 shape searches hit the three frozen declarations bound below.
   * No new definition or independent proof is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge

noncomputable section

/-- Every nontrivial zero stored by `ZeroData` has nonzero imaginary part. -/
theorem zeroData_im_ne_zero (Z : ZeroData) (n : ℕ) :
    (Z.zero n).im ≠ 0 :=
  AlternatingZetaContinuation.ZeroData.im_ne_zero
    Z n (Z.zero_isNontrivial n)

/-- Any stored off-line zero yields a negative full Weil-square zero sum. -/
theorem offLineZero_yields_negative_weil_square
    (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ∃ g : WeilTestFunction,
      ∃ hZero : SymmetricConvergent Z (convolutionSquare g),
        (zeroSum Z (convolutionSquare g) hZero).re < 0 :=
  OffLineNonrealZeroNegativeWeilSquare.offLineNonrealZero_yields_negative_weil_square
    Z n hOff (zeroData_im_ne_zero Z n)

/-- Any stored off-line zero in a cutoff yields a negative truncated
Weil-square zero sum. -/
theorem offLineZero_negative_truncated_weil_square
    (Z : ZeroData) (n : ℕ) (T : ℝ)
    (hn : n ∈ Z.symmetricIndices T)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ∃ g : WeilTestFunction,
      (truncatedZeroSum Z (convolutionSquare g) T).re < 0 :=
  OffLineZeroNegativeTruncatedWeilSquare.offLineZero_yields_negative_truncated_weil_square
    Z n T hn hOff (zeroData_im_ne_zero Z n)

-- These checked terms expose the exact hypotheses and inhabited domains.
example (Z : ZeroData) (n : ℕ) : IsNontrivialZero (Z.zero n) :=
  Z.zero_isNontrivial n

example (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    (Z.zero n).re ≠ criticalAbscissa :=
  hOff

example (Z : ZeroData) (n : ℕ) :
    n ∈ Z.symmetricIndices ‖Z.gamma n‖ := by
  simp

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms zeroData_im_ne_zero
#print axioms offLineZero_yields_negative_weil_square
#print axioms offLineZero_negative_truncated_weil_square

end

end D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
