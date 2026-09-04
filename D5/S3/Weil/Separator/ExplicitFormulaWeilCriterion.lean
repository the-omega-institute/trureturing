/- GID: D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/ExplicitFormulaWeilCriterion
   mirror-E: none(waiver:kernel-verified-criterion-only)
   anchors: []
   digest: The explicit formula transports Weil-square positivity to the prime side. -/

import D5.S3.Weil.Separator.WeilSquarePositivityCriterion
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable

/-!
# Explicit-formula Weil criterion

The classical explicit formula identifies the zero sum of each convolution
square with its pole-minus-prime-plus-archimedean expression. Consequently the
frozen Weil-square criterion can be stated entirely on that explicit side.

The result assumes archimedean convergence for every convolution square. It is
relative to supplied `ZeroData`, whose existence is not asserted here, and uses
this repository's even smooth compactly supported `WeilTestFunction` carrier.
It is therefore a conditional reformulation, not a proof of RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.ExplicitFormulaWeilCriterion

open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable

noncomputable section

/-- The explicit formula for a convolution square, using the canonical
symmetric-convergence witness supplied by the zero data. -/
theorem explicitFormula_weilSquare
    (Z : ZeroData) (g : WeilTestFunction)
    (hArch : ArchimedeanConvergent (convolutionSquare g)) :
    zeroSum Z (convolutionSquare g)
        (symmetricConvergent_of_zeroData Z (convolutionSquare g)) =
      poleTerm (convolutionSquare g) - primeTerm (convolutionSquare g) +
        archimedeanTerm (convolutionSquare g) hArch :=
  ZetaBridge.ClassicExplicitFormula.weil_explicit_formula Z
    (convolutionSquare g)
    (symmetricConvergent_of_zeroData Z (convolutionSquare g)) hArch

/-- Relative to supplied zero data and explicit archimedean integrability, RH
is equivalent to nonnegativity of the prime-side explicit-formula expression
on every convolution square. -/
theorem rh_iff_explicitFormulaPositivity
    (Z : ZeroData)
    (hArch : ∀ g : WeilTestFunction,
      ArchimedeanConvergent (convolutionSquare g)) :
    RiemannHypothesis ↔
      ∀ g : WeilTestFunction,
        0 ≤ (poleTerm (convolutionSquare g) -
          primeTerm (convolutionSquare g) +
          archimedeanTerm (convolutionSquare g) (hArch g)).re := by
  constructor
  · intro hRH g
    have hPos :=
      (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mp
        hRH g (symmetricConvergent_of_zeroData Z (convolutionSquare g))
    rw [explicitFormula_weilSquare Z g (hArch g)] at hPos
    exact hPos
  · intro hPos
    apply
      (Separator.WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity Z).mpr
    intro g hZero
    have hPosG := hPos g
    rw [← explicitFormula_weilSquare Z g (hArch g)] at hPosG
    exact hPosG

-- The explicit archimedean hypothesis is jointly witnessable by its binder.
example
    (hArch : ∀ g : WeilTestFunction,
      ArchimedeanConvergent (convolutionSquare g)) :
    ∀ g : WeilTestFunction,
      ArchimedeanConvergent (convolutionSquare g) :=
  hArch

-- The supplied domains have checked inhabitants.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms explicitFormula_weilSquare
#print axioms rh_iff_explicitFormulaPositivity

end

end D5.S3.Weil.Separator.ExplicitFormulaWeilCriterion
