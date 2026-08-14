/- GID: D5/S3/Weil/WeilIdentity
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:classical-analysis-tail-without-numerical-dependency)
   anchors: []
   digest: Bind the classical Weil explicit formula to the frozen zeta terms. -/

import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.ZeroSum
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

namespace D5.S3.Weil.WeilIdentity

open Filter MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum

/-
TAIL D5-T0018-F (DISCHARGED): the hypothesis-free zeta explicit formula is ported from
Zeta23 and translated to the repository's frozen Weil vocabulary by `ZetaBridge`.
-/

/--
The classical Weil explicit formula in the frozen angular-frequency convention.
Both convergence obligations are explicit, and `Z` supplies the exact
multiplicity-aware nontrivial zeros. No positivity or RH assertion is present.
-/
theorem weil_explicit_formula
    (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z g) (hArch : ArchimedeanConvergent g) :
    zeroSum Z g hZero =
      poleTerm g - primeTerm g + archimedeanTerm g hArch := by
  exact
    D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.weil_explicit_formula Z g hZero hArch

/-- Solve the explicit formula for the concrete prime-power term. -/
theorem prime_term_eq_pole_add_archimedean_sub_zero_sum
    (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z g) (hArch : ArchimedeanConvergent g) :
    primeTerm g =
      poleTerm g + archimedeanTerm g hArch - zeroSum Z g hZero := by
  rw [weil_explicit_formula Z g hZero hArch]
  ring

/-- Solve the explicit formula for the concrete pole contribution. -/
theorem pole_term_eq_zero_sum_add_prime_sub_archimedean
    (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z g) (hArch : ArchimedeanConvergent g) :
    poleTerm g =
      zeroSum Z g hZero + primeTerm g - archimedeanTerm g hArch := by
  rw [weil_explicit_formula Z g hZero hArch]
  ring

end D5.S3.Weil.WeilIdentity
