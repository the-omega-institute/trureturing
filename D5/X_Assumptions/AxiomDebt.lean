/- GID: D5/X_Assumptions/AxiomDebt
   generality: G
   mirror-B: none(waiver:axiom-debt-registry-is-the-semantic-mirror)
   mirror-E: none(waiver:classical-theorem-without-numerical-evidence-dependency)
   anchors: []
   digest: Register the classical three-gap and Weil explicit-formula debts; the Fourier-Laplace debt is discharged (proved in D5/S3/Fourier/PaleyWiener). -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace D5.X_Assumptions.AxiomDebt

open Filter MeasureTheory
open scoped ComplexConjugate ContDiff

/-
AxiomDebt case `D5-T0018-C` (DISCHARGED). Pinned mathlib supplies smooth
compactly supported functions and real Fourier theory but no direct theorem
exposing the entire complex Fourier-Laplace extension; that classical bridge
is now proved natively in
`D5/S3/Fourier/PaleyWiener.fourier_laplace_entire_classic`, so no axiom is
registered here. This case is retained as a discharge marker only.
-/

/-
TAIL D5-T0018-F: pinned mathlib has no theorem binding the concrete prime,
pole, archimedean, and symmetric zero terms in the frozen convention.
-/

/--
The classical Weil explicit formula (Weil 1952) in the repository's frozen
angular-frequency convention.

AxiomDebt case `D5-T0018-F`. Because the assumption foundation imports only
Mathlib, this signature spells out the exact fields and definitional expansions
of `ZeroData`, `WeilTestFunction`, `zeroSum`, `poleTerm`, `primeTerm`, and
`archimedeanTerm`; `D5/S3/Weil/WeilIdentity` proves the named specialization.
It asserts only this equality and contains no positivity, RH, or O-6 conclusion.
-/
axiom weil_explicit_formula_classic
    (zero : ℕ → ℂ) (multiplicity : ℕ → ℕ)
    (_zeroInjective : Function.Injective zero)
    (_zeroIsNontrivial : ∀ n,
      riemannZeta (zero n) = 0 ∧ 0 < (zero n).re ∧ (zero n).re < 1)
    (_zeroExhaustive : ∀ {rho : ℂ},
      (riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1) → ∃ n, zero n = rho)
    (_multiplicitySpec : ∀ n, 0 < multiplicity n ∧
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u (zero n) ∧ u (zero n) ≠ 0 ∧
        riemannZeta =ᶠ[nhds (zero n)] fun z => (z - zero n) ^ multiplicity n * u z)
    (reflection : Equiv.Perm ℕ)
    (_zeroReflection : ∀ n, zero (reflection n) = 1 - zero n)
    (_multiplicityReflection : ∀ n,
      multiplicity (reflection n) = multiplicity n)
    (conjugation : Equiv.Perm ℕ)
    (_zeroConjugation : ∀ n, zero (conjugation n) = conj (zero n))
    (_multiplicityConjugation : ∀ n,
      multiplicity (conjugation n) = multiplicity n)
    (locallyFinite : ∀ T : ℝ,
      {n | ‖-Complex.I * (zero n - (((1 / 2 : ℝ) : ℂ)))‖ ≤ T}.Finite)
    (g : ℝ → ℂ) (_smooth : ContDiff ℝ ∞ g) (_compact : HasCompactSupport g)
    (_even : ∀ x, g (-x) = g x)
    (zeroLimit : ℂ)
    (_zeroConverges : Tendsto
      (fun T : ℝ =>
        ∑ n ∈ (locallyFinite T).toFinset,
          (multiplicity n : ℂ) *
            ∫ x : ℝ,
              Complex.exp
                  (-Complex.I *
                    (-Complex.I * (zero n - (((1 / 2 : ℝ) : ℂ)))) * (x : ℂ)) *
                g x)
      atTop (nhds zeroLimit))
    (_archimedeanConverges : Integrable fun t : ℝ =>
      (((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re -
          Real.log Real.pi : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * g x) :
    zeroLimit =
      ((∫ x : ℝ,
          Complex.exp (-Complex.I * (-Complex.I / 2) * (x : ℂ)) * g x) +
        ∫ x : ℝ,
          Complex.exp (-Complex.I * (Complex.I / 2) * (x : ℂ)) * g x) -
        ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (g (Real.log n) + g (-Real.log n)) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re -
              Real.log Real.pi : ℝ) : ℂ) *
            ∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * g x

end D5.X_Assumptions.AxiomDebt
