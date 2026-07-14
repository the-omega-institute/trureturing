/- GID: D5/S3/Weil/WeilIdentity
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:classical-analysis-tail-without-numerical-dependency)
   anchors: [pzg/v170/26.3, pzg/v170/26.4]
   digest: Bind the classical Weil explicit formula to the frozen zeta terms. -/

import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.ZeroSum
import D5.X_Assumptions.AxiomDebt

namespace D5.S3.Weil.WeilIdentity

open Filter MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.X_Assumptions

/-
TAIL D5-T0018-F: the term definitions and convergence gates are concrete;
their classical equality is the single registered Weil-1952 AxiomDebt.
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
  have hNontrivial : ∀ n,
      riemannZeta (Z.zero n) = 0 ∧ 0 < (Z.zero n).re ∧ (Z.zero n).re < 1 := by
    simpa [IsNontrivialZero, classicalZeta] using Z.zero_isNontrivial
  have hExhaustive : ∀ {rho : ℂ},
      (riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1) →
        ∃ n, Z.zero n = rho := by
    intro rho hrho
    exact Z.zero_exhaustive (by
      simpa [IsNontrivialZero, classicalZeta] using hrho)
  have hMultiplicity : ∀ n, 0 < Z.multiplicity n ∧
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u (Z.zero n) ∧ u (Z.zero n) ≠ 0 ∧
        riemannZeta =ᶠ[nhds (Z.zero n)]
          fun z => (z - Z.zero n) ^ Z.multiplicity n * u z := by
    simpa [HasZetaZeroMultiplicity, classicalZeta] using Z.multiplicity_spec
  have hLocal : ∀ T : ℝ,
      {n | ‖-Complex.I * (Z.zero n - (((1 / 2 : ℝ) : ℂ)))‖ ≤ T}.Finite := by
    simpa [D5.S3.Weil.ZeroSum.spectralRadius, spectralParameter,
      criticalAbscissa] using Z.locallyFinite
  have hZeroRaw : Tendsto
      (fun T : ℝ =>
        ∑ n ∈ (hLocal T).toFinset,
          (Z.multiplicity n : ℂ) *
            ∫ x : ℝ,
              Complex.exp
                  (-Complex.I *
                    (-Complex.I * (Z.zero n - (((1 / 2 : ℝ) : ℂ)))) * (x : ℂ)) *
                g x)
      atTop (nhds (zeroSum Z g hZero)) := by
    have h := truncatedZeroSum_tendsto Z g hZero
    change Tendsto
      (fun T : ℝ =>
        ∑ n ∈ (hLocal T).toFinset,
          (Z.multiplicity n : ℂ) *
            ∫ x : ℝ,
              Complex.exp
                  (-Complex.I *
                    (-Complex.I * (Z.zero n - (((1 / 2 : ℝ) : ℂ)))) * (x : ℂ)) *
                g x)
      atTop (nhds (zeroSum Z g hZero)) at h
    exact h
  have hArchRaw : Integrable fun t : ℝ =>
      (((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re -
          Real.log Real.pi : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * g x := by
    change Integrable (fun t : ℝ =>
      (((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re -
          Real.log Real.pi : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * g x) at hArch
    exact hArch
  have h := AxiomDebt.weil_explicit_formula_classic
    Z.zero Z.multiplicity Z.zero_injective hNontrivial hExhaustive hMultiplicity
    Z.reflection Z.zero_reflection Z.multiplicity_reflection
    Z.conjugation Z.zero_conjugation Z.multiplicity_conjugation hLocal
    (g : ℝ → ℂ) g.contDiff g.hasCompactSupport g.even
    (zeroSum Z g hZero) hZeroRaw hArchRaw
  simpa [zeroSum, poleTerm, primeTerm, primeSummand, archimedeanTerm,
    archimedeanIntegrand, fourierLaplace, fourierKernel] using h

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
