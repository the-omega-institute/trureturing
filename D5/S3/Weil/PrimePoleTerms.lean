/- GID: D5/S3/Weil/PrimePoleTerms
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:structural-explicit-formula-terms-only)
   anchors: [pzg/v170/26.3, pzg/v170/26.4]
   digest: Bind prime, pole, and archimedean terms for the classical zeta Weil formula. -/

import D5.S3.Weil.FourierLaplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace D5.S3.Weil.PrimePoleTerms

open MeasureTheory
open D5.S3.Weil.Convention D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace

/-- The concrete von Mangoldt summand in the prime-power side of the Weil formula. -/
noncomputable def primeSummand (g : WeilTestFunction) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (g (Real.log n) + g (-Real.log n))

/-- The von Mangoldt factor kills every index that is not a prime power. -/
theorem primeSummand_eq_zero_of_not_primePow (g : WeilTestFunction) {n : ℕ}
    (hn : ¬ IsPrimePow n) : primeSummand g n = 0 := by
  have hLambda : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  simp [primeSummand, hLambda]

/-- Compact support of `g` makes the logarithmically sampled prime summand finitely supported. -/
theorem primeSummand_hasFiniteSupport (g : WeilTestFunction) :
    (Function.support (primeSummand g)).Finite := by
  have hsupport : BddAbove (Function.support (g : ℝ → ℂ)) :=
    BddAbove.mono (subset_tsupport (g : ℝ → ℂ))
      g.hasCompactSupport.isBounded.bddAbove
  obtain ⟨C, hC⟩ := hsupport
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : ∀ᶠ n : ℕ in Filter.atTop, g (Real.log n) = 0 := by
    filter_upwards [hlog.eventually_gt_atTop C] with n hn
    by_contra hne
    have hmem : Real.log (n : ℝ) ∈ Function.support (g : ℝ → ℂ) :=
      Function.mem_support.mpr hne
    exact (not_lt_of_ge (hC hmem)) hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hzero
  refine (Finset.finite_toSet (Finset.range N)).subset ?_
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnlt
  have hNle : N ≤ n := Nat.le_of_not_gt hnlt
  have hg : g (Real.log n) = 0 := hN n hNle
  apply (Function.mem_support.mp hn)
  simp [primeSummand, g.even, hg]

/-- The concrete prime-power summand is summable because it has finite support. -/
theorem primeSummand_summable (g : WeilTestFunction) : Summable (primeSummand g) :=
  summable_of_hasFiniteSupport (primeSummand_hasFiniteSupport g)

/-- The prime-power term in the fixed angular-frequency convention. -/
noncomputable def primeTerm (g : WeilTestFunction) : ℂ :=
  ∑' n : ℕ, primeSummand g n

/-- The defining prime series converges to `primeTerm`. -/
theorem primeTerm_hasSum (g : WeilTestFunction) :
    HasSum (primeSummand g) (primeTerm g) := by
  simpa only [primeTerm] using (primeSummand_summable g).hasSum

/-- The pole at `s = 1` and its reflected `s = 0` contribution. -/
noncomputable def poleTerm (g : WeilTestFunction) : ℂ :=
  fourierLaplace g (-Complex.I / 2) + fourierLaplace g (Complex.I / 2)

/-- The completed-zeta digamma integrand in the fixed angular-frequency convention. -/
noncomputable def archimedeanIntegrand (g : WeilTestFunction) (t : ℝ) : ℂ :=
  (((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re -
      Real.log Real.pi : ℝ) : ℂ) * fourierLaplace g t

/-- The explicit convergence obligation for the archimedean integral. -/
def ArchimedeanConvergent (g : WeilTestFunction) : Prop :=
  Integrable (archimedeanIntegrand g)

/-- The completed-zeta archimedean term, gated by its exact integrability obligation. -/
noncomputable def archimedeanTerm (g : WeilTestFunction)
    (_h : ArchimedeanConvergent g) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, archimedeanIntegrand g t

end D5.S3.Weil.PrimePoleTerms
