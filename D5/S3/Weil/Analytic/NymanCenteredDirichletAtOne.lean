/- GID: D5/S3/Weil/Analytic/NymanCenteredDirichletAtOne
   generality: I
   mirror-B: none(waiver:logarithmic-moment-support)
   mirror-E: none(waiver:logarithmic-moment-analysis)
   anchors: []
   utility: none
   digest: The centered prime Dirichlet series has an exact finite part at one. -/

import D5.S3.Weil.Analytic.NymanCenteredPrimeDirichlet
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! The right boundary value of the centered prime Dirichlet series. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Asymptotics Filter
open scoped Topology

namespace NymanCenteredDirichletAtOne

open NymanCenteredPrimeDirichlet (centeredPrimeCoefficientComplex)
open NymanPrimeDilations (centeredPrimeCoefficient)

private def nonprimeMangoldt (n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n

private def nonprimeMangoldtComplex (n : ℕ) : ℂ := nonprimeMangoldt n

private def mangoldtComplex (n : ℕ) : ℂ := (vonMangoldt n : ℝ)

/-- At one, the nonprime Mangoldt contribution comes from prime powers of degree at least two. -/
def primePowerDirichletAtOne : ℝ :=
  ∑' n : ℕ, nonprimeMangoldt n / (n : ℝ)

/-- The finite value of the centered prime Dirichlet series at the right boundary. -/
def centeredPrimeDirichletAtOne : ℝ :=
  1 - 2 * Real.eulerMascheroniConstant - primePowerDirichletAtOne

theorem centeredPrimeDirichletAtOne_neg : centeredPrimeDirichletAtOne < 0 := by
  have h : 0 ≤ primePowerDirichletAtOne := by
    apply tsum_nonneg
    intro n
    apply div_nonneg ?_ (Nat.cast_nonneg n)
    unfold nonprimeMangoldt
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  unfold centeredPrimeDirichletAtOne
  linarith only [h, Real.one_half_lt_eulerMascheroniConstant]

private theorem summable_nonprimeMangoldt_div :
    Summable (fun n : ℕ => nonprimeMangoldt n / (n : ℝ)) := by
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  convert h using 1
  funext n
  have hn : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [nonprimeMangoldt, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator, hn]

private theorem nonprime_term_at_one (n : ℕ) :
    LSeries.term nonprimeMangoldtComplex 1 n =
      ((nonprimeMangoldt n / (n : ℝ) : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one, Complex.ofReal_div,
      Complex.ofReal_natCast] <;> rfl

private theorem nonprime_lSeriesSummable_at_one :
    LSeriesSummable nonprimeMangoldtComplex (1 : ℂ) := by
  change Summable (fun n => LSeries.term nonprimeMangoldtComplex 1 n)
  rw [show (fun n => LSeries.term nonprimeMangoldtComplex 1 n) =
      (fun n => ((nonprimeMangoldt n / (n : ℝ) : ℝ) : ℂ)) from funext nonprime_term_at_one]
  exact Complex.summable_ofReal.mpr summable_nonprimeMangoldt_div

private theorem tendsto_nonprime_lSeries :
    Tendsto (fun σ : ℝ => LSeries nonprimeMangoldtComplex (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (primePowerDirichletAtOne : ℂ)) := by
  unfold LSeries
  rw [primePowerDirichletAtOne, Complex.ofReal_tsum]
  simp_rw [← nonprime_term_at_one]
  refine tendsto_tsum_of_dominated_convergence nonprime_lSeriesSummable_at_one.norm ?_ ?_
  · intro n
    by_cases hn : n = 0
    · simp [hn, LSeries.term_zero]
    simp only [LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hcont := (continuous_const_cpow' hnC).comp Complex.continuous_ofReal
    have hterm :
        ContinuousAt (fun σ : ℝ => nonprimeMangoldtComplex n / (n : ℂ) ^ (σ : ℂ)) 1 :=
      continuousAt_const.div hcont.continuousAt
        (by simpa only [Complex.ofReal_one, Complex.cpow_one] using hnC)
    exact hterm.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ n
    have hre : (1 : ℂ).re ≤ (σ : ℂ).re := by
      simpa only [Complex.one_re, Complex.ofReal_re] using (Set.mem_Ioi.mp hσ).le
    exact LSeries.norm_term_le_of_re_le_re nonprimeMangoldtComplex hre n

private theorem delta_lSeriesSummable (s : ℂ) : LSeriesSummable LSeries.delta s := by
  change Summable (fun n => LSeries.term LSeries.delta s n)
  rw [show (fun n => LSeries.term LSeries.delta s n) =
      (fun n => if n = 1 then (1 : ℂ) else 0) from funext (LSeries.term_delta s)]
  refine summable_of_ne_finset_zero (s := ({1} : Finset ℕ)) fun n hn => ?_
  have hn' : n ≠ 1 := by simpa only [Finset.mem_singleton] using hn
  simp [hn']

private theorem centeredPrime_lSeries_eq {σ : ℝ} (hσ : 1 < σ) :
    LSeries centeredPrimeCoefficientComplex (σ : ℂ) =
      1 - deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - riemannZeta (σ : ℂ) -
        LSeries nonprimeMangoldtComplex (σ : ℂ) := by
  let s : ℂ := σ
  have hs : 1 < s.re := by simpa [s] using hσ
  have hcoef :
      LSeries centeredPrimeCoefficientComplex s =
        LSeries
          (mangoldtComplex - nonprimeMangoldtComplex - (1 : ℕ → ℂ) + LSeries.delta) s := by
    apply LSeries_congr _ s
    intro n hn
    change (centeredPrimeCoefficient n : ℂ) =
      mangoldtComplex n - nonprimeMangoldtComplex n - 1 + LSeries.delta n
    by_cases h1 : n = 1
    · subst n
      simp [centeredPrimeCoefficient, mangoldtComplex, nonprimeMangoldtComplex, nonprimeMangoldt,
        Nat.not_prime_one, LSeries.delta, vonMangoldt_apply_one]
    have h2 : 1 < n := by omega
    by_cases hp : n.Prime
    · simp [centeredPrimeCoefficient, h2, hp, mangoldtComplex, nonprimeMangoldtComplex,
        nonprimeMangoldt, LSeries.delta, h1, vonMangoldt_apply_prime hp, Complex.ofReal_sub]
    · simp [centeredPrimeCoefficient, h2, hp, mangoldtComplex, nonprimeMangoldtComplex,
        nonprimeMangoldt, LSeries.delta, h1]
  have hΛ : LSeriesSummable mangoldtComplex s := LSeriesSummable_vonMangoldt hs
  have hQ : LSeriesSummable nonprimeMangoldtComplex s :=
    nonprime_lSeriesSummable_at_one.of_re_le_re (by simpa only [Complex.one_re] using hs.le)
  have hOne : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hδ := delta_lSeriesSummable s
  have hz : LSeries mangoldtComplex s = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries centeredPrimeCoefficientComplex s = _
  rw [hcoef, LSeries_add ((hΛ.sub hQ).sub hOne) hδ, LSeries_sub (hΛ.sub hQ) hOne,
    LSeries_sub hΛ hQ, LSeries_one_eq_riemannZeta hs,
    congrFun LSeries_delta s, Pi.one_apply, hz, neg_div]
  <;> ring

private theorem real_right_to_complex_punctured :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  refine Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin ?_
  intro σ hσ
  change (σ : ℂ) ≠ 1
  intro he
  have h : σ = 1 := by simpa using congrArg Complex.re he
  exact (Set.mem_Ioi.mp hσ).ne' h

private theorem tendsto_logDeriv_regularPart :
    Tendsto (fun σ : ℝ =>
      deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have h := (isLittleO_one_iff ℂ).mp
    log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [Function.comp_def] using h.comp real_right_to_complex_punctured

private theorem tendsto_zeta_regularPart :
    Tendsto (fun σ : ℝ => riemannZeta (σ : ℂ) - ((σ : ℂ) - 1)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  simpa only [one_div, Function.comp_def] using
    tendsto_riemannZeta_sub_one_div.comp real_right_to_complex_punctured

/-- The pole of the prime series cancels against the pole for integer counting. -/
theorem tendsto_centeredPrimeCoefficient_lSeries_at_one :
    Tendsto (fun σ : ℝ => LSeries centeredPrimeCoefficientComplex (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (centeredPrimeDirichletAtOne : ℂ)) := by
  have hOne : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    tendsto_const_nhds
  have hbound :
      Tendsto
        (fun σ : ℝ =>
          1 - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹) -
            (riemannZeta (σ : ℂ) - ((σ : ℂ) - 1)⁻¹) -
              LSeries nonprimeMangoldtComplex (σ : ℂ))
        (𝓝[>] (1 : ℝ))
        (𝓝 ((1 : ℂ) - (Real.eulerMascheroniConstant : ℂ) -
          (Real.eulerMascheroniConstant : ℂ) - (primePowerDirichletAtOne : ℂ))) := by
    have h := (((hOne.sub tendsto_logDeriv_regularPart).sub tendsto_zeta_regularPart).sub
      tendsto_nonprime_lSeries)
    change Tendsto
      (fun σ : ℝ =>
        1 - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹) -
          (riemannZeta (σ : ℂ) - ((σ : ℂ) - 1)⁻¹) -
            LSeries nonprimeMangoldtComplex (σ : ℂ))
      (𝓝[>] (1 : ℝ))
      (𝓝 ((1 : ℂ) - (Real.eulerMascheroniConstant : ℂ) -
        (Real.eulerMascheroniConstant : ℂ) - (primePowerDirichletAtOne : ℂ))) at h
    exact h
  have hc : ((1 : ℂ) - (Real.eulerMascheroniConstant : ℂ) -
      (Real.eulerMascheroniConstant : ℂ) - (primePowerDirichletAtOne : ℂ)) =
        (centeredPrimeDirichletAtOne : ℂ) := by
    unfold centeredPrimeDirichletAtOne
    push_cast
    ring
  rw [hc] at hbound
  refine hbound.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [centeredPrime_lSeries_eq (Set.mem_Ioi.mp hσ)]
  ring

end NymanCenteredDirichletAtOne
