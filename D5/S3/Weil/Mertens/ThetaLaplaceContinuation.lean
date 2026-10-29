/- GID: D5/S3/Weil/Mertens/ThetaLaplaceContinuation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ThetaLaplaceContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Chebyshev theta Laplace transform and multiplicity-dependent poles. -/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Meromorphic.Order
import D5.S3.Weil.ZetaSeam.StatementSeam

namespace D5.S3.Weil.Mertens.ThetaLaplaceContinuation

open Real Set MeasureTheory Filter Asymptotics Complex
open scoped BigOperators Topology

noncomputable section

/-- The prime-power correction has no prime terms. -/
def b (n : ℕ) : ℝ := if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

/-- The actual absolutely convergent prime-power correction. -/
def C (z : ℂ) : ℂ := LSeries (fun n => (b n : ℂ)) z

/-- The actual Chebyshev error in logarithmic coordinates. -/
def q (u : ℝ) : ℝ := Real.exp (-u) * (Chebyshev.theta (Real.exp u) - Real.exp u)

/-- The cutoff Laplace integral, interpreted as a Lebesgue set integral. -/
def Q (u₀ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi u₀, Complex.exp (-s * (u : ℂ)) * (q u : ℂ)

/-- The oriented finite-cutoff correction. -/
def A (u₀ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..u₀,
    Complex.exp (-(s + 1) * (u : ℂ)) *
      ((Chebyshev.theta (Real.exp u) - Real.exp u : ℝ) : ℂ)

/-- Normalized-zeta continuation; its value at zero uses the normalized factor. -/
def M (u₀ : ℝ) (s : ℂ) : ℂ :=
  -(1 + logDeriv riemannZeta₁ (1 + s) + C (1 + s)) / (1 + s) - A u₀ s

/-- The continuation half-plane. -/
def D : Set ℂ := {s | -(1 / 2 : ℝ) < s.re}

private lemma b_nonneg (n : ℕ) : 0 ≤ b n := by
  unfold b
  split_ifs <;> exact le_rfl <|> exact ArithmeticFunction.vonMangoldt_nonneg

private lemma b_prefix (x : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, b k) = Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  change (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, b k) = _
  apply Finset.sum_congr rfl
  intro k hk
  simp only [b]
  split_ifs <;> simp_all

private lemma b_prefix_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, b k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
  have hprefix := b_prefix (n : ℝ)
  simp only [Nat.floor_natCast] at hprefix
  rw [hprefix, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  simpa only [Real.sqrt_eq_rpow] using hK (n : ℝ)

private lemma c_summable {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    LSeriesSummable (fun n => (b n : ℂ)) z :=
  LSeriesSummable_of_sum_norm_bigO_and_nonneg b_prefix_bigO b_nonneg (by norm_num) hz

private lemma c_analytic : AnalyticOnNhd ℂ C {z | (1 / 2 : ℝ) < z.re} := by
  have hab : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ (1 / 2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => c_summable (by simpa using hy))
  intro z hz
  exact LSeries_analyticOnNhd _ z (hab.trans_lt (by exact_mod_cast hz))

private lemma c_mellin {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    C z = z * ∫ x in Ioi (1 : ℝ),
      ((Chebyshev.psi x - Chebyshev.theta x : ℝ) : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg b (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hz b_prefix_bigO b_nonneg
  simpa only [C, ← Complex.ofReal_sum, b_prefix] using h

private lemma mangoldt_prefix_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  have hsum : (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
    change (∑ k ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt k) = _
    simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [hsum, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
    Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

private lemma psi_mellin {z : ℂ} (hz : 1 < z.re) :
    -logDeriv riemannZeta z = z * ∫ x in Ioi (1 : ℝ),
      (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) (by norm_num : (0 : ℝ) ≤ 1)
    hz mangoldt_prefix_bigO (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  rw [show -logDeriv riemannZeta z =
      LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z by
    simpa only [logDeriv_apply, neg_div, ArithmeticFunction.natCoe_apply] using hL.symm]
  simpa only [← Complex.ofReal_sum, Chebyshev.psi] using h

end
end D5.S3.Weil.Mertens.ThetaLaplaceContinuation
