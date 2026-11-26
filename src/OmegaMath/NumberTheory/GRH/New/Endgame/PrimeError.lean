import OmegaMath.NumberTheory.GRH.Lib.Analytic.Landau.PolarLandau
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! The remainder `primeError` written as an exact finite prime sum. For an integer a and 0 < z ≤ a,
the normalised error at z in the class 1 mod M equals the sum over ν ≤ a, ν ≡ 1, of
Λ(ν)(1−χ_K(ν))(a/ν − a/z)₊, divided by a, less log z/φ(M) and a constant. This standard rewriting of
a weighted prime sum in a residue class as an exact finite identity turns the divisibility sums
∑ λ(ν)(a/ν − a/z)₊ over ν ≤ a into `primeError` at a single z ≤ a. Related work: Davenport,
Multiplicative Number Theory.

Part of: One-sided bound for non-split primes gives a zero-free half-plane (see
New.Endgame.OneSidedCriterion).

This file: Weighted non-split prime sums; their Mellin transform has poles at zeros of
L-functions. -/

noncomputable section

open ArithmeticFunction DirichletCharacter Complex Finset Filter MeasureTheory Nat Real vonMangoldt


variable (d : ℕ) [Fact d.Prime] (M : ℕ)

/-- The weight λ(ν) = Λ(ν)(1 − (ν/d)) for ν ≡ 1 mod M, and 0 otherwise; Λ is von Mangoldt's
function and (ν/d) the Legendre symbol. -/
def lambdaClass ν := @residueClass M 1 ν * (1 - chiK d ν)

/-- The sum y^{−r} ∑_{1≤ν≤y} λ(ν) ν^{r−1}, with λ = `lambdaClass`: for r = 0 it is ∑ λ(ν)/ν, for r
= 1 it is y⁻¹ ∑ λ(ν). -/
def lambdaSum r y := (∑ k ∈ Icc 1 ⌊y⌋₊, lambdaClass d M k / k * k ^ r) / y ^ r

/-- The function φ(M)⁻¹(∑_ξ (L̃′/L̃(s, ξ·(·/d)) − L̃′/L̃(s, ξ)) − 1), summed over the characters
ξ mod M, where L̃ is `entireL`. -/
def logDerivMean [NeZero M] s :=
  (∑ ξ, (logDeriv (entireL (quadTwist ξ d)) s - logDeriv (@entireL M _ ξ) s) - 1) / φ M

/-- The remainder R_M(x) = ∑_{ν≤x} λ(ν)(1/ν − 1/x) − log x/φ(M) − Re `logDerivMean`(1), where λ(ν)
= Λ(ν)(1 − (ν/d)) for ν ≡ 1 mod M, else 0. -/
def primeError [NeZero M]
    x := lambdaSum d M 0 x - lambdaSum d M 1 x - x.log / φ M - (logDerivMean d M 1).re

lemma lambdaClass_nonneg_and_abs_le ν : 0 ≤ lambdaClass d M ν ∧ |lambdaClass d M ν| ≤ 2 * ν := by
  simp [lambdaClass, chiK, Set.indicator, quadraticCharFun, sub_ite]
  grind [vonMangoldt_nonneg, vonMangoldt_le_log, Real.log_le_self]

lemma abs_lambdaSum_exp_le r v : |lambdaSum d M r (rexp v)| ≤ 2 * rexp v := by
  grw [lambdaSum, abs_div, abs_sum_le_sum_abs, sum_le_card_nsmul _ _ (2 * v.exp ^ r)] <;> simp
    +contextual [abs_div, le_floor_iff, exp_nonneg, mul_le_mul, div_le_of_le_mul₀, field,
    lambdaClass_nonneg_and_abs_le, pow_le_pow_left₀, floor_le]

/-- For a prime d, the real part of `logDerivMean` for modulus M = 1 at s = 1 is −1 − ℓ, where ℓ =
`chowlaSelbergConst` d = γ − Re L′/L(1, (·/d)) and γ is Euler's constant. -/
lemma re_logDerivMean_one : (logDerivMean d 1 1).re = -1 - chowlaSelbergConst d := by
  simp [logDerivMean, chowlaSelbergConst, logDeriv, level_one, show @entireL 1 _ 1 = riemannZeta₁ by
    simp_all [entireL, Function.update_eq_iff, riemannZeta_eq_inv_sub_mul]]; ring

variable [NeZero M] {d M}

/-- For 0 < z ≤ A, `primeError d M z` in terms of the sum ∑_{ν ≤ A} λ(ν)(A/ν − A/z)⁺, where λ is
`lambdaClass d M`. -/
lemma primeError_eq_sum (A : ℕ) {z : ℝ} (u : 0 < z) (h : z ≤ A) : primeError d M z = ∑ ν ∈ Icc 1 A,
  lambdaClass d M ν * (A / ν - A / z)⁺ / A - z.log / φ M - re (logDerivMean d M 1) := by
  have := u.trans_le h
  simp [primeError, lambdaSum, sum_div, ← sum_sub_distrib]; apply sum_congr_of_eq_on_inter <;>
    simp +contextual [le_floor_iff u.le, field] <;> rify <;> grind

/-- For d ≡ 7 mod 8 prime to M, v ↦ R_M(e^v) is polar (`IsPolar`) with residue at s equal to
∑_ξ (ord_s L̃(ξ) − ord_s L̃(ξ(·/d))) / (φ(M) s(1 − s)), ξ over the characters mod M, L̃ =
`entireL`. -/
lemma isPolar_primeError (hd : d % 8 = 7) (h : M.Coprime d) : IsPolar (primeError d M ·.exp) fun s ↦
    (∑ ξ, (analyticOrderNatAt (@entireL M _ ξ) s - analyticOrderNatAt (entireL (quadTwist ξ d))
  s : ℂ)) / φ M / (s * (1 - s)) := by
  let κ := (logDerivMean d M 1).re
  have A : AnalyticOnNhd ℂ (fun s ↦ logDerivMean d M s / s - κ) {s | 1 ≤ s.re} := fun _ _ ↦ by
    fun_prop (disch := grind [entireL_ne_zero, zero_re]) [logDerivMean, logDeriv]
  refine ⟨by fun_prop [primeError, lambdaSum], |κ| + 5, fun s ↦ (logDerivMean d M s / s - κ) /
    (s - 1), fun _ ↦ by fun_prop [logDerivMean], fun v a ↦ (abs_sub ..).trans ?_, ?q,
  -- real on `(2, ∞)`, hence at `1`
  have := @ext _ 0 (by simp [κ]) ((A.mono (by aesop)
    ).im_ofReal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ici (by simp) (.mono
    (lt_mem_nhds (lt_add_one _)) fun x u ↦ congr(im $((div_eq_iff (by aesop)).1 (?q x u))).trans
    (by norm_cast)) (le_refl (1 : ℝ)))
  ⟨?B, fun ρ _ ↦ have I := (@continuousWithinAt_id _ _ {ρ}ᶜ ρ).sub_const
    if e : 1 = ρ then e ▸ .trans_eq (tendsto_inf_left (?B 1 (by simp)).continuousAt) (by simp) else
    by convert ((((((tendsto_finsetSum ⊤ fun ξ _ ↦ (tendsto_sub_mul_logDeriv_entireL (@quadTwist M ξ
      d _)).2.sub (tendsto_sub_mul_logDeriv_entireL ξ).2).sub (I ρ)).div_const (φ M)).div
      (I 0) ?_).sub ((I ρ).mul_const ↑κ)).div
      (I 1) ?_) using 2 <;> simp [logDerivMean, ← mul_sum] <;> grind [zero_re]⟩⟩
  grw [abs_sub, v.log_exp, ← @NeZero.one_le (φ _), add_mul,
    ← le_mul_of_one_le_right] <;> grind [add_one_le_exp, abs_lambdaSum_exp_le]
  intro s u
  have L := @laplace_pow (s - 1) (by simp [u.trans'])
  have e r : (s + r - 1) * ∫ v in _, lambdaSum d M r (rexp v) * (v - s * v).exp = _ := .trans (by
    congr 1; convert integral_comp_exp_Ioi _ 0 <;> simp [lambdaSum, field, cpow_add, cpow_neg,
      le_of_lt,
    Complex.exp_sub, cpow_def _ s, Complex.log_exp, mul_comm s, pi_pos]) ((@LSeries_eq_mul_integral'
    _ (1 + r) (by bound) _ (by simp; bound) (.of_bound 2 (.mono (Ioi_mem_atTop 0) fun n _ ↦ by
    simpa [lambdaSum, *, div_le_iff₀, abs_div, rpow_add, field, lambdaClass_nonneg_and_abs_le,
      Real.exp_log, abs_of_nonneg] using abs_lambdaSum_exp_le d M r (.log n)))).symm.trans
    (((LSeriesHasSum.sum (S := ⊤) fun ξ _ ↦ (@LSeriesHasSum_mul_vonMangoldt M ξ _ s (by bound)).sub
    (LSeriesHasSum_mul_vonMangoldt (quadTwist ξ d) (by bound))).div_const (φ M)).congr_fun
    fun n ↦ by by_cases n = 0 <;> simp [*, cpow_sub, field, cpow_add, lambdaClass,
    chiK_eq_legendreSym, residueClass_apply, mod_cast (quadTwist_apply · d n), ← sum_mul]).tsum_eq)
  obtain := L 0, L 1, Integrable.of_integral_ne_zero ((L 0).trans_ne (by aesop)),
    Integrable.of_integral_ne_zero ((L 1).trans_ne (by aesop)),
    fun r ↦ integrableOn_laplace_of_abs_le
    (by fun_prop [lambdaSum]) (fun v _ ↦ abs_lambdaSum_exp_le d M r _) u
  simp [primeError, κ, IntegrableOn, sub_mul, div_eq_inv_mul, logDerivMean, mul_assoc,
    quadTwist_ne_one _ d (by lia) h] at *
  simp (disch := fun_prop) [integral_sub, *]
  linear_combination (norm := field (disch := grind [zero_re, one_re])) e 1 / s - e 0 / (s - 1)
  grind [ofReal_one]
