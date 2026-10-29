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
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Meromorphic.Order
import D5.S3.Weil.ZetaSeam.StatementSeam

/-! The actual theta error, its prime-power correction and cutoff transform. -/

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
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

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
  convert h using 2
  congr 1
  ext x
  congr 1
  rw [← Complex.ofReal_sum]
  rfl

private lemma prime_power_term (z : ℂ) (p : Nat.Primes) (j : ℕ) :
    LSeries.term (fun n => (b n : ℂ)) z ((p : ℕ) ^ (j + 2)) =
      (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-((j + 2 : ℕ) : ℂ) * z) := by
  rw [LSeries.term_def₀ (by simp [b]), b,
    ite_eq_right (Nat.Prime.not_prime_pow (by omega : 2 ≤ j + 2)),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega : j + 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  push_cast
  congr 1
  rw [← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring

private lemma c_prime_powers {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    Summable (fun pj : Nat.Primes × ℕ =>
      (Real.log (pj.1 : ℝ) : ℂ) * (pj.1 : ℂ) ^ (-((pj.2 + 2 : ℕ) : ℂ) * z)) ∧
    C z = ∑' p : Nat.Primes, ∑' j : ℕ,
      (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-((j + 2 : ℕ) : ℂ) * z) := by
  have hF := c_summable hz
  have hinj : Function.Injective (fun pj : Nat.Primes × ℕ =>
      (pj.1 : ℕ) ^ (pj.2 + 2)) :=
    Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective |>.comp
      (Function.Injective.prodMap (fun ⦃_ _⦄ => id) (add_left_injective 1))
  refine ⟨(hF.comp_injective hinj).congr (fun pj => prime_power_term z pj.1 pj.2), ?_⟩
  have hsupp : Function.support (LSeries.term (fun n => (b n : ℂ)) z) ⊆
      {n | IsPrimePow n} := by
    intro n hn
    by_contra hnpp
    apply hn
    rw [LSeries.term_def₀ (by simp [b])]
    simp [b, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnpp]
  have heq := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hF hsupp
  have hprime (p : Nat.Primes) : LSeries.term (fun n => (b n : ℂ)) z p = 0 := by
    simp [LSeries.term, b, p.prop]
  simpa only [C, LSeries, hprime, tsum_zero, zero_add, prime_power_term] using heq

private lemma q_measurable : Measurable q := by
  unfold q
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u))).mul
    ((Chebyshev.theta_mono.measurable.comp (by fun_prop)).sub (by fun_prop))

private lemma q_bound (u : ℝ) : ‖q u‖ ≤ Real.log 4 + 1 := by
  have he := (Real.exp_pos u).le
  have ht := Chebyshev.theta_nonneg (Real.exp u)
  have hb := Chebyshev.theta_le_log4_mul_x he
  rw [q, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  calc
    Real.exp (-u) * |Chebyshev.theta (Real.exp u) - Real.exp u|
        ≤ Real.exp (-u) * (Chebyshev.theta (Real.exp u) + Real.exp u) := by
      gcongr
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg ht, abs_of_nonneg he])
    _ ≤ Real.exp (-u) * (Real.log 4 * Real.exp u + Real.exp u) := by gcongr
    _ = Real.log 4 + 1 := by
      rw [← add_one_mul, mul_left_comm, ← Real.exp_add]
      simp

private def F (s : ℂ) (u : ℝ) : ℂ := Complex.exp (-s * (u : ℂ)) * (q u : ℂ)

private lemma F_measurable (s : ℂ) : Measurable (F s) :=
  (by fun_prop : Measurable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))).mul
    q_measurable.complex_ofReal

private lemma F_integrable (u₀ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (F s) (Ioi u₀) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) u₀).mul_bdd
    q_measurable.complex_ofReal.aestronglyMeasurable.restrict
    (Eventually.of_forall fun u => by simpa using q_bound u)

private lemma F_eq (s : ℂ) (u : ℝ) :
    F s u = Complex.exp (-(s + 1) * (u : ℂ)) *
      ((Chebyshev.theta (Real.exp u) - Real.exp u : ℝ) : ℂ) := by
  unfold F q
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma A_eq (u₀ : ℝ) (s : ℂ) : A u₀ s = ∫ u in (0 : ℝ)..u₀, F s u := by
  unfold A
  apply intervalIntegral.integral_congr
  intro u hu
  exact (F_eq s u).symm

private lemma F_interval_integrable (u₀ : ℝ) (s : ℂ) :
    IntervalIntegrable (F s) volume 0 u₀ := by
  obtain ⟨K, hK⟩ := (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) u₀)).exists_bound_of_continuousOn
    (f := fun u : ℝ => Complex.exp (-s * (u : ℂ))) (by fun_prop)
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := K * (Real.log 4 + 1))
    (by simp) (F_measurable s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [F, norm_mul]
  exact mul_le_mul (hK u (uIoc_subset_uIcc hu)) (by simpa using q_bound u)
    (norm_nonneg _) (le_trans (norm_nonneg _) (hK u (uIoc_subset_uIcc hu)))

private lemma F_hasDeriv (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => F z u) (-(u : ℂ) * F s u) s := by
  have h := (((hasDerivAt_id s).neg).mul_const (u : ℂ)).cexp.mul_const (q u : ℂ)
  convert h using 1 <;> dsimp [F] <;> ring

private lemma A_differentiable (u₀ : ℝ) : Differentiable ℂ (A u₀) := by
  intro s
  obtain ⟨K, hK⟩ := ((isCompact_closedBall s (1 : ℝ)).prod
    (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) u₀))).exists_bound_of_continuousOn
      (f := fun v : ℂ × ℝ => -(v.2 : ℂ) * Complex.exp (-v.1 * (v.2 : ℂ)))
      (by fun_prop)
  have hmeas (z : ℂ) : Measurable (fun u : ℝ => -(u : ℂ) * F z u) :=
    (by fun_prop : Measurable (fun u : ℝ => -(u : ℂ))).mul (F_measurable z)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun z u => -(u : ℂ) * F z u)
    (bound := fun _ : ℝ => K * (Real.log 4 + 1))
    (a := (0 : ℝ)) (b := u₀) (μ := volume) (Metric.ball_mem_nhds s zero_lt_one)
    (Eventually.of_forall fun z => (F_measurable z).aestronglyMeasurable.restrict)
    (F_interval_integrable u₀ s) (hmeas s).aestronglyMeasurable.restrict ?_
    intervalIntegrable_const (Eventually.of_forall fun u _ z _ => F_hasDeriv u z)
  · rw [show A u₀ = (fun z => ∫ u in (0 : ℝ)..u₀, F z u) by funext z; exact A_eq u₀ z]
    exact h.2.differentiableAt
  · filter_upwards with u
    intro hu z hz
    rw [F, ← mul_assoc, norm_mul]
    have hb := hK (z, u) ⟨Metric.ball_subset_closedBall hz, uIoc_subset_uIcc hu⟩
    exact mul_le_mul hb (by simpa using q_bound u) (norm_nonneg _)
      (le_trans (norm_nonneg _) hb)

private lemma Q_cutoff (u₀ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Q u₀ s = Q 0 s - A u₀ s := by
  rw [A_eq]
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (F_integrable 0 hs) (F_integrable u₀ hs)
  change Q 0 s - Q u₀ s = _ at h
  linear_combination -h

private def primeCoeff (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n - b n

private lemma primeCoeff_nonneg (n : ℕ) : 0 ≤ primeCoeff n := by
  unfold primeCoeff b
  split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

private lemma primeCoeff_prefix (x : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, primeCoeff k) = Chebyshev.theta x := by
  simp only [primeCoeff, Finset.sum_sub_distrib, b_prefix]
  have h : (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi x := rfl
  rw [h]
  ring

private lemma primeCoeff_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoeff k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine IsBigO.of_bound (Real.log 4) (Eventually.of_forall fun n => ?_)
  have hp := primeCoeff_prefix (n : ℝ)
  simp only [Nat.floor_natCast] at hp
  rw [hp, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.theta_nonneg _),
    Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)

private lemma theta_mellin {z : ℂ} (hz : 1 < z.re) :
    -logDeriv riemannZeta z - C z = z * ∫ x in Ioi (1 : ℝ),
      (Chebyshev.theta x : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg primeCoeff
    (by norm_num : (0 : ℝ) ≤ 1) hz primeCoeff_bigO primeCoeff_nonneg
  have hcoeff : (fun n => (primeCoeff n : ℂ)) =
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) - (fun n => (b n : ℂ)) := by
    ext n
    simp [primeCoeff]
  rw [hcoeff, LSeries_sub
    (by simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeriesSummable_vonMangoldt hz)
    (c_summable (by linarith))] at h
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  simpa only [← Complex.ofReal_sum, primeCoeff_prefix, C, logDeriv_apply,
    neg_div, ArithmeticFunction.natCoe_apply, hL] using h

private lemma cpow_exp (u : ℝ) (z : ℂ) :
    (Real.exp u : ℂ) ^ z = Complex.exp ((u : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

private lemma theta_exp_point (s : ℂ) (u : ℝ) :
    Real.exp u • ((Chebyshev.theta (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1))) =
      F s u + Complex.exp (-s * (u : ℂ)) := by
  rw [cpow_exp, F_eq, Real.smul_def, Complex.ofReal_sub, Complex.ofReal_exp]
  have he : Complex.exp (-(s + 1) * (u : ℂ)) * Complex.exp (u : ℂ) =
      Complex.exp (-s * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hprod : Complex.exp (u : ℂ) *
      Complex.exp ((u : ℂ) * (-((1 + s) + 1))) =
      Complex.exp (-(s + 1) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_left_comm, hprod]
  linear_combination he

private lemma Q_zero_raw {s : ℂ} (hs : 0 < s.re) :
    Q 0 s = (-logDeriv riemannZeta (1 + s) - C (1 + s)) / (1 + s) - 1 / s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hm := theta_mellin (z := 1 + s) (by simp; linarith)
  have he := integral_comp_exp_Ioi
    (fun x : ℝ => (Chebyshev.theta x : ℂ) * (x : ℂ) ^ (-((1 + s) + 1))) 0
  simp only [Real.exp_zero] at he
  have hpt : (fun u : ℝ => Real.exp u • ((Chebyshev.theta (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1)))) =
      (fun u => F s u + Complex.exp (-s * (u : ℂ))) := funext (theta_exp_point s)
  rw [hpt, integral_add (F_integrable 0 hs)
    (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0)] at he
  have hem : (∫ u in Ioi (0 : ℝ), Complex.exp (-s * (u : ℂ))) = 1 / s := by
    simpa using integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  rw [hem] at he
  change Q 0 s + 1 / s = _ at he
  rw [← he] at hm
  apply (eq_div_iff hz0).mpr at hm
  linear_combination -hm

private lemma normalized_logDeriv {z : ℂ} (hz : z ≠ 1) (hn : riemannZeta₁ z ≠ 0) :
    logDeriv riemannZeta z = -(z - 1)⁻¹ + logDeriv riemannZeta₁ z := by
  rw [logDeriv_apply, logDeriv_apply, riemannZeta_eq_inv_sub_mul hz,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hz]
  field_simp [sub_ne_zero.mpr hz, hn]
  <;> ring

private lemma Q_eq_M (u₀ : ℝ) {s : ℂ} (hs : 0 < s.re) : Q u₀ s = M u₀ s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hz1 : 1 + s ≠ 1 := by simpa using hs0
  have hn : riemannZeta₁ (1 + s) ≠ 0 := by
    intro hn
    have he := riemannZeta_eq_inv_sub_mul hz1
    rw [hn, mul_zero] at he
    exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith) he
  rw [Q_cutoff u₀ hs, Q_zero_raw hs, normalized_logDeriv hz1 hn]
  unfold M
  field_simp [hs0, hz0]
  <;> ring

private lemma M_meromorphic (u₀ : ℝ) : MeromorphicOn (M u₀) D := by
  intro s hs
  have hC : AnalyticAt ℂ (fun s => C (1 + s)) s :=
    (c_analytic (1 + s) (by simp; change -(1 / 2 : ℝ) < s.re at hs; linarith)).comp
      (by fun_prop)
  have hz : MeromorphicAt (fun s => logDeriv riemannZeta₁ (1 + s)) s :=
    ((differentiable_riemannZeta₁.analyticAt (1 + s)).meromorphicAt.logDeriv).comp_analyticAt
      (by fun_prop)
  exact (((MeromorphicAt.const 1 s).add hz |>.add hC.meromorphicAt).neg.div
    (by fun_prop)).sub (A_differentiable u₀ |>.analyticAt s |>.meromorphicAt)

private lemma M_analytic_zero (u₀ : ℝ) : AnalyticAt ℂ (M u₀) 0 := by
  have hz : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 :=
    (differentiable_riemannZeta₁.analyticAt 1).deriv.div
      (differentiable_riemannZeta₁.analyticAt 1) (by simp)
  have hc := c_analytic (1 : ℂ) (by norm_num)
  have ha := A_differentiable u₀ |>.analyticAt 0
  unfold M
  apply AnalyticAt.sub _ ha
  apply AnalyticAt.div _ (by fun_prop) (by norm_num)
  apply AnalyticAt.neg
  apply AnalyticAt.add
  · apply AnalyticAt.add analyticAt_const
    exact hz.comp (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 + s) 0)
  · exact hc.comp (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 + s) 0)

end
end D5.S3.Weil.Mertens.ThetaLaplaceContinuation
