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
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
  have he : LSeries (fun n => (primeCoeff n : ℂ)) z =
      -logDeriv riemannZeta z - C z := by
    rw [hcoeff, LSeries_sub
      (by simpa only [ArithmeticFunction.natCoe_apply] using
        ArithmeticFunction.LSeriesSummable_vonMangoldt hz)
      (c_summable (by linarith))]
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    simpa only [C, logDeriv_apply, neg_div, ArithmeticFunction.natCoe_apply] using
      congrArg (fun w => w - C z) hL
  rw [he] at h
  simpa only [← Complex.ofReal_sum, primeCoeff_prefix] using h

private lemma cpow_exp (u : ℝ) (z : ℂ) :
    (Real.exp u : ℂ) ^ z = Complex.exp ((u : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

private lemma theta_exp_point (s : ℂ) (u : ℝ) :
    Real.exp u • ((Chebyshev.theta (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1))) =
      F s u + Complex.exp (-s * (u : ℂ)) := by
  rw [cpow_exp, F_eq, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_exp]
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
  have hd : (-logDeriv riemannZeta (1 + s) - C (1 + s)) / (1 + s) =
      Q 0 s + 1 / s := by
    rw [hm]
    field_simp
  linear_combination -hd

private lemma normalized_logDeriv {z : ℂ} (hz : z ≠ 1) (hn : riemannZeta₁ z ≠ 0) :
    logDeriv riemannZeta z = -(z - 1)⁻¹ + logDeriv riemannZeta₁ z := by
  rw [logDeriv_apply, logDeriv_apply, riemannZeta_eq_inv_sub_mul hz,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hz]
  field_simp [sub_ne_zero.mpr hz, hn]

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
  ring

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
    exact hz.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 + s) 0) (by simp)
  · exact hc.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 + s) 0) (by simp)

private lemma Q_hasDeriv (u₀ : ℝ) (hu₀ : 0 ≤ u₀) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))
      (Ioi u₀) ∧
    HasDerivAt (Q u₀)
      (-(∫ u in Ioi u₀, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s := by
  have heps : 0 < s.re / 2 := by linarith
  have hb : IntegrableOn (fun u : ℝ =>
      u * Real.exp (-(s.re / 2) * u) * (Real.log 4 + 1)) (Ioi u₀) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num) heps
    simpa only [IntegrableOn, Real.rpow_one] using
      (h.mono_set (Ioi_subset_Ioi hu₀)).mul_const (Real.log 4 + 1)
  have hdmeas : Measurable (fun u : ℝ => -(u : ℂ) * F s u) :=
    (by fun_prop : Measurable (fun u : ℝ => -(u : ℂ))).mul (F_measurable s)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun z u => -(u : ℂ) * F z u)
    (μ := volume.restrict (Ioi u₀))
    (s := {z : ℂ | s.re / 2 < z.re})
    (bound := fun u : ℝ => u * Real.exp (-(s.re / 2) * u) * (Real.log 4 + 1))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith))
    (Eventually.of_forall fun z => (F_measurable z).aestronglyMeasurable.restrict)
    (F_integrable u₀ hs) hdmeas.aestronglyMeasurable.restrict ?_ hb
    (Eventually.of_forall fun u z _ => F_hasDeriv u z)
  · constructor
    · change Integrable _ (volume.restrict (Ioi u₀))
      convert h.1.neg using 1
      ext u
      simp [F, mul_assoc]
    · change HasDerivAt (fun z => ∫ u in Ioi u₀, F z u) _ s
      simpa only [F, neg_mul, integral_neg, mul_assoc] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu0 : 0 ≤ u := hu₀.trans hu.le
    dsimp [F]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu0, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hz.le) hu0)) hu0)
      (by simpa using q_bound u) (abs_nonneg _)
      (by positivity)

private lemma factor_logDeriv {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g a) (hg0 : g a ≠ 0)
    (heq : f =ᶠ[𝓝 a] fun z => (z - a) ^ m * g z) :
    AnalyticAt ℂ (logDeriv g) a ∧
    logDeriv f =ᶠ[𝓝[≠] a] fun z => (m : ℂ) / (z - a) + logDeriv g z := by
  refine ⟨hg.deriv.div hg hg0, ?_⟩
  have hne := hg.continuousAt.eventually_ne hg0
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds heq.eventually_nhds,
    mem_nhdsWithin_of_mem_nhds hne,
    mem_nhdsWithin_of_mem_nhds hg.eventually_analyticAt] with z hz hfz hgz hgan
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  have hfz' : f =ᶠ[𝓝 z] (fun z => (z - a) ^ m * g z) := hfz
  have hld : logDeriv f z = logDeriv (fun z => (z - a) ^ m * g z) z := by
    simp only [logDeriv_apply, hfz'.deriv_eq, hfz'.self_of_nhds]
  rw [hld, logDeriv_fun_mul (f := fun z : ℂ => (z - a) ^ m) (g := g) z
    (pow_ne_zero _ hza) hgz (by fun_prop) hgan.differentiableAt]
  congr 1
  rw [show (fun z : ℂ => (z - a) ^ m) = (fun w : ℂ => w ^ m) ∘ (fun z => z - a) from rfl,
    logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
  simp

private lemma pole_orders {f H : ℂ → ℂ} {a α : ℂ}
    (hH : AnalyticAt ℂ H a) (hα : α ≠ 0)
    (heq : f =ᶠ[𝓝[≠] a] fun z => α / (z - a) + H z) :
    (fun z => -deriv f z + f z) =ᶠ[𝓝[≠] a]
      (fun z => α / (z - a) ^ 2 + α / (z - a) + H z - deriv H z) ∧
    meromorphicOrderAt f a = (-1 : ℤ) ∧
    meromorphicOrderAt (fun z => -deriv f z + f z) a = (-2 : ℤ) := by
  have hm : MeromorphicAt f a :=
    (((MeromorphicAt.const α a).div (by fun_prop)).add hH.meromorphicAt).congr heq.symm
  have heq' : (fun z => -deriv f z + f z) =ᶠ[𝓝[≠] a]
      (fun z => α / (z - a) ^ 2 + α / (z - a) + H z - deriv H z) := by
    filter_upwards [heq, heq.nhdsNE_deriv, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds hH.eventually_analyticAt] with z hf hd hz hHz
    have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    have hder : deriv (fun z => α / (z - a) + H z) z =
        -α / (z - a) ^ 2 + deriv H z := by
      rw [deriv_fun_add (by fun_prop) hHz.differentiableAt,
        deriv_fun_div (c := fun _ : ℂ => α) (d := fun w : ℂ => w - a)
          (x := z) (by fun_prop) (by fun_prop) hza]
      simp
    rw [hd, hder, hf]
    ring
  refine ⟨heq', ?_, ?_⟩
  · apply (meromorphicOrderAt_eq_int_iff hm).mpr
    refine ⟨fun z => α + (z - a) * H z, by fun_prop, by simpa using hα, ?_⟩
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hza
    have hne : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hza)
    rw [hz]
    simp only [zpow_neg_one, smul_eq_mul]
    field_simp
    <;> ring
  · apply (meromorphicOrderAt_eq_int_iff (hm.deriv.neg.add hm)).mpr
    refine ⟨fun z => α + α * (z - a) + (z - a) ^ 2 * (H z - deriv H z),
      (by have hd := hH.deriv; fun_prop), by simpa using hα, ?_⟩
    filter_upwards [heq', self_mem_nhdsWithin] with z hz hza
    have hne : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hza)
    change -deriv f z + f z = _
    rw [hz]
    simp only [zpow_neg, zpow_ofNat, smul_eq_mul]
    field_simp
    <;> ring

private lemma actual_poles (u₀ : ℝ) {ρ : ℂ}
    (hρ : (1 / 2 : ℝ) < ρ.re) (hzero : riemannZeta ρ = 0) :
    let a := ρ - 1
    let m := analyticOrderNatAt riemannZeta ρ
    let α := -(m : ℂ) / ρ
    a ∈ D ∧ a ≠ 0 ∧ 0 < m ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ ∧ α ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      M u₀ =ᶠ[𝓝[≠] a] (fun s => α / (s - a) + H s) ∧
      (fun s => -deriv (M u₀) s + M u₀ s) =ᶠ[𝓝[≠] a]
        (fun s => α / (s - a) ^ 2 + α / (s - a) + H s - deriv H s) ∧
      meromorphicOrderAt (M u₀) a = (-1 : ℤ) ∧
      meromorphicOrderAt (fun s => -deriv (M u₀) s + M u₀ s) a = (-2 : ℤ) := by
  let a := ρ - 1
  let m := analyticOrderNatAt riemannZeta ρ
  let α := -(m : ℂ) / ρ
  change a ∈ D ∧ a ≠ 0 ∧ 0 < m ∧ _ ∧ α ≠ 0 ∧ _
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hρ1 : ρ ≠ 1 := by
    intro h
    exact riemannZeta_one_ne_zero (h ▸ hzero)
  have hf : AnalyticAt ℂ riemannZeta ρ := Zeta23.riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hfin := Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1
  have hmpos : 0 < m := ENat.toNat_pos (hf.analyticOrderAt_ne_zero.mpr hzero) hfin
  have hα : α ≠ 0 := div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hmpos.ne')) hρ0
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfin
  let g₁ : ℂ → ℂ := fun z => (z - 1) * g z
  have hg₁ : AnalyticAt ℂ g₁ ρ := (analyticAt_id.sub analyticAt_const).mul hg
  have hg₁0 : g₁ ρ ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hρ1) hg0
  have hf₁ : riemannZeta₁ =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ m * g₁ z := by
    filter_upwards [hfg, compl_singleton_mem_nhds hρ1] with z hz hz1
    have hn : z ≠ 1 := by simpa using hz1
    have he : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hn]
      field_simp
    rw [he, hz]
    simp only [smul_eq_mul]
    dsimp [g₁]
    ring
  obtain ⟨hR, hlog⟩ := factor_logDeriv hg₁ hg₁0 hf₁
  let R := logDeriv g₁
  let H : ℂ → ℂ := fun s =>
    (m : ℂ) / (ρ * (1 + s)) - (1 + R (1 + s) + C (1 + s)) / (1 + s) - A u₀ s
  have hlin : AnalyticAt ℂ (fun s : ℂ => 1 + s) a := by fun_prop
  have hpoint : 1 + a = ρ := by dsimp [a]; ring
  have hden : 1 + a ≠ 0 := hpoint ▸ hρ0
  have hRc : AnalyticAt ℂ (fun s => R (1 + s)) a := hR.comp_of_eq hlin hpoint
  have hCc : AnalyticAt ℂ (fun s => C (1 + s)) a :=
    (c_analytic ρ hρ).comp_of_eq hlin hpoint
  have hH : AnalyticAt ℂ H a :=
    ((analyticAt_const.div (analyticAt_const.mul hlin) (mul_ne_zero hρ0 hden)).sub
      (((analyticAt_const.add hRc).add hCc).div hlin hden)).sub
      (A_differentiable u₀ |>.analyticAt a)
  have ht : Tendsto (fun s : ℂ => 1 + s) (𝓝 a) (𝓝 ρ) := by
    rw [← hpoint]
    exact (continuous_const.add continuous_id).continuousAt.tendsto
  have hlogpull := ht.eventually (eventually_nhdsWithin_iff.mp hlog)
  have heq : M u₀ =ᶠ[𝓝[≠] a] (fun s => α / (s - a) + H s) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlogpull,
      mem_nhdsWithin_of_mem_nhds (hlin.continuousAt.eventually_ne hden)] with s hs hlogs hds
    have hsa : s - a ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    have hsρ : 1 + s ≠ ρ := by
      intro h
      apply hsa
      dsimp [a]
      linear_combination h
    have hld : logDeriv riemannZeta₁ (1 + s) = (m : ℂ) / (s - a) + R (1 + s) := by
      convert hlogs hsρ using 1
      dsimp [a, R]
      congr 2
      ring
    dsimp [M, H, α]
    rw [hld]
    field_simp [hρ0, hds, hsa]
    ring
  have hp := pole_orders hH hα heq
  refine ⟨?_, sub_ne_zero.mpr hρ1, hmpos, hfin, hα, H, hH, heq, hp.1, hp.2.1, hp.2.2⟩
  change -(1 / 2 : ℝ) < (ρ - 1).re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The actual cutoff theta transform, its analytic continuation and poles
with their full zeta-zero multiplicities. -/
theorem theta_laplace_continuation (u₀ : ℝ) (hu₀ : 0 ≤ u₀) :
    AnalyticOnNhd ℂ C {z | (1 / 2 : ℝ) < z.re} ∧
    Differentiable ℂ (A u₀) ∧
    (∀ z : ℂ, (1 / 2 : ℝ) < z.re →
      LSeriesSummable (fun n => (b n : ℂ)) z ∧
      Summable (fun pj : Nat.Primes × ℕ =>
        ‖(Real.log (pj.1 : ℝ) : ℂ) * (pj.1 : ℂ) ^ (-((pj.2 + 2 : ℕ) : ℂ) * z)‖) ∧
      C z = ∑' p : Nat.Primes, ∑' j : ℕ,
        (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-((j + 2 : ℕ) : ℂ) * z)) ∧
    (∀ s : ℂ, 0 < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (q u : ℂ)) (Ioi u₀) ∧
      Q u₀ s = M u₀ s ∧
      IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))
        (Ioi u₀) ∧
      HasDerivAt (Q u₀)
        (-(∫ u in Ioi u₀, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s) ∧
    MeromorphicOn (M u₀) D ∧
    AnalyticAt ℂ (M u₀) 0 ∧
    M u₀ 0 = -1 - (Real.eulerMascheroniConstant : ℂ) - C 1 - A u₀ 0 ∧
    (∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → riemannZeta ρ = 0 →
      let a := ρ - 1
      let m := analyticOrderNatAt riemannZeta ρ
      let α := -(m : ℂ) / ρ
      a ∈ D ∧ a ≠ 0 ∧ 0 < m ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ ∧ α ≠ 0 ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
        M u₀ =ᶠ[𝓝[≠] a] (fun s => α / (s - a) + H s) ∧
        (fun s => -deriv (M u₀) s + M u₀ s) =ᶠ[𝓝[≠] a]
          (fun s => α / (s - a) ^ 2 + α / (s - a) + H s - deriv H s) ∧
        meromorphicOrderAt (M u₀) a = (-1 : ℤ) ∧
        meromorphicOrderAt (fun s => -deriv (M u₀) s + M u₀ s) a = (-2 : ℤ)) := by
  refine ⟨c_analytic, A_differentiable u₀, ?_, ?_, M_meromorphic u₀,
    M_analytic_zero u₀, ?_, fun ρ hρ hz => actual_poles u₀ hρ hz⟩
  · intro z hz
    exact ⟨c_summable hz, (c_prime_powers hz).1.norm, (c_prime_powers hz).2⟩
  · intro s hs
    exact ⟨F_integrable u₀ hs, Q_eq_M u₀ hs, (Q_hasDeriv u₀ hu₀ hs).1,
      (Q_hasDeriv u₀ hu₀ hs).2⟩
  · simp only [M, logDeriv_apply, add_zero, riemannZeta₁_one,
      deriv_riemannZeta₁_one, div_one]
    ring

#print axioms theta_laplace_continuation

end
end D5.S3.Weil.Mertens.ThetaLaplaceContinuation
