/- GID: D5/S3/Analytic/Adelic/PrimeObserverCasimirCompleteMonotonicity
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/PrimeObserverCasimirCompleteMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The split-prime observer Casimir is completely monotone. -/

import D5.S3.PrimeForms.GoldenPrimeClassification
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Exact-name and body-shape searches found no frozen D5 owner for the
     split-prime regulator mode coefficients, their zero-minus-first mode
     Casimir, or its alternating iterated derivatives.
   * `GoldenPrimeClassification.golden_not_prime_iff_mod_five_eq_one_or_four`
     is the canonical repository bridge from golden splitting to the two
     nonramified residue classes and is applied below.
   * `LSeries.abscissaOfAbsConv_le_of_le_const`, `LSeries_sub`,
     `LSeries.LSeries_iteratedDeriv`, and `LSeries.iteratedDeriv_alternating`
     are exact pinned-Mathlib component hits and are applied directly.
   * Searches for `IsPrimePow` with `minFac` and cosine-weighted coefficients,
     and for real restrictions of mode L-series, found no public D5 primitive
     with the bodies introduced below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.PrimeObserverCasimirCompleteMonotonicity

open Complex D5.S0.Carrier LSeries
open D5.S3.PrimeForms.GoldenPrimeClassification
open Filter
open scoped ComplexOrder Topology

/-- A rational prime that splits, rather than ramifies, in the golden integers. -/
def IsGoldenSplitPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 5 ∧ ¬ Prime (p : GoldenInt)

/-- The prime-power coefficient of a regulator Fourier mode. Non-prime-powers
and prime powers outside the golden split classes contribute zero. -/
noncomputable def splitRegulatorModeCoefficient
    (phase : ℕ → ℝ) (mode n : ℕ) : ℂ := by
  classical
  exact
    if IsPrimePow n ∧ IsGoldenSplitPrime n.minFac then
      ((2 * Real.cos
          (((mode * n.factorization n.minFac : ℕ) : ℝ) * phase n.minFac) /
        (n.factorization n.minFac : ℝ) : ℝ) : ℂ)
    else
      0

/-- The real logarithmic reading of a regulator Fourier mode. -/
noncomputable def splitRegulatorModeLog
    (phase : ℕ → ℝ) (mode : ℕ) (sigma : ℝ) : ℝ :=
  (LSeries (splitRegulatorModeCoefficient phase mode) sigma).re

/-- The coefficient difference between the zero and first regulator modes. -/
noncomputable def primeObserverCasimirCoefficient
    (phase : ℕ → ℝ) (n : ℕ) : ℂ :=
  splitRegulatorModeCoefficient phase 0 n -
    splitRegulatorModeCoefficient phase 1 n

/-- The observer Casimir, constructed as the zero-mode logarithm minus the
first-mode logarithm. -/
noncomputable def goldenObserverCasimir
    (phase : ℕ → ℝ) (sigma : ℝ) : ℝ :=
  splitRegulatorModeLog phase 0 sigma - splitRegulatorModeLog phase 1 sigma

private theorem golden_split_prime_iff_mod_five
    {p : ℕ} (hp : p.Prime) :
    IsGoldenSplitPrime p ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  constructor
  · intro hsplit
    exact (golden_not_prime_iff_mod_five_eq_one_or_four hp hsplit.2.1).mp hsplit.2.2
  · intro hmod
    have h5 : p ≠ 5 := by
      intro hp5
      subst p
      norm_num at hmod
    exact ⟨hp, h5, (golden_not_prime_iff_mod_five_eq_one_or_four hp h5).mpr hmod⟩

private theorem mode_coefficient_prime_power
    (phase : ℕ → ℝ) (mode p k : ℕ) (hp : p.Prime)
    (hk : 0 < k) (hsplit : IsGoldenSplitPrime p) :
    splitRegulatorModeCoefficient phase mode (p ^ k) =
      (((2 * Real.cos (((mode * k : ℕ) : ℝ) * phase p)) / (k : ℝ) : ℝ) : ℂ) := by
  have his : IsPrimePow (p ^ k) :=
    (isPrimePow_pow_iff hk.ne').mpr hp.prime.isPrimePow
  have hmin : (p ^ k).minFac = p := hp.pow_minFac hk.ne'
  have hfac : (p ^ k).factorization (p ^ k).minFac = k := by
    rw [hmin, hp.factorization_pow, Finsupp.single_eq_same]
  have hcond : IsPrimePow (p ^ k) ∧ IsGoldenSplitPrime (p ^ k).minFac := by
    exact ⟨his, by simpa only [hmin] using hsplit⟩
  rw [splitRegulatorModeCoefficient, if_pos hcond, hfac, hmin]

private theorem casimir_coefficient_prime_power
    (phase : ℕ → ℝ) (p k : ℕ) (hp : p.Prime)
    (hk : 0 < k) (hsplit : IsGoldenSplitPrime p) :
    primeObserverCasimirCoefficient phase (p ^ k) =
      (((2 * (1 - Real.cos ((k : ℝ) * phase p))) / (k : ℝ) : ℝ) : ℂ) := by
  rw [primeObserverCasimirCoefficient,
    mode_coefficient_prime_power phase 0 p k hp hk hsplit,
    mode_coefficient_prime_power phase 1 p k hp hk hsplit]
  push_cast
  norm_num
  ring

private theorem mode_coefficient_norm_le_two
    (phase : ℕ → ℝ) (mode n : ℕ) :
    ‖splitRegulatorModeCoefficient phase mode n‖ ≤ 2 := by
  rw [splitRegulatorModeCoefficient]
  split_ifs with h
  · have hk : 0 < n.factorization n.minFac :=
      Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero h.1.one_lt)
    have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hkCastNonneg : (0 : ℝ) ≤ (n.factorization n.minFac : ℝ) :=
      Nat.cast_nonneg _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg htwoNonneg, abs_of_nonneg hkCastNonneg]
    have hcos := Real.abs_cos_le_one
      (((mode * n.factorization n.minFac : ℕ) : ℝ) * phase n.minFac)
    have hkOne : (1 : ℝ) ≤ n.factorization n.minFac := by exact_mod_cast hk
    calc
      2 * |Real.cos
          (((mode * n.factorization n.minFac : ℕ) : ℝ) * phase n.minFac)| /
          (n.factorization n.minFac : ℝ) ≤ 2 * 1 / 1 := by gcongr
      _ = 2 := by norm_num
  · simp

private theorem casimir_coefficient_nonnegative
    (phase : ℕ → ℝ) (n : ℕ) :
    0 ≤ primeObserverCasimirCoefficient phase n := by
  rw [primeObserverCasimirCoefficient]
  by_cases h : IsPrimePow n ∧ IsGoldenSplitPrime n.minFac
  · have hk : 0 < n.factorization n.minFac :=
      Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero h.1.one_lt)
    simp only [splitRegulatorModeCoefficient, if_pos h,
      Nat.cast_zero, zero_mul, Real.cos_zero]
    rw [← Complex.ofReal_sub, Complex.zero_le_real]
    have hcos := Real.cos_le_one
      (((n.factorization n.minFac : ℕ) : ℝ) * phase n.minFac)
    have hkNonneg : (0 : ℝ) ≤ n.factorization n.minFac := by positivity
    have hpositive :
        0 ≤ 2 * (1 - Real.cos
          (((n.factorization n.minFac : ℕ) : ℝ) * phase n.minFac)) /
            (n.factorization n.minFac : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hcos)) hkNonneg
    convert hpositive using 1
    ring_nf
  · simp only [splitRegulatorModeCoefficient, if_neg h, sub_zero, le_refl]

private theorem casimir_coefficient_norm_le_four
    (phase : ℕ → ℝ) (n : ℕ) :
    ‖primeObserverCasimirCoefficient phase n‖ ≤ 4 := by
  rw [primeObserverCasimirCoefficient]
  calc
    ‖splitRegulatorModeCoefficient phase 0 n -
        splitRegulatorModeCoefficient phase 1 n‖ ≤
        ‖splitRegulatorModeCoefficient phase 0 n‖ +
          ‖splitRegulatorModeCoefficient phase 1 n‖ := norm_sub_le _ _
    _ ≤ 2 + 2 := add_le_add
      (mode_coefficient_norm_le_two phase 0 n)
      (mode_coefficient_norm_le_two phase 1 n)
    _ = 4 := by norm_num

private theorem mode_abscissa_le_one
    (phase : ℕ → ℝ) (mode : ℕ) :
    abscissaOfAbsConv (splitRegulatorModeCoefficient phase mode) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨2, fun n _ => mode_coefficient_norm_le_two phase mode n⟩

private theorem casimir_abscissa_le_one (phase : ℕ → ℝ) :
    abscissaOfAbsConv (primeObserverCasimirCoefficient phase) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨4, fun n _ => casimir_coefficient_norm_le_four phase n⟩

private theorem abscissa_lt_of_one_lt
    {a : ℕ → ℂ} (ha : abscissaOfAbsConv a ≤ 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    abscissaOfAbsConv a < (sigma : ℂ).re := by
  simpa only [ofReal_re] using ha.trans_lt (EReal.coe_lt_coe_iff.mpr hsigma)

private theorem casimir_eq_lseries
    (phase : ℕ → ℝ) {sigma : ℝ} (hsigma : 1 < sigma) :
    goldenObserverCasimir phase sigma =
      (LSeries (primeObserverCasimirCoefficient phase) sigma).re := by
  have hzero : LSeriesSummable (splitRegulatorModeCoefficient phase 0) sigma :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (abscissa_lt_of_one_lt (mode_abscissa_le_one phase 0) hsigma)
  have hone : LSeriesSummable (splitRegulatorModeCoefficient phase 1) sigma :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (abscissa_lt_of_one_lt (mode_abscissa_le_one phase 1) hsigma)
  simp only [goldenObserverCasimir, splitRegulatorModeLog]
  rw [← Complex.sub_re, ← LSeries_sub hzero hone]
  rfl

private theorem real_lseries_iterated_deriv
    (a : ℕ → ℂ) (ha : abscissaOfAbsConv a ≤ 1)
    (m : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    iteratedDeriv m (fun x : ℝ => (LSeries a x).re) sigma =
      (-1 : ℝ) ^ m * (LSeries (logMul^[m] a) sigma).re := by
  induction m generalizing sigma with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hevent :
          iteratedDeriv m (fun x : ℝ => (LSeries a x).re) =ᶠ[𝓝 sigma]
            fun x : ℝ => (-1 : ℝ) ^ m * (LSeries (logMul^[m] a) x).re := by
        filter_upwards [isOpen_Ioi.mem_nhds hsigma] with x hx
        exact ih hx
      rw [hevent.deriv_eq]
      have hconv : abscissaOfAbsConv (logMul^[m] a) < (sigma : ℂ).re := by
        rw [LSeries.absicssaOfAbsConv_logPowMul]
        exact abscissa_lt_of_one_lt ha hsigma
      have hderiv :=
        ((LSeries_hasDerivAt hconv).real_of_complex.const_mul ((-1 : ℝ) ^ m))
      rw [hderiv.deriv]
      simp only [Function.iterate_succ_apply', pow_succ, Complex.neg_re]
      ring

private theorem signed_casimir_derivative_formula
    (phase : ℕ → ℝ) (m : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (-1 : ℝ) ^ m * iteratedDeriv m (goldenObserverCasimir phase) sigma =
      (LSeries ((logMul^[m]) (primeObserverCasimirCoefficient phase)) sigma).re := by
  have hEq : Set.EqOn (goldenObserverCasimir phase)
      (fun x : ℝ => (LSeries (primeObserverCasimirCoefficient phase) x).re)
      (Set.Ioi 1) := fun x hx => casimir_eq_lseries phase hx
  have hderiv := hEq.iteratedDeriv_of_isOpen isOpen_Ioi m hsigma
  rw [hderiv, real_lseries_iterated_deriv
    (primeObserverCasimirCoefficient phase) (casimir_abscissa_le_one phase) m hsigma]
  simp only [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_mul]

/-- The prime-power formula constructs the split observer coefficients from the
golden splitting predicate and regulator phases. The Casimir is publicly tied to
the zero-minus-first mode difference, its signed derivatives have the explicit
log-weighted L-series expansion, and every such derivative is nonnegative. -/
theorem prime_observer_casimir_complete_monotonicity
    (phase : ℕ → ℝ) :
    (∀ p k : ℕ, p.Prime → 0 < k → IsGoldenSplitPrime p →
      primeObserverCasimirCoefficient phase (p ^ k) =
        (((2 * (1 - Real.cos ((k : ℝ) * phase p))) / (k : ℝ) : ℝ) : ℂ)) ∧
    (∀ p : ℕ, p.Prime →
      (IsGoldenSplitPrime p ↔ p % 5 = 1 ∨ p % 5 = 4)) ∧
    (∀ sigma : ℝ, 1 < sigma →
      goldenObserverCasimir phase sigma =
        (LSeries (primeObserverCasimirCoefficient phase) sigma).re) ∧
    (∀ m : ℕ, ∀ sigma : ℝ, 1 < sigma →
      (-1 : ℝ) ^ m * iteratedDeriv m (goldenObserverCasimir phase) sigma =
        (LSeries ((logMul^[m]) (primeObserverCasimirCoefficient phase)) sigma).re) ∧
    (∀ m : ℕ, ∀ sigma : ℝ, 1 < sigma →
      0 ≤ (-1 : ℝ) ^ m *
        iteratedDeriv m (goldenObserverCasimir phase) sigma) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun p k hp hk hsplit =>
      casimir_coefficient_prime_power phase p k hp hk hsplit
  · exact fun p hp => golden_split_prime_iff_mod_five hp
  · exact fun sigma hsigma => casimir_eq_lseries phase hsigma
  · exact fun m sigma hsigma => signed_casimir_derivative_formula phase m hsigma
  · intro m sigma hsigma
    have hconv :
        abscissaOfAbsConv (primeObserverCasimirCoefficient phase) < (sigma : EReal) :=
      (casimir_abscissa_le_one phase).trans_lt (EReal.coe_lt_coe_iff.mpr hsigma)
    rw [signed_casimir_derivative_formula phase m hsigma]
    have hnonneg := LSeries.iteratedDeriv_alternating
      (casimir_coefficient_nonnegative phase) hconv m
    rw [LSeries_iteratedDeriv m (by simpa using hconv)] at hnonneg
    simp only [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_mul] at hnonneg
    exact (Complex.nonneg_iff.mp hnonneg).1

#print axioms prime_observer_casimir_complete_monotonicity

end D5.S3.Analytic.Adelic.PrimeObserverCasimirCompleteMonotonicity
