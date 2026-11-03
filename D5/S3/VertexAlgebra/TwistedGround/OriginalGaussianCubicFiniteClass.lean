/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFiniteClass
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFiniteClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit finite polynomials in the original neck coordinate represent every positive modulus coefficient of the literal TT and UT kernels. -/

/-
  This module keeps the two literal kernels from
  OriginalGaussianCubicKernel.  It derives their all-degree finite polynomial
  class membership directly from the displayed PowerSeries(LaurentSeries)
  formulas.  No resolvent, sewing, residue, root, or correspondence theorem is
  used as a premise.

  The input supplier and the previously supplied finite-current/pole support
  source are imported unchanged.  The finite polynomials below are new and are
  defined by finite sums in Complex[X].
-/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicFinitePrincipalParts
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

local notation "H" => halfSeries
private abbrev h := halfBinomial

/- The finite coefficient polynomial for H(x/a)H(x/b). -/
private def APoly (d : ℕ) (b : ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial (d - i)
      (h i * h (d - i) * (b ^ (d - i))⁻¹)

private lemma eval_APoly (d : ℕ) (a b : ℂ) :
    (APoly d b).eval a =
      ∑ i ∈ Finset.range (d + 1),
        h i * h (d - i) * (b ^ (d - i))⁻¹ * a ^ (d - i) := by
  simp [APoly, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

private lemma halfSeries_binomial_again :
    H = PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) := by
  ext n
  simp [halfSeries, PowerSeries.binomialSeries_coeff, halfBinomial_choose]

/- This is the native formal-binomial multiplication, coefficient by coefficient. -/
private lemma half_convolution (d : ℕ) :
    ∑ i ∈ Finset.range (d + 1), h i * h (d - i) = (-1 : ℂ) ^ d := by
  have hs : H * H = PowerSeries.binomialSeries ℂ (-1 : ℂ) := by
    rw [halfSeries_binomial_again, ← PowerSeries.binomialSeries_add]
    norm_num
  have hc := congrArg (fun q : PowerSeries ℂ => PowerSeries.coeff d q) hs
  simpa only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.binomialSeries_coeff, halfSeries,
    PowerSeries.coeff_mk, smul_eq_mul, mul_one, Ring.choose_neg', Ring.multichoose_one,
    Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast, mul_one, Nat.succ_eq_add_one, h] using hc

/- The weighted convolution is the finite index-reversal identity.  The
   derivative form is used only as an algebraic abbreviation for the same
   finite sum; no analytic differentiation is involved. -/
private lemma half_weighted_convolution (d : ℕ) :
    ∑ i ∈ Finset.range (d + 1),
      (d - i : ℂ) * h i * h (d - i) =
        (d : ℂ) / 2 * (-1 : ℂ) ^ d := by
  have hs := half_convolution d
  have hrev :
      ∑ i ∈ Finset.range (d + 1),
          (i : ℂ) * h i * h (d - i) =
        ∑ i ∈ Finset.range (d + 1),
          (d - i : ℂ) * h i * h (d - i) := by
    apply Finset.sum_bij (fun i hi => d - i)
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i₁ hi₁ i₂ hi₂ he
      simp only [Finset.mem_range] at hi₁ hi₂
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨d - j, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      have hi' : d - (d - i) = i := by omega
      have hcast : ((d - i : ℕ) : ℂ) = (d : ℂ) - (i : ℂ) :=
        Nat.cast_sub (by omega : i ≤ d)
      simp only [hi', hcast]
      ring
  have hsum :
      (∑ i ∈ Finset.range (d + 1),
          (i : ℂ) * h i * h (d - i)) +
        ∑ i ∈ Finset.range (d + 1),
          (d - i : ℂ) * h i * h (d - i) =
      (d : ℂ) * (-1 : ℂ) ^ d := by
    calc
      _ = ∑ i ∈ Finset.range (d + 1),
          (d : ℂ) * (h i * h (d - i)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hi_le : i ≤ d := by
          simp only [Finset.mem_range] at hi
          omega
        have hadd : (i : ℂ) + ((d - i : ℕ) : ℂ) = (d : ℂ) := by
          exact_mod_cast (show i + (d - i) = d by omega)
        calc
          _ = ((i : ℂ) + ((d - i : ℕ) : ℂ)) *
              (h i * h (d - i)) := by
                simp only [Nat.cast_sub hi_le]
                ring
          _ = _ := by rw [hadd]
      _ = (d : ℂ) * ∑ i ∈ Finset.range (d + 1),
          h i * h (d - i) := by rw [Finset.mul_sum]
      _ = _ := by rw [hs]
  rw [hrev] at hsum
  linear_combination (1 / 2 : ℂ) * hsum

private lemma APoly_at_b (d : ℕ) {b : ℂ} (hb : b ≠ 0) :
    (APoly d b).eval b = (-1 : ℂ) ^ d := by
  rw [eval_APoly]
  calc
    _ = ∑ i ∈ Finset.range (d + 1), h i * h (d - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpow : b ^ (d - i) ≠ 0 := pow_ne_zero _ hb
      simp only [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
    _ = _ := half_convolution d

private lemma APoly_derivative_at_b (d : ℕ) {b : ℂ} (hb : b ≠ 0) :
    (APoly d b).derivative.eval b =
      (d : ℂ) / (2 * b) * (-1 : ℂ) ^ d := by
  classical
  simp only [APoly, Polynomial.derivative_sum, Polynomial.eval_finset_sum,
    Polynomial.derivative_monomial, Polynomial.eval_monomial]
  calc
    _ = (∑ i ∈ Finset.range (d + 1),
          (d - i : ℂ) * h i * h (d - i)) / b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ d := by
        simp only [Finset.mem_range] at hi
        omega
      by_cases hdi : d - i = 0
      · have hdeq : d = i := by omega
        subst d
        simp
      · have hstep : (d - i - 1) + 1 = d - i := by omega
        have hpow : b ^ (d - i) = b ^ (d - i - 1) * b := by
          rw [← pow_succ, hstep]
        have hpow0 : b ^ (d - i - 1) ≠ 0 := pow_ne_zero _ hb
        simp only [hpow, Nat.cast_sub hi_le]
        field_simp [hb, hpow0] <;> ring
    _ = _ := by
      rw [half_weighted_convolution d]
      field_simp [hb] <;> ring

/- The literal polar coefficient numerator.  It is a polynomial in the inner
   Laurent variable a; the b-powers occur only as complex coefficients. -/
private def MPoly (d : ℕ) (b : ℂ) : Polynomial ℂ :=
  Polynomial.C b * (Polynomial.X + Polynomial.C b + Polynomial.C 2) * APoly d b +
    (Polynomial.C 2 * Polynomial.X * Polynomial.C b + Polynomial.X + Polynomial.C b) *
      APoly (d - 1) b

private lemma MPoly_at_b (d : ℕ) {b : ℂ} (hb : b ≠ 0) (hd : 1 ≤ d) :
    (MPoly d b).eval b = 0 := by
  simp only [MPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, APoly_at_b d hb,
    APoly_at_b (d - 1) hb]
  have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
    calc
      _ = -((-1 : ℂ) ^ ((d - 1) + 1)) := by rw [pow_succ]; ring
      _ = _ := by rw [Nat.sub_add_cancel hd]
  rw [hsign]
  ring

private lemma MPoly_derivative_at_b (d : ℕ) {b : ℂ} (hb : b ≠ 0) (hd : 1 ≤ d) :
    (MPoly d b).derivative.eval b = 0 := by
  simp only [MPoly, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero, Polynomial.eval_one, zero_add, add_zero,
    zero_mul, mul_zero, one_mul, mul_one,
    APoly_at_b d hb, APoly_at_b (d - 1) hb,
    APoly_derivative_at_b d hb, APoly_derivative_at_b (d - 1) hb]
  have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
    calc
      _ = -((-1 : ℂ) ^ ((d - 1) + 1)) := by rw [pow_succ]; ring
      _ = _ := by rw [Nat.sub_add_cancel hd]
  have hcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub hd :
      ((d - 1 : ℕ) : ℂ) = (d : ℂ) - (1 : ℕ))
  rw [hsign, hcast]
  field_simp [hb] <;> ring

private lemma MPoly_degree_le (d : ℕ) (b : ℂ) :
    (MPoly d b).degree ≤ ((d + 1 : ℕ) : WithBot ℕ) := by
  have hA : (APoly d b).degree ≤ d := by
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
    intro i hi
    exact (Polynomial.degree_monomial_le _ _).trans
      (WithBot.coe_le_coe.mpr (Nat.sub_le d i))
  have hA' : (APoly (d - 1) b).degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
    intro i hi
    exact (Polynomial.degree_monomial_le _ _).trans
      (WithBot.coe_le_coe.mpr (Nat.sub_le (d - 1) i))
  have hlin : (Polynomial.X + Polynomial.C b + Polynomial.C 2).degree ≤ (1 : WithBot ℕ) := by
    apply Polynomial.degree_add_le_of_degree_le
    · exact Polynomial.degree_add_le_of_degree_le Polynomial.degree_X_le
        (Polynomial.degree_C_le.trans (by norm_num))
    · exact Polynomial.degree_C_le.trans (by norm_num)
  have hlin' :
      (Polynomial.C 2 * Polynomial.X * Polynomial.C b + Polynomial.X +
        Polynomial.C b).degree ≤ (1 : WithBot ℕ) := by
    apply Polynomial.degree_add_le_of_degree_le
    · apply Polynomial.degree_add_le_of_degree_le
      · convert
          (Polynomial.degree_mul_le_of_le
            (Polynomial.degree_mul_le_of_le
              (Polynomial.degree_C_le (a := (2 : ℂ)))
              (Polynomial.degree_X_le (R := ℂ)))
            (Polynomial.degree_C_le (a := b))) using 1 <;> norm_num
      · exact Polynomial.degree_X_le
    · exact Polynomial.degree_C_le.trans (by norm_num)
  have hleft :
      (Polynomial.C b * (Polynomial.X + Polynomial.C b + Polynomial.C 2) *
        APoly d b).degree ≤ ((d + 1 : ℕ) : WithBot ℕ) := by
    calc
      _ ≤ (0 : WithBot ℕ) + 1 + d :=
        Polynomial.degree_mul_le_of_le
          (Polynomial.degree_mul_le_of_le (Polynomial.degree_C_le (a := b)) hlin) hA
      _ = (d + 1 : ℕ) := by simp [add_assoc, add_comm, add_left_comm]
  have hright :
      ((Polynomial.C 2 * Polynomial.X * Polynomial.C b + Polynomial.X + Polynomial.C b) *
        APoly (d - 1) b).degree ≤ ((d + 1 : ℕ) : WithBot ℕ) := by
    calc
      _ ≤ (1 : WithBot ℕ) + ((d - 1 : ℕ) : WithBot ℕ) :=
        Polynomial.degree_mul_le_of_le hlin' hA'
      _ ≤ (d + 1 : ℕ) := by
        exact_mod_cast (show 1 + (d - 1) ≤ d + 1 by omega)
  exact (Polynomial.degree_add_le _ _).trans (max_le hleft hright)

/- Minimal local adapter: a double root gives a genuine square divisor, and the
   quotient has the required strict degree.  The zero polynomial is included. -/
private lemma MPoly_square_factor (d : ℕ) {b : ℂ} (hb : b ≠ 0) (hd : 1 ≤ d) :
    ∃ q : Polynomial ℂ,
      MPoly d b = (Polynomial.X - Polynomial.C b) ^ 2 * q ∧ q.degree < d := by
  classical
  by_cases hM : MPoly d b = 0
  · refine ⟨0, by simp [hM], by simp⟩
  have hroot : Polynomial.IsRoot (MPoly d b) b := MPoly_at_b d hb hd
  let r := MPoly d b /ₘ (Polynomial.X - Polynomial.C b)
  have hfac : (Polynomial.X - Polynomial.C b) * r = MPoly d b := by
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
  have hder := congrArg (fun p : Polynomial ℂ => p.eval b)
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      (MPoly d b) b)
  have hrroot : r.eval b = 0 := by
    simpa [r, MPoly_derivative_at_b d hb hd] using hder
  let q := r /ₘ (Polynomial.X - Polynomial.C b)
  have hqfac : (Polynomial.X - Polynomial.C b) * q = r := by
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hrroot
  refine ⟨q, ?_, ?_⟩
  · rw [← hfac, ← hqfac]
    ring
  · by_cases hq : q = 0
    · simp [hq]
    · have hdegfac : (MPoly d b).degree = (q.natDegree + 2 : ℕ) := by
        rw [← hfac, ← hqfac]
        simp only [Polynomial.degree_mul, Polynomial.degree_X_sub_C,
          Polynomial.degree_eq_natDegree hq]
        exact_mod_cast (show 1 + (1 + q.natDegree) = q.natDegree + 2 by omega)
      have hdegM := MPoly_degree_le d b
      rw [hdegfac] at hdegM
      have hnat : q.natDegree + 2 ≤ d + 1 := WithBot.coe_le_coe.mp hdegM
      rw [Polynomial.degree_eq_natDegree hq]
      exact WithBot.coe_lt_coe.mpr (show q.natDegree < d by omega)

private def QPoly (d : ℕ) (b : ℂ) : Polynomial ℂ :=
  MPoly d b /ₘ (Polynomial.X - Polynomial.C b) ^ 2

private lemma QPoly_factor (d : ℕ) {b : ℂ} (hb : b ≠ 0) (hd : 1 ≤ d) :
    MPoly d b = (Polynomial.X - Polynomial.C b) ^ 2 * QPoly d b := by
  obtain ⟨q, hq, hdeg⟩ := MPoly_square_factor d hb hd
  have hquot : QPoly d b = q := by
    unfold QPoly
    exact (Polynomial.div_modByMonic_unique q 0
      ((Polynomial.monic_X_sub_C b).pow 2)
      ⟨by simpa only [zero_add] using hq.symm, by
        rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
        exact ((Polynomial.monic_X_sub_C b).pow 2).ne_zero⟩).1
  rw [hquot]
  exact hq

private lemma QPoly_degree (d : ℕ) {b : ℂ} (hb : b ≠ 0) (hd : 1 ≤ d) :
    (QPoly d b).degree < d := by
  obtain ⟨q, hq, hdeg⟩ := MPoly_square_factor d hb hd
  have hquot : QPoly d b = q := by
    unfold QPoly
    exact (Polynomial.div_modByMonic_unique q 0
      ((Polynomial.monic_X_sub_C b).pow 2)
      ⟨by simpa only [zero_add] using hq.symm, by
        rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
        exact ((Polynomial.monic_X_sub_C b).pow 2).ne_zero⟩).1
  rw [hquot]
  exact hdeg

/- Scalar contribution.  The constant coefficient is zero, so l starts at one;
   the antidiagonal makes every exponent d-i-1 nonnegative and at most d-1. -/
private def CPoly (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range d,
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d - (l + 1)),
      Polynomial.monomial (d - ij.1 - 1)
        ((hb / b) * PowerSeries.coeff (l + 1) scalarCSeries *
          h ij.1 * h ij.2 * (b ^ ij.2)⁻¹)

private lemma CPoly_degree (d : ℕ) (b hb : ℂ) :
    (CPoly d b hb).degree < d := by
  refine (Polynomial.degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_)
  intro l hl
  refine (Polynomial.degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_)
  intro ij hij
  have hij' : ij.1 + ij.2 = d - (l + 1) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hl' : l < d := Finset.mem_range.mp hl
  have he : d - ij.1 - 1 < d := by omega
  exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr he)

private def PTPoly (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  Polynomial.C (hb / (2 * b)) * QPoly d b + CPoly d b hb

private lemma PTPoly_degree (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    (PTPoly d b hb).degree < d := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  apply max_lt
  · exact (Polynomial.degree_mul_le_of_le Polynomial.degree_C_le le_rfl).trans_lt
      (by simpa only [zero_add] using QPoly_degree d hb0 hd)
  · exact CPoly_degree d b hb

private abbrev PE : Polynomial ℂ →+* LaurentSeries ℂ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp Polynomial.coeToPowerSeries.ringHom

private lemma PE_coe (p : Polynomial ℂ) : PE p = (p : LaurentSeries ℂ) :=
  RatFunc.coe_coe p

private lemma PE_C (c : ℂ) : PE (Polynomial.C c) = HahnSeries.C c := by
  simp [PE, Polynomial.coeToPowerSeries.ringHom, Polynomial.coe_C]

private lemma PE_X : PE Polynomial.X = HahnSeries.single 1 (1 : ℂ) := by
  simp [PE, Polynomial.coeToPowerSeries.ringHom, Polynomial.coe_X]

private lemma PE_monomial (n : ℕ) (c : ℂ) :
    PE (Polynomial.monomial n c) = HahnSeries.single (n : ℤ) c := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, PE_C, PE_X,
    HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp

private lemma omega_product_term {b hb : ℂ} (hb0 : b ≠ 0)
    (n i : ℕ) (hi : i ≤ n) :
    omegaCoefficient i * HahnSeries.C (hb * h (n - i) / b ^ (n - i + 1)) =
      HahnSeries.single (-(n : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        HahnSeries.C (hb / b) *
        PE (Polynomial.monomial (n - i)
          (h i * h (n - i) * (b ^ (n - i))⁻¹)) := by
  have he : -(n : ℤ) - 1 + ((n - i : ℕ) : ℤ) = -(i : ℤ) - 1 := by omega
  rw [omegaCoefficient, PE_monomial, HahnSeries.C_apply, HahnSeries.C_apply]
  have hs :
      (HahnSeries.single (-(n : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) *
        HahnSeries.single 0 (hb / b) *
        HahnSeries.single ((n - i : ℕ) : ℤ)
          (h i * h (n - i) * (b ^ (n - i))⁻¹) =
        HahnSeries.single (-(i : ℤ) - 1)
          (h i * (hb * h (n - i) / b ^ (n - i + 1))) := by
    simp only [HahnSeries.single_mul_single, add_zero, one_mul, he]
    congr 1
    rw [pow_succ]
    field_simp [hb0, pow_ne_zero _ hb0]
    <;> ring
  calc
    _ = (H : LaurentSeries ℂ) *
        (HahnSeries.single (-(i : ℤ) - 1) (h i) *
          HahnSeries.single 0 (hb * h (n - i) / b ^ (n - i + 1))) := by ring
    _ = (H : LaurentSeries ℂ) *
        (HahnSeries.single (-(n : ℤ) - 1) (1 : ℂ) *
          HahnSeries.single 0 (hb / b) *
          HahnSeries.single ((n - i : ℕ) : ℤ)
            (h i * h (n - i) * (b ^ (n - i))⁻¹)) := by
      rw [hs, HahnSeries.single_mul_single, add_zero]
    _ = _ := by ring

private lemma omega_product_coefficient (n : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) :
    PowerSeries.coeff n (formalOmega * formalExternalOmega b hb) =
      HahnSeries.single (-(n : ℤ) - 1) (1 : ℂ) *
        (H : LaurentSeries ℂ) * HahnSeries.C (hb / b) * PE (APoly n b) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [formalOmega, formalExternalOmega, PowerSeries.coeff_mk, APoly,
    map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact omega_product_term hb0 n i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)

private lemma scalar_omega_term (d l i j : ℕ) {b hb : ℂ} (hb0 : b ≠ 0)
    (hl : l < d) (hij : i + j = d - (l + 1)) :
    HahnSeries.C (PowerSeries.coeff (l + 1) scalarCSeries) *
        (omegaCoefficient i * HahnSeries.C (hb * h j / b ^ (j + 1))) =
      HahnSeries.single (-(d : ℤ)) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (Polynomial.monomial (d - i - 1)
          ((hb / b) * PowerSeries.coeff (l + 1) scalarCSeries *
            h i * h j * (b ^ j)⁻¹)) := by
  have he : -(d : ℤ) + ((d - i - 1 : ℕ) : ℤ) = -(i : ℤ) - 1 := by omega
  rw [omegaCoefficient, PE_monomial]
  calc
    _ = (H : LaurentSeries ℂ) *
        (HahnSeries.single (-(i : ℤ) - 1) (h i) *
          HahnSeries.C (hb * h j / b ^ (j + 1)) *
          HahnSeries.C (PowerSeries.coeff (l + 1) scalarCSeries)) := by ring
    _ = (H : LaurentSeries ℂ) *
        (HahnSeries.single (-(d : ℤ)) (1 : ℂ) *
          HahnSeries.single ((d - i - 1 : ℕ) : ℤ)
            ((hb / b) * PowerSeries.coeff (l + 1) scalarCSeries *
              h i * h j * (b ^ j)⁻¹)) := by
      simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero,
        one_mul, he]
      congr 2
      rw [pow_succ]
      field_simp [hb0, pow_ne_zero _ hb0]
      <;> ring
    _ = _ := by ring

private lemma scalar_product_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) :
    PowerSeries.coeff d ((formalOmega * formalExternalOmega b hb) *
      PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries) =
      HahnSeries.single (-(d : ℤ)) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (CPoly d b hb) := by
  have hc0 : PowerSeries.coeff 0 scalarCSeries = 0 := by simp [scalarCSeries]
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [PowerSeries.coeff_map, hc0, map_zero, zero_mul, add_zero, zero_add]
  simp only [CPoly, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [PowerSeries.coeff_mul]
  simp only [formalOmega, formalExternalOmega, PowerSeries.coeff_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  exact scalar_omega_term d l ij.1 ij.2 hb0 (Finset.mem_range.mp hl)
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hij)

/- A literal coefficient expansion.  `aSeries` and `bSeries` are unfolded only
   here; all sums are finite because PowerSeries.coeff_mul uses the natural
   antidiagonal. -/
private lemma literal_tt_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    PowerSeries.coeff d (cubicTTSeries b hb) =
      HahnSeries.single (-(d : ℤ)) (1 : ℂ) *
        (H : LaurentSeries ℂ) * (PTPoly d b hb : LaurentSeries ℂ) := by
  classical
  let a : LaurentSeries ℂ := HahnSeries.single 1 1
  let B : LaurentSeries ℂ := HahnSeries.C b
  let F := formalOmega * formalExternalOmega b hb
  let SC := PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries
  let N0 := a * B * (a + B + 2)
  let N1 := 2 * a * B + a + B
  have hden : (2 * (PowerSeries.C a - PowerSeries.C B) ^ 2 : AnnulusSeries) =
      PowerSeries.C (2 * (a - B) ^ 2) := by
    simp only [map_mul, map_pow, map_sub, map_ofNat]
  have hshape : cubicTTSeries b hb =
      (F * PowerSeries.C N0 + (F * PowerSeries.X) * PowerSeries.C N1) *
        PowerSeries.C ((2 * (a - B) ^ 2)⁻¹) + F * SC := by
    change F * ((PowerSeries.C a * PowerSeries.C B * (PowerSeries.C a + PowerSeries.C B) +
      2 * (1 + PowerSeries.X) * PowerSeries.C a * PowerSeries.C B +
      PowerSeries.X * (PowerSeries.C a + PowerSeries.C B)) *
      (2 * (PowerSeries.C a - PowerSeries.C B) ^ 2)⁻¹ + SC) = _
    rw [hden, PowerSeries.C_inv]
    simp only [N0, N1, map_mul, map_add, map_ofNat]
    ring
  have hshift : PowerSeries.coeff d (F * PowerSeries.X) =
      PowerSeries.coeff (d - 1) F := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    simpa only [pow_one] using PowerSeries.coeff_mul_X_pow F 1 (d - 1)
  have hs : (HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) * a =
      HahnSeries.single (-(d : ℤ)) 1 := by
    have he : -(d : ℤ) - 1 + 1 = -(d : ℤ) := by omega
    simp only [a, HahnSeries.single_mul_single, mul_one, he]
  have hs' : (HahnSeries.single (-((d - 1 : ℕ) : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) =
      HahnSeries.single (-(d : ℤ)) 1 := by
    have he : -((d - 1 : ℕ) : ℤ) - 1 = -(d : ℤ) := by omega
    rw [he]
  have hnum : PowerSeries.coeff d F * N0 + PowerSeries.coeff (d - 1) F * N1 =
      HahnSeries.single (-(d : ℤ)) (1 : ℂ) * (H : LaurentSeries ℂ) *
        HahnSeries.C (hb / b) * PE (MPoly d b) := by
    rw [omega_product_coefficient d hb0, omega_product_coefficient (d - 1) hb0, hs']
    simp only [MPoly, map_add, map_mul, PE_C, PE_X]
    change _ = HahnSeries.single (-(d : ℤ)) 1 * (H : LaurentSeries ℂ) *
      HahnSeries.C (hb / b) *
        (B * (a + B + HahnSeries.C 2) * PE (APoly d b) + N1 * PE (APoly (d - 1) b))
    rw [map_ofNat]
    calc
      _ = ((HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) * a) *
          (H : LaurentSeries ℂ) * HahnSeries.C (hb / b) *
            (B * (a + B + 2) * PE (APoly d b)) +
          HahnSeries.single (-(d : ℤ)) 1 * (H : LaurentSeries ℂ) *
            HahnSeries.C (hb / b) * PE (APoly (d - 1) b) * N1 := by dsimp [N0]; ring
      _ = _ := by rw [hs]; ring
  have hdiff : a - B ≠ 0 := by
    intro he
    have hc := congrArg (fun q : LaurentSeries ℂ => q.coeff 1) he
    norm_num [a, B, HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single] at hc
  have hq : PE (MPoly d b) = (a - B) ^ 2 * PE (QPoly d b) := by
    rw [QPoly_factor d hb0 hd, map_mul, map_pow, map_sub, PE_X, PE_C]
  have hc : HahnSeries.C (hb / b) * (a - B) ^ 2 * (2 * (a - B) ^ 2)⁻¹ =
      HahnSeries.C (hb / (2 * b)) := by
    have hscalar : hb / (2 * b) = (hb / b) / 2 := by ring
    have hemb : HahnSeries.C (hb / (2 * b)) =
        (HahnSeries.C (hb / b) : LaurentSeries ℂ) / 2 := by
      simp only [hscalar, map_div₀, map_ofNat]
    rw [hemb]
    field_simp [hdiff]
    <;> ring
  rw [hshape, map_add, PowerSeries.coeff_mul_C, map_add, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_C, hshift, hnum, hq, scalar_product_coefficient d hb0]
  rw [← PE_coe (PTPoly d b hb)]
  simp only [PTPoly, map_add, map_mul, PE_C]
  calc
    _ = HahnSeries.single (-(d : ℤ)) 1 * (H : LaurentSeries ℂ) *
        (HahnSeries.C (hb / b) * (a - B) ^ 2 * (2 * (a - B) ^ 2)⁻¹) * PE (QPoly d b) +
        HahnSeries.single (-(d : ℤ)) 1 * (H : LaurentSeries ℂ) * PE (CPoly d b hb) := by ring
    _ = _ := by rw [hc]; ring

/- UT finite numerator.  The first antidiagonal splits i+j+n=d-1 and the
   second splits i+j+n=d-2.  The displayed monomials are the three terms of
   N₁ and the three terms of N₂ respectively. -/
private def UMain1 (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d - 1),
    ∑ jn ∈ Finset.HasAntidiagonal.antidiagonal ij.2,
      let i := ij.1
      let j := jn.1
      let n := jn.2
      let z := (n + 1 : ℂ) / 2
      let c := (hb / b) * h i * h j * (b ^ (j + n + 2))⁻¹ * z
      Polynomial.monomial (d - i - n) (-(c * b)) +
        Polynomial.monomial (d - i - n - 1) (-(c * b ^ 2)) +
        Polynomial.monomial (d - i - n - 1) (-(c * (2 * b)))

private def UMain2 (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  if 2 ≤ d then
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d - 2),
      ∑ jn ∈ Finset.HasAntidiagonal.antidiagonal ij.2,
        let i := ij.1
        let j := jn.1
        let n := jn.2
        let z := (n + 1 : ℂ) / 2
        let c := (hb / b) * h i * h j * (b ^ (j + n + 2))⁻¹ * z
        Polynomial.monomial (d - i - n - 1) (-c) +
          Polynomial.monomial (d - i - n - 2) (-(c * b)) +
          Polynomial.monomial (d - i - n - 1) (-(c * (2 * b)))
  else 0

private def UMain (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  UMain1 d b hb + UMain2 d b hb

private def UCPoly (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range d,
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d - (l + 1)),
      Polynomial.monomial (d - ij.1)
        (-((hb / b) * PowerSeries.coeff (l + 1) scalarCSeries *
          h ij.1 * h ij.2 * (b ^ ij.2)⁻¹))

private def PUPoly (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  UMain d b hb + UCPoly d b hb

private lemma UMain_degree (d : ℕ) (b hb : ℂ) :
    (UMain d b hb).degree ≤ d := by
  have hU1 : (UMain1 d b hb).degree ≤ d := by
    unfold UMain1
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
    intro ij hij
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
    intro jn hjn
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij hjn
    have hsum1 : ij.1 + jn.1 + jn.2 = d - 1 := by omega
    have he1 : d - ij.1 - jn.2 ≤ d := by
      exact (Nat.sub_le (d - ij.1) jn.2).trans (Nat.sub_le d ij.1)
    have he2 : d - ij.1 - jn.2 - 1 ≤ d := by
      exact (Nat.sub_le (d - ij.1 - jn.2) 1).trans
        ((Nat.sub_le (d - ij.1) jn.2).trans (Nat.sub_le d ij.1))
    dsimp
    apply Polynomial.degree_add_le_of_degree_le
    · apply Polynomial.degree_add_le_of_degree_le
      · exact (Polynomial.degree_monomial_le _ _).trans
          (WithBot.coe_le_coe.mpr he1)
      · exact (Polynomial.degree_monomial_le _ _).trans
          (WithBot.coe_le_coe.mpr he2)
    · exact (Polynomial.degree_monomial_le _ _).trans
        (WithBot.coe_le_coe.mpr he2)
  have hU2 : (UMain2 d b hb).degree ≤ d := by
    by_cases hd2 : 2 ≤ d
    · rw [UMain2, if_pos hd2]
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
      intro ij hij
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
      intro jn hjn
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij hjn
      have hsum2 : ij.1 + jn.1 + jn.2 = d - 2 := by omega
      have he1 : d - ij.1 - jn.2 - 1 ≤ d := by
        exact (Nat.sub_le (d - ij.1 - jn.2) 1).trans
          ((Nat.sub_le (d - ij.1) jn.2).trans (Nat.sub_le d ij.1))
      have he2 : d - ij.1 - jn.2 - 2 ≤ d := by
        exact (Nat.sub_le (d - ij.1 - jn.2) 2).trans
          ((Nat.sub_le (d - ij.1) jn.2).trans (Nat.sub_le d ij.1))
      dsimp
      apply Polynomial.degree_add_le_of_degree_le
      · apply Polynomial.degree_add_le_of_degree_le
        · exact (Polynomial.degree_monomial_le _ _).trans
            (WithBot.coe_le_coe.mpr he1)
        · exact (Polynomial.degree_monomial_le _ _).trans
            (WithBot.coe_le_coe.mpr he2)
      · exact (Polynomial.degree_monomial_le _ _).trans
          (WithBot.coe_le_coe.mpr he1)
    · rw [UMain2, if_neg hd2, Polynomial.degree_zero]
      exact bot_le
  rw [UMain]
  exact Polynomial.degree_add_le_of_degree_le hU1 hU2

private lemma UCPoly_degree (d : ℕ) (b hb : ℂ) :
    (UCPoly d b hb).degree ≤ d := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
  intro l hl
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
  intro ij hij
  simp only [Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hl hij
  have he : d - ij.1 ≤ d := by omega
  exact (Polynomial.degree_monomial_le _ _).trans (WithBot.coe_le_coe.mpr he)

private lemma PUPoly_degree (d : ℕ) (b hb : ℂ) :
    (PUPoly d b hb).degree < d + 1 := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  exact (max_le (UMain_degree d b hb) (UCPoly_degree d b hb)).trans_lt
    (show (d : WithBot ℕ) < (d + 1 : ℕ) from
      WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))

private lemma ut_denominator_coefficient {b : ℂ} (hb0 : b ≠ 0) (n : ℕ) :
    (PowerSeries.coeff n
      ((2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2 : AnnulusSeries)⁻¹)) =
      HahnSeries.C ((n + 1 : ℂ) / (2 : ℂ)) *
        (HahnSeries.single (-(n : ℤ) - 2) ((b ^ (n + 2))⁻¹)) := by
  have hu : (HahnSeries.single 1 b : LaurentSeries ℂ) ≠ 0 :=
    HahnSeries.single_ne_zero hb0
  let u : (LaurentSeries ℂ)ˣ :=
    Units.mk0 (HahnSeries.single 1 b) hu
  have hJ : PowerSeries.invUnitsSub u *
      (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) = 1 :=
    PowerSeries.invUnitsSub_mul_sub u
  have htwo : (2 : LaurentSeries ℂ) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : LaurentSeries ℂ => f.coeff 0) h
    change (HahnSeries.single 0 (2 : ℂ)).coeff 0 = (0 : LaurentSeries ℂ).coeff 0 at hc
    norm_num at hc
  have hhalf : (PowerSeries.C (1 / 2 : LaurentSeries ℂ) : AnnulusSeries) * 2 = 1 := by
    calc
      _ = PowerSeries.C ((1 / 2 : LaurentSeries ℂ) * 2) := by rw [map_mul]; rfl
      _ = 1 := by rw [one_div, inv_mul_cancel₀ htwo, map_one]
  have hconst : PowerSeries.constantCoeff
      (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2 : AnnulusSeries) ≠ 0 := by
    change PowerSeries.constantCoeff (PowerSeries.C (2 : LaurentSeries ℂ) *
      (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2) ≠ 0
    simpa only [map_mul, map_pow, map_sub, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, sub_zero] using mul_ne_zero htwo (pow_ne_zero 2 hu)
  have hmul : (PowerSeries.C (1 / 2 : LaurentSeries ℂ) * PowerSeries.invUnitsSub u ^ 2) *
      (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2) = 1 := by
    calc
      _ = (PowerSeries.C (1 / 2 : LaurentSeries ℂ) * 2) *
          (PowerSeries.invUnitsSub u * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X)) ^ 2 := by ring
      _ = 1 := by rw [hhalf, hJ]; simp
  have hinv := ((PowerSeries.eq_inv_iff_mul_eq_one hconst).mpr hmul).symm
  have hcoeff (m : ℕ) : PowerSeries.coeff m (PowerSeries.invUnitsSub u) =
      HahnSeries.single (-((m + 1 : ℕ) : ℤ)) ((b ^ (m + 1))⁻¹) := by
    rw [PowerSeries.coeff_invUnitsSub, one_divp, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    change (((HahnSeries.single 1 b : LaurentSeries ℂ) ^ (m + 1))⁻¹) = _
    rw [HahnSeries.single_pow, HahnSeries.inv_single]
    simp only [nsmul_eq_mul, mul_one]
  rw [hinv, PowerSeries.coeff_C_mul, pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hs : (∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (PowerSeries.invUnitsSub u) *
        PowerSeries.coeff (n - k) (PowerSeries.invUnitsSub u)) =
      (n + 1) • (HahnSeries.single (-((n + 2 : ℕ) : ℤ)) ((b ^ (n + 2))⁻¹) : LaurentSeries ℂ) := by
    trans ∑ k ∈ Finset.range (n + 1),
      (HahnSeries.single (-((n + 2 : ℕ) : ℤ)) ((b ^ (n + 2))⁻¹) : LaurentSeries ℂ)
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      rw [hcoeff, hcoeff, HahnSeries.single_mul_single, ← mul_inv, ← pow_add]
      have hsum : k + 1 + (n - k + 1) = n + 2 := by omega
      rw [hsum, ← neg_add, ← Nat.cast_add, hsum]
    · simp only [Finset.sum_const, Finset.card_range]
  rw [hs, nsmul_eq_mul]
  have hhalfC : (1 / 2 : LaurentSeries ℂ) = HahnSeries.C (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat]
  rw [hhalfC]
  have hnC : (↑(n + 1) : LaurentSeries ℂ) = HahnSeries.C (↑(n + 1) : ℂ) := by rw [map_natCast]
  rw [hnC, ← mul_assoc, ← map_mul]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    simp only [neg_add, sub_eq_add_neg]

private lemma ut_triple_coefficient {b hb : ℂ} (hb0 : b ≠ 0) (i j n : ℕ) :
    omegaCoefficient i * HahnSeries.C (hb * h j / b ^ (j + 1)) *
      (HahnSeries.C ((n + 1 : ℂ) / 2) *
        HahnSeries.single (-(n : ℤ) - 2) ((b ^ (n + 2))⁻¹)) =
      (H : LaurentSeries ℂ) * HahnSeries.single (-(i : ℤ) - 1 + (-(n : ℤ) - 2))
        ((hb / b) * h i * h j * (b ^ (j + n + 2))⁻¹ * ((n + 1 : ℂ) / 2)) := by
  rw [omegaCoefficient]
  calc
    _ = (H : LaurentSeries ℂ) *
        (HahnSeries.single (-(i : ℤ) - 1) (h i) *
          HahnSeries.C (hb * h j / b ^ (j + 1)) *
          HahnSeries.C ((n + 1 : ℂ) / 2) *
          HahnSeries.single (-(n : ℤ) - 2) ((b ^ (n + 2))⁻¹)) := by ring
    _ = _ := by
      simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero]
      congr 2
      simp only [pow_add, pow_succ]
      field_simp [hb0, pow_ne_zero _ hb0]
      <;> ring

private lemma ut_shift_monomial (s t : ℤ) (k e : ℕ) (r c : ℂ)
    (he : s + k = t + e) :
    -((HahnSeries.single s r : LaurentSeries ℂ) * PE (Polynomial.monomial k c)) =
      HahnSeries.single t (1 : ℂ) * PE (Polynomial.monomial e (-(r * c))) := by
  rw [PE_monomial, PE_monomial, HahnSeries.single_mul_single,
    HahnSeries.single_mul_single, one_mul, HahnSeries.single_neg, he]

private lemma ut_first_numerator (b : ℂ) :
    (HahnSeries.single 1 (1 : ℂ) : LaurentSeries ℂ) * HahnSeries.C b *
      (HahnSeries.single 1 (1 : ℂ) + HahnSeries.C b + 2) =
    PE (Polynomial.monomial 2 b + Polynomial.monomial 1 (b ^ 2) +
      Polynomial.monomial 1 (2 * b)) := by
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_add, map_mul, map_pow,
    PE_C, PE_X, map_ofNat, pow_one]
  ring

private lemma ut_second_numerator (b : ℂ) :
    (HahnSeries.single 1 (1 : ℂ) : LaurentSeries ℂ) + HahnSeries.C b +
      2 * HahnSeries.single 1 (1 : ℂ) * HahnSeries.C b =
    PE (Polynomial.monomial 1 1 + Polynomial.monomial 0 b +
      Polynomial.monomial 1 (2 * b)) := by
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_add, map_mul, map_pow,
    PE_C, PE_X, map_ofNat, map_one, pow_one, pow_zero, mul_one, one_mul]
  ring

private lemma ut_first_term (d i j n : ℕ) (hsum : i + j + n = d - 1)
    (hd : 1 ≤ d) (b r : ℂ) :
    -((HahnSeries.single (-(i : ℤ) - 1 + (-(n : ℤ) - 2)) r : LaurentSeries ℂ) *
      (HahnSeries.single 1 (1 : ℂ) * HahnSeries.C b *
        (HahnSeries.single 1 (1 : ℂ) + HahnSeries.C b + 2))) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) *
        PE (Polynomial.monomial (d - i - n) (-(r * b)) +
          Polynomial.monomial (d - i - n - 1) (-(r * b ^ 2)) +
          Polynomial.monomial (d - i - n - 1) (-(r * (2 * b)))) := by
  rw [ut_first_numerator]
  simp only [map_add, mul_add, neg_add]
  congr 2
  · exact ut_shift_monomial _ _ _ _ _ _ (by omega)
  · exact ut_shift_monomial _ _ _ _ _ _ (by omega)
  · exact ut_shift_monomial _ _ _ _ _ _ (by omega)

private lemma ut_second_term (d i j n : ℕ) (hsum : i + j + n = d - 2)
    (hd : 2 ≤ d) (b r : ℂ) :
    -((HahnSeries.single (-(i : ℤ) - 1 + (-(n : ℤ) - 2)) r : LaurentSeries ℂ) *
      (HahnSeries.single 1 (1 : ℂ) + HahnSeries.C b +
        2 * HahnSeries.single 1 (1 : ℂ) * HahnSeries.C b)) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) *
        PE (Polynomial.monomial (d - i - n - 1) (-r) +
          Polynomial.monomial (d - i - n - 2) (-(r * b)) +
          Polynomial.monomial (d - i - n - 1) (-(r * (2 * b)))) := by
  rw [ut_second_numerator]
  simp only [map_add, mul_add, neg_add]
  have h1 := ut_shift_monomial (-(i : ℤ) - 1 + (-(n : ℤ) - 2))
    (-(d : ℤ) - 1) 1 (d - i - n - 1) r 1 (by omega)
  simp only [mul_one] at h1
  rw [h1, ut_shift_monomial (-(i : ℤ) - 1 + (-(n : ℤ) - 2)) (-(d : ℤ) - 1) 0 (d - i - n - 2) r b (by omega),
    ut_shift_monomial (-(i : ℤ) - 1 + (-(n : ℤ) - 2)) (-(d : ℤ) - 1) 1 (d - i - n - 1) r (2 * b) (by omega)]

private abbrev utWeight (b hb : ℂ) (i j n : ℕ) : ℂ :=
  (hb / b) * h i * h j * (b ^ (j + n + 2))⁻¹ * ((n + 1 : ℂ) / 2)

private lemma ut_kernel_coefficient (m : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) :
    PowerSeries.coeff m (formalOmega * (formalExternalOmega b hb *
      (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹)) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
        ∑ jn ∈ Finset.HasAntidiagonal.antidiagonal ij.2,
          (H : LaurentSeries ℂ) *
            HahnSeries.single (-(ij.1 : ℤ) - 1 + (-(jn.2 : ℤ) - 2))
              (utWeight b hb ij.1 jn.1 jn.2) := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro jn hjn
  simp only [formalOmega, formalExternalOmega, PowerSeries.coeff_mk,
    ut_denominator_coefficient hb0]
  rw [← mul_assoc]
  exact ut_triple_coefficient hb0 ij.1 jn.1 jn.2

private lemma ut_first_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    -(PowerSeries.coeff (d - 1) (formalOmega * (formalExternalOmega b hb *
        (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹)) *
      (HahnSeries.single 1 (1 : ℂ) * HahnSeries.C b *
        (HahnSeries.single 1 (1 : ℂ) + HahnSeries.C b + 2))) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (UMain1 d b hb) := by
  rw [ut_kernel_coefficient (d - 1) hb0]
  simp only [UMain1, map_sum, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro jn hjn
  have hsum : ij.1 + jn.1 + jn.2 = d - 1 := by
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hjn
    omega
  rw [mul_assoc, ← mul_neg, ut_first_term d ij.1 jn.1 jn.2 hsum hd]
  ring

private lemma ut_second_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 2 ≤ d) :
    -(PowerSeries.coeff (d - 2) (formalOmega * (formalExternalOmega b hb *
        (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹)) *
      (HahnSeries.single 1 (1 : ℂ) + HahnSeries.C b +
        2 * HahnSeries.single 1 (1 : ℂ) * HahnSeries.C b)) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (UMain2 d b hb) := by
  rw [ut_kernel_coefficient (d - 2) hb0]
  simp only [UMain2, if_pos hd, map_sum, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro jn hjn
  have hsum : ij.1 + jn.1 + jn.2 = d - 2 := by
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hjn
    omega
  rw [mul_assoc, ← mul_neg, ut_second_term d ij.1 jn.1 jn.2 hsum hd]
  ring

private lemma UCPoly_shift (d : ℕ) (b hb : ℂ) :
    UCPoly d b hb = -(Polynomial.X * CPoly d b hb) := by
  simp only [UCPoly, CPoly, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Polynomial.X_mul_monomial]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro ij hij
  have h1 := Finset.mem_range.mp hl
  have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have he : d - ij.1 - 1 + 1 = d - ij.1 := by omega
  rw [map_neg, he]

private lemma ut_scalar_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) :
    -(PowerSeries.coeff d ((formalOmega * formalExternalOmega b hb) *
      PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries)) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (UCPoly d b hb) := by
  rw [scalar_product_coefficient d hb0, UCPoly_shift, map_neg, map_mul, PE_X]
  have hs : (HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) *
      HahnSeries.single 1 1 = HahnSeries.single (-(d : ℤ)) 1 := by
    have he : -(d : ℤ) - 1 + 1 = -(d : ℤ) := by omega
    simp only [HahnSeries.single_mul_single, mul_one, he]
  calc
    _ = -((HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * HahnSeries.single 1 1) *
        (H : LaurentSeries ℂ) * PE (CPoly d b hb)) := by rw [hs]
    _ = _ := by ring

private lemma literal_ut_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    PowerSeries.coeff d (cubicUTSeries b hb) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) *
        (H : LaurentSeries ℂ) * (PUPoly d b hb : LaurentSeries ℂ) := by
  classical
  let a : LaurentSeries ℂ := HahnSeries.single 1 1
  let B : LaurentSeries ℂ := HahnSeries.C b
  let F := formalOmega * formalExternalOmega b hb
  let SC := PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries
  let J : AnnulusSeries := (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹
  let K := formalOmega * (formalExternalOmega b hb * J)
  let N0 := a * B * (a + B + 2)
  let N1 := a + B + 2 * a * B
  have hab : PowerSeries.C a * PowerSeries.C B =
      (PowerSeries.C (HahnSeries.single 1 b) : AnnulusSeries) := by
    rw [← map_mul]
    congr 1
    simp only [a, B, HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero, one_mul]
  have hshape : cubicUTSeries b hb =
      -((K * PowerSeries.X) * PowerSeries.C N0 +
        (K * PowerSeries.X ^ 2) * PowerSeries.C N1 + F * SC) := by
    change -(formalOmega * formalExternalOmega b hb) *
      (PowerSeries.X * (PowerSeries.C a * PowerSeries.C B *
        (PowerSeries.C a + PowerSeries.C B + 2) +
          PowerSeries.X * (PowerSeries.C a + PowerSeries.C B +
            2 * PowerSeries.C a * PowerSeries.C B)) *
        (2 * (PowerSeries.C a * PowerSeries.C B - PowerSeries.X) ^ 2)⁻¹ + SC) = _
    conv_lhs => arg 2; arg 1; arg 2; rw [hab]
    dsimp only [K, J, F, N0, N1]
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hshift1 : PowerSeries.coeff d (K * PowerSeries.X) =
      PowerSeries.coeff (d - 1) K := by
    simpa only [pow_one, if_pos hd] using PowerSeries.coeff_mul_X_pow' K 1 d
  have hshift2 := PowerSeries.coeff_mul_X_pow' K 2 d
  have hfirst : -(PowerSeries.coeff (d - 1) K * N0) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (UMain1 d b hb) := ut_first_coefficient d hb0 hd
  have hscalar : -(PowerSeries.coeff d (F * SC)) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * (H : LaurentSeries ℂ) *
        PE (UCPoly d b hb) := ut_scalar_coefficient d hb0
  rw [hshape, map_neg, map_add, map_add, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_C, hshift1, hshift2, neg_add, neg_add, hfirst, hscalar,
    ← PE_coe (PUPoly d b hb)]
  by_cases hd2 : 2 ≤ d
  · rw [if_pos hd2, ut_second_coefficient d hb0 hd2]
    simp only [PUPoly, UMain, map_add]
    ring
  · rw [if_neg hd2, zero_mul, neg_zero, add_zero]
    simp only [PUPoly, UMain, UMain2, if_neg hd2, add_zero, map_add]
    ring

/-- Actual all-degree TT finite-class membership for the literal kernel. -/
theorem cubicTT_finite_class (b hb : ℂ) (hb0 : b ≠ 0) (d : ℕ) (hd : 1 ≤ d) :
    ∃ p : Polynomial ℂ, p.degree < d ∧
      PowerSeries.coeff d (cubicTTSeries b hb) =
        HahnSeries.single (-(d : ℤ)) (1 : ℂ) *
          (H : LaurentSeries ℂ) * (p : LaurentSeries ℂ) := by
  refine ⟨PTPoly d b hb, PTPoly_degree d hb0 hd, ?_⟩
  exact literal_tt_coefficient d hb0 hd

/-- Actual all-degree UT finite-class membership for the literal kernel. -/
theorem cubicUT_finite_class (b hb : ℂ) (hb0 : b ≠ 0) (d : ℕ) (hd : 1 ≤ d) :
    ∃ p : Polynomial ℂ, p.degree < d + 1 ∧
      PowerSeries.coeff d (cubicUTSeries b hb) =
        HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) *
          (H : LaurentSeries ℂ) * (p : LaurentSeries ℂ) := by
  refine ⟨PUPoly d b hb, PUPoly_degree d b hb, ?_⟩
  exact literal_ut_coefficient d hb0 hd

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
