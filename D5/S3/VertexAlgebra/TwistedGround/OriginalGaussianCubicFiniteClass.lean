/-
  SOURCE ONLY, UNCOMPILED.

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
local notation "h" i => halfBinomial i

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
    PowerSeries.coeff_mk, smul_eq_mul, mul_one, Ring.choose_neg'] using hc

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
    (MPoly d b).degree ≤ (d + 1 : ℕ) := by
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
  have hlin : (Polynomial.X + Polynomial.C b + Polynomial.C 2).degree ≤ (1 : ℕ) := by
    apply Polynomial.degree_add_le_of_degree_le
    · exact Polynomial.degree_add_le_of_degree_le Polynomial.degree_X_le
        (Polynomial.degree_C_le.trans (by norm_num))
    · exact Polynomial.degree_C_le.trans (by norm_num)
  have hlin' :
      (Polynomial.C 2 * Polynomial.X * Polynomial.C b + Polynomial.X +
        Polynomial.C b).degree ≤ (1 : ℕ) := by
    apply Polynomial.degree_add_le_of_degree_le
    · apply Polynomial.degree_add_le_of_degree_le
      · simpa only [zero_add, add_zero] using
          (Polynomial.degree_mul_le_of_le
            (Polynomial.degree_mul_le_of_le
              (Polynomial.degree_C_le (a := (2 : ℂ)))
              (Polynomial.degree_X_le (R := ℂ)))
            (Polynomial.degree_C_le (a := b)))
      · exact Polynomial.degree_X_le
    · exact Polynomial.degree_C_le.trans (by norm_num)
  have hleft :
      (Polynomial.C b * (Polynomial.X + Polynomial.C b + Polynomial.C 2) *
        APoly d b).degree ≤ (d + 1 : ℕ) := by
    calc
      _ ≤ (0 : WithBot ℕ) + 1 + d :=
        Polynomial.degree_mul_le_of_le
          (Polynomial.degree_mul_le_of_le (Polynomial.degree_C_le (a := b)) hlin) hA
      _ = (d + 1 : ℕ) := by simp [add_assoc, add_comm, add_left_comm]
  have hright :
      ((Polynomial.C 2 * Polynomial.X * Polynomial.C b + Polynomial.X + Polynomial.C b) *
        APoly (d - 1) b).degree ≤ (d + 1 : ℕ) := by
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
      exact WithBot.coe_lt_coe.mpr (by omega)

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
    ∑ ij ∈ Finset.antidiagonal (d - (l + 1)),
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
  have hij' : ij.1 + ij.2 = d - (l + 1) := by omega
  have he : d - ij.1 - 1 < d := by omega
  exact (Polynomial.degree_monomial_le _ _).trans_lt he

private def PTPoly (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  Polynomial.C (hb / (2 * b)) * QPoly d b + CPoly d b hb

private lemma PTPoly_degree (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    (PTPoly d b hb).degree < d := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  apply max_lt
  · exact (Polynomial.degree_mul_le_of_le Polynomial.degree_C_le le_rfl).trans_lt
      (by simpa only [zero_add] using QPoly_degree d hb0 hd)
  · exact CPoly_degree d b hb

/- A literal coefficient expansion.  `aSeries` and `bSeries` are unfolded only
   here; all sums are finite because PowerSeries.coeff_mul uses the natural
   antidiagonal. -/
private lemma literal_tt_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    PowerSeries.coeff d (cubicTTSeries b hb) =
      HahnSeries.single (-(d : ℤ)) (1 : ℂ) *
        (H : LaurentSeries ℂ) * (PTPoly d b hb : LaurentSeries ℂ) := by
  classical
  have hq := QPoly_factor d hb0 hd
  have hscalar : PowerSeries.coeff 0 scalarCSeries = 0 := by
    simp [scalarCSeries]
  change PowerSeries.coeff d
    (formalOmega * formalExternalOmega b hb *
      ((PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) *
          PowerSeries.C (HahnSeries.C b) *
          (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) +
            PowerSeries.C (HahnSeries.C b)) +
        2 * (1 + PowerSeries.X) * PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) *
          PowerSeries.C (HahnSeries.C b) +
        PowerSeries.X * (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) +
          PowerSeries.C (HahnSeries.C b))) *
        (2 * (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) -
          PowerSeries.C (HahnSeries.C b)) ^ 2)⁻¹ +
      PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries))
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_map, hscalar]
  /- The remaining finite Laurent calculation is exactly:
       a⁻¹ H(a) · (hb/b)H(x/a)H(x/b) · polar/(2(a-b)²)
         = single(-d) H(a) (hb/(2b)) Q_d(a),
     with the scalar sum equal to `CPoly`.  `field_simp [hb0]` clears only
     finite powers of b, and `ring` closes the coefficient identities. -/
  simp only [formalOmega, formalExternalOmega, PowerSeries.coeff_mk,
    HahnSeries.coeff_single_mul, LaurentSeries.coeff_coe_powerSeries,
    HahnSeries.coeff_single, if_true, if_false]
  field_simp [hb0]
  ring_nf
  simpa [PTPoly, CPoly, QPoly, hq]

/- UT finite numerator.  The first antidiagonal splits i+j+n=d-1 and the
   second splits i+j+n=d-2.  The displayed monomials are the three terms of
   N₁ and the three terms of N₂ respectively. -/
private def UMain1 (d : ℕ) (b hb : ℂ) : Polynomial ℂ :=
  ∑ ij ∈ Finset.antidiagonal (d - 1),
    ∑ jn ∈ Finset.antidiagonal ij.2,
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
    ∑ ij ∈ Finset.antidiagonal (d - 2),
      ∑ jn ∈ Finset.antidiagonal ij.2,
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
    ∑ ij ∈ Finset.antidiagonal (d - (l + 1)),
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
    simp only [Finset.mem_antidiagonal] at hij hjn
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
      simp only [Finset.mem_antidiagonal] at hij hjn
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
  simp only [Finset.mem_range, Finset.mem_antidiagonal] at hl hij
  have he : d - ij.1 ≤ d := by omega
  exact (Polynomial.degree_monomial_le _ _).trans he

private lemma PUPoly_degree (d : ℕ) (b hb : ℂ) :
    (PUPoly d b hb).degree < d + 1 := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  exact (max_le (UMain_degree d b hb) (UCPoly_degree d b hb)).trans_lt
    (show (d : WithBot ℕ) < (d + 1 : ℕ) from
      WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))

private lemma literal_ut_coefficient (d : ℕ) {b hb : ℂ} (hb0 : b ≠ 0) (hd : 1 ≤ d) :
    PowerSeries.coeff d (cubicUTSeries b hb) =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) *
        (H : LaurentSeries ℂ) * (PUPoly d b hb : LaurentSeries ℂ) := by
  classical
  have hscalar : PowerSeries.coeff 0 scalarCSeries = 0 := by
    simp [scalarCSeries]
  have hu : (HahnSeries.single 1 b : LaurentSeries ℂ) ≠ 0 :=
    HahnSeries.single_ne_zero hb0
  have hunit (n : ℕ) :
      (PowerSeries.coeff n
        ((2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹)) =
        (n + 1 : ℂ) / (2 : ℂ) *
          (HahnSeries.single (-(n : ℤ) - 2) (b ^ (n + 2))⁻¹) := by
    let u : (LaurentSeries ℂ)ˣ :=
      Units.mk0 (HahnSeries.single 1 b) hu
    have hmul :
        (PowerSeries.C (1 / 2 : LaurentSeries ℂ) *
            PowerSeries.invUnitsSub u ^ 2) *
          (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2) = 1 := by
      rw [pow_two]
      simp [PowerSeries.invUnitsSub_mul_sub, u]
      ring
    have hinv :
        (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹ =
          PowerSeries.C (1 / 2 : LaurentSeries ℂ) * PowerSeries.invUnitsSub u ^ 2 := by
      apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hu])).mpr
      exact hmul
    rw [hinv, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_invUnitsSub,
      one_divp, Units.val_pow_eq_pow_val, HahnSeries.coeff_single,
      if_true, smul_eq_mul]
    field_simp [hb0]
    ring
  change PowerSeries.coeff d
    (-(formalOmega * formalExternalOmega b hb) *
      (PowerSeries.X *
          (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) *
            PowerSeries.C (HahnSeries.C b) *
              (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) +
                PowerSeries.C (HahnSeries.C b) + 2) +
            PowerSeries.X *
              (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) +
                PowerSeries.C (HahnSeries.C b) +
                2 * PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) *
                  PowerSeries.C (HahnSeries.C b))) *
        (2 * (PowerSeries.C (HahnSeries.single 1 b) - PowerSeries.X) ^ 2)⁻¹ +
      PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries))
  rw [PowerSeries.coeff_mul]
  simp only [map_neg, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_mk, PowerSeries.coeff_map, hscalar]
  simp only [formalOmega, formalExternalOmega, PowerSeries.coeff_mk,
    HahnSeries.coeff_single_mul, LaurentSeries.coeff_coe_powerSeries,
    HahnSeries.coeff_single, if_true, if_false, hunit]
  field_simp [hb0]
  ring_nf
  simpa [PUPoly, UMain, UMain1, UMain2, UCPoly]

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
