/- GID: D5/S1/Recurrence/CentralFactorialTransferExpansion
   generality: G
   mirror-B: D5/B/S1/Recurrence/CentralFactorialTransferExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central factorial coefficients give the binary spectral expansion. -/
/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19685.
Direct frozen dependencies: none (pinned Mathlib only).
The integer double factorial extension is written directly using Int.toNat and Nat.doubleFactorial.
mPoly: proof_shape: bind-only; consumer: mPoly_zero, mPoly_shift_succ, mPoly_shift_succ_right, mPoly_two_step, mPoly_comp_add_one, mPoly_comp_sub_one, mPoly_central_difference, centralCoeff, centralCoeff_zero, centralCoeff_one, centralCoeff_two_step, centralCoeff_central_difference, centralCoeff_one_succ, central_spectral_coeff, scalarExpansion, scalar_settlement, claim, claim_of_spectral_obligations. | dfBinom: proof_shape: bind-only; consumer: dfBinom_zero, dfBinom_step, dfBinom_choose, central_spectral_coeff, scalarExpansion, scalar_settlement, claim, claim_of_spectral_obligations.
scalarEigenvalue: proof_shape: bind-only; consumer: scalar_settlement, transfer_walsh, claim_of_spectral_obligations, claim_of_scalar_identity. | mPoly_zero: proof_shape: bind-only; consumer: centralCoeff_zero.
mPoly_one: proof_shape: bind-only; consumer: centralCoeff_one.
mPoly_shift_succ: proof_shape: bind-only; consumer: mPoly_two_step, mPoly_comp_sub_one. | mPoly_shift_succ_right: proof_shape: bind-only; consumer: mPoly_two_step, mPoly_comp_add_one.
mPoly_two_step: proof_shape: bind-only; consumer: centralCoeff_two_step. | mPoly_comp_add_one: proof_shape: bind-only; consumer: mPoly_central_difference, centralCoeff_one_succ.
mPoly_comp_sub_one: proof_shape: bind-only; consumer: mPoly_central_difference. | mPoly_central_difference: proof_shape: bind-only; consumer: centralCoeff_central_difference.
dfac_step_nat: proof_shape: bind-only; consumer: dfac_step. | dfac_cast_ne_zero: proof_shape: bind-only; consumer: dfBinom_zero.
dfac_step: proof_shape: bind-only; consumer: dfBinom_step. | dfBinom_zero: proof_shape: bind-only; consumer: dfBinom_choose.
dfBinom_step: proof_shape: bind-only; consumer: dfBinom_choose. | centralCoeff: proof_shape: bind-only; consumer: centralCoeff_zero, centralCoeff_one, centralCoeff_two_step, centralCoeff_central_difference, centralSeries, centralSeries_central_difference, centralCoeff_zero_recurrence, centralSeries_zero_ode, centralCoeff_one_succ, centralSeries_one, centralTransform_constantCoeff, coeff_transferSubst_trunc, centralWeighted_coeff, centralWeighted_coeff_even, central_spectral_coeff.
centralCoeff_zero: proof_shape: bind-only; consumer: centralSeries_central_difference, centralSeries_zero_ode, centralSeries_zero_square, centralSeries_one, centralTransform_constantCoeff. | centralCoeff_one: proof_shape: bind-only; consumer: centralSeries_zero_ode.
centralCoeff_two_step: proof_shape: bind-only; consumer: centralCoeff_zero_recurrence. | centralCoeff_central_difference: proof_shape: bind-only; consumer: centralSeries_central_difference.
centralSeries: proof_shape: bind-only; consumer: centralSeries_central_difference, centralSeries_zero_ode, centralSeries_zero_square, centralSeries_one, centralTransform, centralTransform_difference, centralTransform_constantCoeff, centralTransform_zero, centralTransform_one, coeff_transferSubst_trunc. | centralSeries_central_difference: proof_shape: bind-only; consumer: centralTransform_difference.
halfBinomial: proof_shape: bind-only; consumer: halfBinomial_add, halfBinomial_zero, halfBinomial_two, halfBinomial_even_coeff, halfBinomial_odd_coeff, halfBinomial_constantCoeff, inverseSqrt_square, transferSubst, transferSubst_X, centralTransform_difference, centralTransform_constantCoeff, centralTransform_zero, centralTransform_one, centralTransform_neg_one, halfBinomial_mul_shift, halfBinomial_nat_step, centralTransform_nat, centralTransform_neg_nat, centralTransform_difference_nat, halfBinomial_nat_mul, coeff_transferSubst_trunc, centralWeighted_coeff, centralWeighted_coeff_even, central_spectral_coeff. | halfBinomial_add: proof_shape: bind-only; consumer: inverseSqrt_square, halfBinomial_mul_shift, halfBinomial_nat_step, centralTransform_difference_nat, halfBinomial_nat_mul, centralWeighted_coeff.
halfBinomial_zero: proof_shape: bind-only; consumer: inverseSqrt_square, centralTransform_nat, centralTransform_neg_nat, halfBinomial_nat_mul. | halfBinomial_two: proof_shape: bind-only; consumer: inverseSqrt_square, halfBinomial_nat_step, centralTransform_difference_nat.
halfBinomial_even_coeff: proof_shape: bind-only; consumer: halfBinomial_constantCoeff, centralWeighted_coeff_even. | halfBinomial_odd_coeff: proof_shape: bind-only; consumer: centralWeighted_coeff_even.
halfBinomial_constantCoeff: proof_shape: bind-only; consumer: centralTransform_zero. | inverseSqrt_square: proof_shape: bind-only; consumer: centralTransform_zero.
centralCoeff_zero_recurrence: proof_shape: bind-only; consumer: centralSeries_zero_ode. | centralSeries_zero_ode: proof_shape: bind-only; consumer: centralSeries_zero_square.
centralSeries_zero_square: proof_shape: content; consumer: centralTransform_zero. | centralCoeff_one_succ: proof_shape: bind-only; consumer: centralSeries_one.
centralSeries_one: proof_shape: bind-only; consumer: centralTransform_one. | transferSubst: proof_shape: bind-only; consumer: transferSubst_X, centralTransform, centralTransform_difference, centralTransform_constantCoeff, centralTransform_zero, centralTransform_one, coeff_transferSubst_trunc.
transferSubst_X: proof_shape: bind-only; consumer: centralTransform_difference, centralTransform_zero, centralTransform_one. | centralTransform: proof_shape: bind-only; consumer: centralTransform_difference, centralTransform_constantCoeff, centralTransform_zero, centralTransform_one, centralTransform_neg_one, centralTransform_nat, centralTransform_neg_nat, centralTransform_difference_nat, coeff_transferSubst_trunc, centralWeighted_coeff, centralWeighted_coeff_even, central_spectral_coeff.
centralTransform_difference: proof_shape: bind-only; consumer: centralTransform_neg_one, centralTransform_nat, centralTransform_neg_nat. | centralTransform_constantCoeff: proof_shape: bind-only; consumer: centralTransform_zero.
centralTransform_zero: proof_shape: content; consumer: centralTransform_one, centralTransform_neg_one, centralTransform_nat, centralTransform_neg_nat. | centralTransform_one: proof_shape: content; consumer: centralTransform_neg_one, centralTransform_nat.
centralTransform_neg_one: proof_shape: content; consumer: centralTransform_neg_nat. | halfBinomial_mul_shift: proof_shape: bind-only; consumer: centralTransform_nat, centralTransform_neg_nat.
second_order_power: proof_shape: bind-only; consumer: centralTransform_nat, centralTransform_neg_nat. | halfBinomial_nat_step: proof_shape: bind-only; consumer: centralTransform_nat, centralTransform_neg_nat.
centralTransform_nat: proof_shape: content; consumer: centralTransform_difference_nat. | centralTransform_neg_nat: proof_shape: content; consumer: centralTransform_difference_nat.
centralTransform_difference_nat: proof_shape: content; consumer: central_spectral_coeff. | halfBinomial_nat_mul: proof_shape: bind-only; consumer: centralWeighted_coeff.
coeff_transferSubst_trunc: proof_shape: bind-only; consumer: centralWeighted_coeff. | centralWeighted_coeff: proof_shape: bind-only; consumer: centralWeighted_coeff_even.
sum_even_residual: proof_shape: bind-only; consumer: centralWeighted_coeff_even. | centralWeighted_coeff_even: proof_shape: bind-only; consumer: central_spectral_coeff.
choose_shift_step: proof_shape: bind-only; consumer: dfBinom_choose. | dfBinom_choose: proof_shape: bind-only; consumer: central_spectral_coeff.
central_spectral_coeff: proof_shape: content; consumer: scalar_settlement. escape_witness: central_spectral_coeff. | spectralPolynomial: proof_shape: bind-only; consumer: spectralPolynomial_degree, spectralPolynomial_eval_sum.
spectralPolynomial_degree: proof_shape: bind-only; consumer: spectralPolynomial_eval_sum. | spectralPolynomial_eval_sum: proof_shape: bind-only; consumer: scalar_settlement.
homogeneous_term: proof_shape: bind-only; consumer: scalar_settlement. | scalarExpansion: proof_shape: bind-only; consumer: scalar_settlement, claim_of_spectral_obligations, claim_of_scalar_identity.
scalar_settlement: proof_shape: content; consumer: result. escape_witness: central_spectral_coeff.
-/
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
variable {F : Type*} [Field F]
noncomputable def mPoly (j : ℕ) : Polynomial F :=
  ∏ k ∈ Finset.range j, (Polynomial.X - Polynomial.C ((j : F) - 1 - 2 * k))
noncomputable def dfBinom (n₁ n₂ : ℤ) : F := ((n₁).toNat.doubleFactorial : F) / (((n₂).toNat.doubleFactorial : F) * (((n₁ - n₂)).toNat.doubleFactorial : F))
noncomputable def scalarEigenvalue (m l : ℕ) (u : F) : F :=
  2 * (1 + u ^ 2) * (1 - u) ^ (2 * l) * (1 + u) ^ (2 * (m - l))
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open Polynomial Finset
variable {F : Type*} [Field F]
@[simp] private lemma mPoly_zero : mPoly (F := F) 0 = 1 := by
  exact toFinsupp_eq_one.mp rfl
@[simp] private lemma mPoly_one : mPoly (F := F) 1 = X := by simp [mPoly]
private lemma mPoly_shift_succ (r : ℕ) :
    mPoly (F := F) (r + 1) =
      (X - C (r : F)) * (mPoly r).comp (X + 1) := by
  simp only [mPoly, Finset.prod_range_succ', Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, sub_zero, add_sub_cancel_right]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Nat.cast_add, Nat.cast_one, map_sub, map_add, map_mul, map_ofNat, map_one]
  ring
private lemma mPoly_shift_succ_right (r : ℕ) :
    mPoly (F := F) (r + 1) =
      (mPoly r).comp (X - 1) * (X + C (r : F)) := by
  simp only [mPoly, Finset.prod_range_succ, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [map_sub, map_add, map_mul, map_ofNat, map_one]
    ring
  · try simp only [map_sub, map_add, map_mul, map_ofNat, map_one, map_neg]
    all_goals ring
private lemma mPoly_two_step (r : ℕ) :
    mPoly (F := F) (r + 2) =
      (X ^ 2 - C (((r : F) + 1) ^ 2)) * mPoly r := by
  rw [show r + 2 = (r + 1) + 1 by omega, mPoly_shift_succ,
    mPoly_shift_succ_right, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.comp_assoc]
  have hc : (X - 1 : Polynomial F).comp (X + 1) = X := by simp
  rw [hc, Polynomial.comp_X]
  simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1, Polynomial.C_pow]
  ring
private lemma mPoly_comp_add_one (r : ℕ) :
    (mPoly (F := F) (r + 1)).comp (X + 1) =
      mPoly r * (X + C ((r : F) + 1)) := by
  rw [mPoly_shift_succ_right, Polynomial.mul_comp, Polynomial.comp_assoc]
  have hc : (X - 1 : Polynomial F).comp (X + 1) = X := by simp
  rw [hc, Polynomial.comp_X]
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    map_add, map_one]
  ring
private lemma mPoly_comp_sub_one (r : ℕ) :
    (mPoly (F := F) (r + 1)).comp (X - 1) =
      (X - C ((r : F) + 1)) * mPoly r := by
  rw [mPoly_shift_succ, Polynomial.mul_comp, Polynomial.comp_assoc]
  have hc : (X + 1 : Polynomial F).comp (X - 1) = X := by simp
  rw [hc, Polynomial.comp_X]
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    map_add, map_one]
  ring
private lemma mPoly_central_difference (r : ℕ) :
    (mPoly (F := F) (r + 1)).comp (X + 1) -
      (mPoly (F := F) (r + 1)).comp (X - 1) =
      C (2 * ((r : F) + 1)) * mPoly r := by
  rw [mPoly_comp_add_one, mPoly_comp_sub_one]
  simp only [map_mul, map_add, map_ofNat, map_one]
  ring
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open Finset Polynomial
variable {F : Type*} [Field F] [CharZero F]
private lemma dfac_step_nat (a : ℤ) (ha : -1 ≤ a) :
    ((a + 2)).toNat.doubleFactorial = (a + 2).toNat * (a).toNat.doubleFactorial := by
  by_cases he : a = -1
  · subst a
    norm_num [Nat.doubleFactorial]
  · have hz : 0 ≤ a := by omega
    have ht : (a + 2).toNat = a.toNat + 2 := by omega
    simp only [ht, Nat.doubleFactorial_add_two]
private lemma dfac_cast_ne_zero (a : ℤ) : ((a).toNat.doubleFactorial : F) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (Nat.doubleFactorial_pos a.toNat)
private lemma dfac_step (a : ℤ) (ha : -1 ≤ a) :
    (((a + 2)).toNat.doubleFactorial : F) = ((a + 2 : ℤ) : F) * ((a).toNat.doubleFactorial : F) := by
  rw [dfac_step_nat a ha, Nat.cast_mul]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ a + 2)
private lemma dfBinom_zero (a : ℤ) : dfBinom (F := F) a 0 = 1 := by
  simp only [dfBinom, Int.sub_zero, Int.toNat_zero, Nat.doubleFactorial,
    Nat.cast_one, one_mul]
  exact div_self (dfac_cast_ne_zero (F := F) a)
private lemma dfBinom_step (a : ℤ) (ha : -1 ≤ a) (j : ℕ) :
    dfBinom (F := F) (a + 2 * (j + 1)) (2 * (j + 1)) =
      (((a : F) + 2 * ((j : F) + 1)) / (2 * ((j : F) + 1))) *
        dfBinom (F := F) (a + 2 * j) (2 * j) := by
  have hnum := dfac_step (F := F) (a + 2 * j) (by omega)
  have hden := dfac_step (F := F) (2 * (j : ℤ)) (by omega)
  have hx : a + 2 * ((j : ℤ) + 1) = (a + 2 * j) + 2 := by ring
  have hy : 2 * ((j : ℤ) + 1) = 2 * j + 2 := by
    exact mul_add_one (2 : ℤ) (j : ℤ)
  unfold dfBinom
  rw [hx, hy]
  simp only [show (a + 2 * (j : ℤ) + 2) - (2 * j + 2) = a by ring,
    show (a + 2 * (j : ℤ)) - 2 * j = a by ring]
  rw [hnum, hden]
  push_cast
  have hj : 2 * ((j : F) + 1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast Nat.succ_ne_zero j
  field_simp [dfac_cast_ne_zero, hj]
  <;> ring
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open Polynomial
variable {F : Type*} [Field F] [CharZero F]
private noncomputable def centralCoeff (x : F) (r : ℕ) : F :=
  (mPoly (F := F) r).eval x / (r.factorial : F)
private lemma centralCoeff_zero (x : F) : centralCoeff x 0 = 1 := by
  simp [centralCoeff]
private lemma centralCoeff_one (x : F) : centralCoeff x 1 = x := by
  simp [centralCoeff]
private lemma centralCoeff_two_step (x : F) (r : ℕ) :
    ((r : F) + 2) * ((r : F) + 1) * centralCoeff x (r + 2) =
      (x ^ 2 - ((r : F) + 1) ^ 2) * centralCoeff x r := by
  have hp := congrArg (Polynomial.eval x) (mPoly_two_step (F := F) r)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hp
  unfold centralCoeff
  rw [hp]
  have hf : (r.factorial : F) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr1 : (r : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have hr2 : (r : F) + 2 ≠ 0 := by exact_mod_cast (by omega : r + 2 ≠ 0)
  have hff : ((r + 2).factorial : F) =
      ((r : F) + 2) * ((r : F) + 1) * (r.factorial : F) := by
    rw [show r + 2 = (r + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hff]
  field_simp [hf, hr1, hr2]
  <;> ring
private lemma centralCoeff_central_difference (x : F) (r : ℕ) :
    centralCoeff (x + 1) (r + 1) - centralCoeff (x - 1) (r + 1) =
      2 * centralCoeff x r := by
  have hp := congrArg (Polynomial.eval x) (mPoly_central_difference (F := F) r)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C] at hp
  unfold centralCoeff
  rw [← sub_div, hp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (r.factorial : F) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr1 : (r : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp
  <;> ring
private noncomputable def centralSeries (x : F) : PowerSeries F :=
  PowerSeries.mk (centralCoeff x)
private lemma centralSeries_central_difference (x : F) :
    centralSeries (x + 1) - centralSeries (x - 1) =
      2 * PowerSeries.X * centralSeries x := by
  ext n
  cases n with
  | zero => simp [centralSeries, centralCoeff_zero]
  | succ n =>
    simp only [map_sub, centralSeries, PowerSeries.coeff_mk]
    rw [mul_assoc, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    exact centralCoeff_central_difference x n
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
variable {F : Type*} [Field F] [CharZero F]
private noncomputable def halfBinomial (a : F) : PowerSeries F :=
  PowerSeries.expand 2 (by decide)
    (PowerSeries.rescale (-1) (PowerSeries.binomialSeries F (a / 2)))
private lemma halfBinomial_add (a b : F) :
    halfBinomial (a + b) = halfBinomial a * halfBinomial b := by
  unfold halfBinomial
  rw [add_div, PowerSeries.binomialSeries_add, map_mul, map_mul]
private lemma halfBinomial_zero : halfBinomial (0 : F) = 1 := by
  simp [halfBinomial]
private lemma halfBinomial_two : halfBinomial (2 : F) = 1 - PowerSeries.X ^ 2 := by
  have h : (2 : F) / 2 = (1 : ℕ) := by norm_num
  unfold halfBinomial
  rw [h, PowerSeries.binomialSeries_nat]
  simp [PowerSeries.rescale_X, PowerSeries.expand_C, sub_eq_add_neg]
private lemma halfBinomial_even_coeff (a : F) (j : ℕ) :
    PowerSeries.coeff (2 * j) (halfBinomial a) =
      (-1 : F) ^ j * Ring.choose (a / 2) j := by
  simp [halfBinomial, PowerSeries.coeff_expand_mul, smul_eq_mul]
private lemma halfBinomial_odd_coeff (a : F) (j : ℕ) :
    PowerSeries.coeff (2 * j + 1) (halfBinomial a) = 0 := by
  have hn : ¬ 2 ∣ 2 * j + 1 := by exact Nat.not_two_dvd_bit1 j
  simp [halfBinomial, PowerSeries.coeff_expand, hn]
private lemma halfBinomial_constantCoeff (a : F) :
    PowerSeries.constantCoeff (halfBinomial a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simpa using halfBinomial_even_coeff a 0
private lemma inverseSqrt_square :
    halfBinomial (-1 : F) ^ 2 * (1 - PowerSeries.X ^ 2) = 1 := by
  rw [pow_two, ← halfBinomial_two, ← halfBinomial_add, ← halfBinomial_add]
  norm_num [halfBinomial_zero]
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open PowerSeries
variable {F : Type*} [Field F] [CharZero F]
private lemma centralCoeff_zero_recurrence (r : ℕ) :
    ((r : F) + 2) * centralCoeff (0 : F) (r + 2) +
      ((r : F) + 1) * centralCoeff (0 : F) r = 0 := by
  have h := centralCoeff_two_step (F := F) 0 r
  have hr : (r : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have hz : ((r : F) + 1) * (((r : F) + 2) * centralCoeff (0 : F) (r + 2) +
      ((r : F) + 1) * centralCoeff (0 : F) r) = 0 := by
    calc
      _ = ((r : F) + 2) * ((r : F) + 1) * centralCoeff (0 : F) (r + 2) +
          ((r : F) + 1) ^ 2 * centralCoeff (0 : F) r := by ring
      _ = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp hz).resolve_left hr
private lemma centralSeries_zero_ode :
    (1 + X ^ 2) * derivative (centralSeries (0 : F)) + X * centralSeries (0 : F) = 0 := by
  rw [add_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp [centralSeries]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp [centralCoeff_one]
  | succ n =>
    cases n with
    | zero =>
      have h := centralCoeff_zero_recurrence (F := F) 0
      simpa [coeff_X_pow_mul', coeff_derivative, centralSeries, centralCoeff_zero,
        one_add_one_eq_two, mul_comm] using h
    | succ n =>
      have h := centralCoeff_zero_recurrence (F := F) (n + 1)
      simp only [map_add, map_zero, coeff_succ_X_mul, coeff_X_pow_mul',
        show 2 ≤ n + 1 + 1 by omega, ite_true,
        show n + 1 + 1 - 2 = n by omega, coeff_derivative,
        centralSeries, coeff_mk]
      simp only [Nat.cast_add, Nat.cast_one] at h ⊢
      linear_combination h
private lemma centralSeries_zero_square :
    (1 + X ^ 2) * centralSeries (0 : F) ^ 2 = 1 := by
  have hd : derivative ((1 + X ^ 2) * centralSeries (0 : F) ^ 2) = 0 := by
    calc
      _ = 2 * centralSeries (0 : F) *
          ((1 + X ^ 2) * derivative (centralSeries (0 : F)) + X * centralSeries (0 : F)) := by
        simp only [Derivation.leibniz, map_add, derivative_one, derivative_pow,
          derivative_X, smul_eq_mul, pow_one, Nat.cast_ofNat, mul_one]
        ring
      _ = 0 := by rw [centralSeries_zero_ode, mul_zero]
  apply PowerSeries.derivative.ext
  · simpa only [derivative_one] using hd
  · have hc : constantCoeff (centralSeries (0 : F)) = 1 := by
      change centralCoeff (0 : F) 0 = 1
      exact centralCoeff_zero 0
    simp only [map_mul, map_add, map_pow, map_one, constantCoeff_X, hc]
    norm_num
private lemma centralCoeff_one_succ (r : ℕ) :
    centralCoeff (1 : F) (r + 1) = centralCoeff (0 : F) r := by
  have hp := congrArg (Polynomial.eval (0 : F)) (mPoly_comp_add_one (F := F) r)
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, zero_add] at hp
  unfold centralCoeff
  rw [hp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (r.factorial : F) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr : (r : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp
private lemma centralSeries_one : centralSeries (1 : F) = 1 + X * centralSeries (0 : F) := by
  ext n
  cases n with
  | zero => simp [centralSeries, centralCoeff_zero]
  | succ n => simpa [centralSeries] using centralCoeff_one_succ (F := F) n
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open PowerSeries
variable {F : Type*} [Field F] [CharZero F]
private noncomputable def transferSubst : PowerSeries F →ₐ[F] PowerSeries F :=
  PowerSeries.substAlgHom (show PowerSeries.HasSubst
    (PowerSeries.X * halfBinomial (-1 : F)) from PowerSeries.HasSubst.X'.mul_left)
private lemma transferSubst_X : transferSubst (F := F) X = X * halfBinomial (-1 : F) := by
  simp [transferSubst, PowerSeries.substAlgHom_X]
private noncomputable def centralTransform (x : F) : PowerSeries F :=
  transferSubst (centralSeries x)
private lemma centralTransform_difference (x : F) :
    centralTransform (x + 1) - centralTransform (x - 1) =
      2 * (X * halfBinomial (-1 : F)) * centralTransform x := by
  have h := congrArg (transferSubst (F := F)) (centralSeries_central_difference x)
  simpa only [map_sub, map_mul, map_ofNat, transferSubst_X, centralTransform] using h
private lemma centralTransform_constantCoeff (x : F) :
    constantCoeff (centralTransform x) = 1 := by
  have hc : constantCoeff (centralSeries x) = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simpa only [centralSeries, coeff_mk] using centralCoeff_zero x
  unfold centralTransform transferSubst
  rw [PowerSeries.coe_substAlgHom, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero (by
      rw [← PowerSeries.constantCoeff_eq]
      simp), hc]
  simp
private lemma centralTransform_zero :
    halfBinomial (-1 : F) * centralTransform 0 = 1 := by
  have hs := inverseSqrt_square (F := F)
  have hz : 1 + (X * halfBinomial (-1 : F)) ^ 2 = halfBinomial (-1 : F) ^ 2 := by
    linear_combination -hs
  have hm := congrArg (transferSubst (F := F)) (centralSeries_zero_square (F := F))
  simp only [map_mul, map_add, map_one, map_pow, transferSubst_X] at hm
  rw [hz] at hm
  change halfBinomial (-1 : F) ^ 2 * centralTransform 0 ^ 2 = 1 at hm
  have hp : (halfBinomial (-1 : F) * centralTransform 0 - 1) *
      (halfBinomial (-1 : F) * centralTransform 0 + 1) = 0 := by
    linear_combination hm
  rcases mul_eq_zero.mp hp with h | h
  · exact sub_eq_zero.mp h
  · have hc := congrArg (constantCoeff (R := F)) h
    simp only [map_add, map_one, map_zero, map_mul, halfBinomial_constantCoeff,
      centralTransform_constantCoeff, one_mul] at hc
    norm_num at hc
private lemma centralTransform_one : centralTransform (1 : F) = 1 + X := by
  have h := congrArg (transferSubst (F := F)) (centralSeries_one (F := F))
  simp only [map_add, map_one, map_mul, transferSubst_X] at h
  change centralTransform (1 : F) =
    1 + (X * halfBinomial (-1 : F)) * centralTransform 0 at h
  rw [mul_assoc, centralTransform_zero, mul_one] at h
  exact h
private lemma centralTransform_neg_one : centralTransform (-1 : F) = 1 - X := by
  have h := centralTransform_difference (F := F) 0
  simp only [zero_add, zero_sub, centralTransform_one] at h
  have h0 : 2 * (X * halfBinomial (-1 : F)) * centralTransform 0 = 2 * X := by
    calc
      _ = 2 * X * (halfBinomial (-1 : F) * centralTransform 0) := by ring
      _ = _ := by rw [centralTransform_zero, mul_one]
  rw [h0] at h
  linear_combination -h
private lemma halfBinomial_mul_shift (a : F) :
    halfBinomial (a + 1) * (X * halfBinomial (-1 : F)) = X * halfBinomial a := by
  calc
    _ = X * (halfBinomial (a + 1) * halfBinomial (-1 : F)) := by ring
    _ = _ := by rw [← halfBinomial_add]; congr 1; congr 1; ring
private lemma second_order_power {R : Type*} [CommRing R] (t : R) (a : ℕ → R)
    (h0 : a 0 = 1) (h1 : a 1 = 1 + t)
    (hrec : ∀ m, a (m + 2) = 2 * t * a (m + 1) + (1 - t ^ 2) * a m)
    (m : ℕ) : a m = (1 + t) ^ m := by
  let E : LinearRecurrence R := ⟨2, ![1 - t ^ 2, 2 * t]⟩
  have ha : E.IsSolution a := by
    intro n
    simpa [E, Fin.sum_univ_two, add_comm] using hrec n
  have hb : E.IsSolution (fun n => (1 + t) ^ n) := by
    intro n
    simp only [E, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, Nat.add_zero]
    simp only [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  have he : a = (fun n => (1 + t) ^ n) :=
    (E.eq_iff_eqOn_range_order _ _ ha hb).2 (by
      intro n hn
      have hlt : n < 2 := by exact List.mem_range.mp hn
      have hn' : n = 0 ∨ n = 1 := by exact List.mem_pair.mp hn
      rcases hn' with rfl | rfl <;> simp [h0, h1])
  exact congrFun he m
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open PowerSeries
variable {F : Type*} [Field F] [CharZero F]
private lemma halfBinomial_nat_step (m : ℕ) :
    halfBinomial ((m : F) + 1) =
      (1 - X ^ 2) * halfBinomial ((m : F) - 1) := by
  rw [← halfBinomial_two, ← halfBinomial_add]
  congr 1
  ring
private lemma centralTransform_nat (m : ℕ) :
    halfBinomial ((m : F) - 1) * centralTransform (m : F) = (1 + X) ^ m := by
  refine second_order_power X
    (fun k => halfBinomial ((k : F) - 1) * centralTransform (k : F)) ?_ ?_ ?_ m
  · simpa using centralTransform_zero (F := F)
  · simp [halfBinomial_zero, centralTransform_one]
  · intro k
    push_cast
    simp only [show (k : F) + 2 - 1 = (k : F) + 1 by ring, add_sub_cancel_right]
    have hc : centralTransform ((k : F) + 2) - centralTransform (k : F) =
        2 * (X * halfBinomial (-1 : F)) * centralTransform ((k : F) + 1) := by
      convert centralTransform_difference ((k : F) + 1) using 1 <;> congr 1 <;> ring
    have hB := halfBinomial_nat_step (F := F) k
    have hS := halfBinomial_mul_shift (F := F) (k : F)
    have hc' := congrArg (fun v => halfBinomial ((k : F) + 1) * v) hc
    rw [mul_sub] at hc'
    rw [show halfBinomial ((k : F) + 1) *
        (2 * (X * halfBinomial (-1 : F)) * centralTransform ((k : F) + 1)) =
        2 * (halfBinomial ((k : F) + 1) * (X * halfBinomial (-1 : F))) *
          centralTransform ((k : F) + 1) by ring, hS] at hc'
    have hb : halfBinomial ((k : F) + 1) * centralTransform (k : F) =
        (1 - X ^ 2) * (halfBinomial ((k : F) - 1) * centralTransform (k : F)) := by
      rw [hB]
      ring
    rw [hb] at hc'
    convert (sub_eq_iff_eq_add.mp hc') using 1 <;> ring
private lemma centralTransform_neg_nat (m : ℕ) :
    halfBinomial ((m : F) - 1) * centralTransform (-(m : F)) = (1 - X) ^ m := by
  have h := second_order_power (-X : PowerSeries F)
    (fun k => halfBinomial ((k : F) - 1) * centralTransform (-(k : F)))
  apply (h ?_ ?_ ?_ m).trans
  · simp only [sub_eq_add_neg]
  · simpa using centralTransform_zero (F := F)
  · simp [halfBinomial_zero, centralTransform_neg_one, sub_eq_add_neg]
  · intro k
    push_cast
    simp only [show (k : F) + 2 - 1 = (k : F) + 1 by ring, add_sub_cancel_right]
    have hc : centralTransform (-(k : F)) - centralTransform (-((k : F) + 2)) =
        2 * (X * halfBinomial (-1 : F)) * centralTransform (-((k : F) + 1)) := by
      convert centralTransform_difference (-((k : F) + 1)) using 1 <;> congr 1 <;> ring
    have hB := halfBinomial_nat_step (F := F) k
    have hS := halfBinomial_mul_shift (F := F) (k : F)
    have hc' := congrArg (fun v => halfBinomial ((k : F) + 1) * v) hc
    rw [mul_sub] at hc'
    rw [show halfBinomial ((k : F) + 1) *
        (2 * (X * halfBinomial (-1 : F)) * centralTransform (-((k : F) + 1))) =
        2 * (halfBinomial ((k : F) + 1) * (X * halfBinomial (-1 : F))) *
          centralTransform (-((k : F) + 1)) by ring, hS] at hc'
    have hb : halfBinomial ((k : F) + 1) * centralTransform (-(k : F)) =
        (1 - X ^ 2) * (halfBinomial ((k : F) - 1) * centralTransform (-(k : F))) := by
      rw [hB]
      ring
    rw [hb] at hc'
    linear_combination -hc'
private lemma centralTransform_difference_nat (a b : ℕ) :
    halfBinomial ((a : F) + b - 1) * centralTransform ((a : F) - b) =
      (1 + X) ^ a * (1 - X) ^ b := by
  induction a generalizing b with
  | zero => simpa using centralTransform_neg_nat (F := F) b
  | succ a ih =>
    cases b with
    | zero => simpa using centralTransform_nat (F := F) (a + 1)
    | succ b =>
      have hi := ih b
      have he : halfBinomial (((a + 1 : ℕ) : F) + (b + 1 : ℕ) - 1) =
          (1 - X ^ 2) * halfBinomial ((a : F) + b - 1) := by
        rw [← halfBinomial_two, ← halfBinomial_add]
        congr 1
        push_cast
        ring
      have hx : (((a + 1 : ℕ) : F) - (b + 1 : ℕ)) = (a : F) - b := by
        push_cast; ring
      rw [he, hx, mul_assoc, hi, pow_succ, pow_succ]
      ring
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open PowerSeries Finset
variable {F : Type*} [Field F] [CharZero F]
private lemma halfBinomial_nat_mul (a : F) (r : ℕ) :
    halfBinomial (a * r) = halfBinomial a ^ r := by
  induction r with
  | zero => simp [halfBinomial_zero]
  | succ r ih => simp [Nat.cast_add, mul_add, halfBinomial_add, ih, pow_succ]
private lemma coeff_transferSubst_trunc (x : F) (k i : ℕ) (hi : i ≤ k) :
    coeff i (centralTransform x) = coeff i
      (∑ r ∈ range (k + 1), C (centralCoeff x r) *
        (X * halfBinomial (-1 : F)) ^ r) := by
  have hb : PowerSeries.HasSubst (X * halfBinomial (-1 : F)) :=
    PowerSeries.HasSubst.X'.mul_left
  have hz (r : ℕ) (hr : i < r) :
      coeff i ((X * halfBinomial (-1 : F)) ^ r) = 0 := by
    rw [mul_pow, coeff_X_pow_mul']
    simp [show ¬r ≤ i by omega]
  unfold centralTransform transferSubst
  rw [PowerSeries.coe_substAlgHom]
  rw [coeff_subst' hb]
  have hs : Function.support (fun r => coeff r (centralSeries x) •
      coeff i ((X * halfBinomial (-1 : F)) ^ r)) ⊆ (range (k + 1) : Set ℕ) := by
    intro r hr
    by_contra hn
    have hh : i < r := by simp only [mem_coe, mem_range] at hn; omega
    exact hr (by dsimp only; rw [hz r hh, smul_zero])
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [map_sum, coeff_C_mul, smul_eq_mul, centralSeries, coeff_mk]
private lemma centralWeighted_coeff (a x : F) (k : ℕ) :
    coeff k (halfBinomial a * centralTransform x) =
      ∑ r ∈ range (k + 1), centralCoeff x r *
        coeff (k - r) (halfBinomial (a - r)) := by
  have htr : coeff k (halfBinomial a * centralTransform x) =
      coeff k (halfBinomial a *
        ∑ r ∈ range (k + 1), C (centralCoeff x r) *
          (X * halfBinomial (-1 : F)) ^ r) := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [coeff_transferSubst_trunc x k p.2 (by
      have := Finset.mem_antidiagonal.mp hp; omega)]
  rw [htr, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r ≤ k := by exact mem_range_succ_iff.mp hr
  have hB : halfBinomial a * halfBinomial (-1 : F) ^ r = halfBinomial (a - r) := by
    rw [← halfBinomial_nat_mul, ← halfBinomial_add]
    congr 1
    ring
  have he : halfBinomial a *
      (C (centralCoeff x r) * (X * halfBinomial (-1 : F)) ^ r) =
      C (centralCoeff x r) * (X ^ r * halfBinomial (a - r)) := by
    rw [mul_pow, ← hB]
    ring
  rw [he, coeff_C_mul, coeff_X_pow_mul', if_pos hrk]
private lemma sum_even_residual (k : ℕ) (c d : ℕ → F) (ho : ∀ j, d (2 * j + 1) = 0) :
    (∑ r ∈ range (k + 1), c r * d (k - r)) =
      ∑ j ∈ range (k / 2 + 1), c (k - 2 * j) * d (2 * j) := by
  classical
  have hp (r : ℕ) (hr : r ∈ range (k + 1)) (hne : c r * d (k-r) ≠ 0) :
      2 * ((k-r)/2) = k-r := by
    have hrk : r ≤ k := by exact mem_range_succ_iff.mp hr
    have hm : (k-r)%2 < 2 := Nat.mod_lt _ (by decide)
    by_contra he
    have hh : k-r = 2*((k-r)/2)+1 := by omega
    exact hne (by rw [hh, ho, mul_zero])
  refine Finset.sum_bij_ne_zero (fun r _ _ => (k-r)/2) ?_ ?_ ?_ ?_
  · intro r hr hne
    have := hp r hr hne
    simp only [mem_range] at hr ⊢
    omega
  · intro r hr hne s hs hsne heq
    have := hp r hr hne
    have := hp s hs hsne
    simp only [mem_range] at hr hs
    omega
  · intro j hj hne
    have hjk : 2*j ≤ k := by simp only [mem_range] at hj; omega
    refine ⟨k-2*j, by simp only [mem_range]; omega, ?_, ?_⟩
    · simpa only [Nat.sub_sub_self hjk] using hne
    · omega
  · intro r hr hne
    have he := hp r hr hne
    have hrk : r ≤ k := by exact mem_range_succ_iff.mp hr
    rw [he, Nat.sub_sub_self hrk]
private lemma centralWeighted_coeff_even (a x : F) (k : ℕ) :
    coeff k (halfBinomial a * centralTransform x) =
      ∑ j ∈ range (k / 2 + 1), centralCoeff x (k - 2*j) *
        ((-1 : F)^j * Ring.choose ((a - (k - 2*j : ℕ)) / 2) j) := by
  rw [centralWeighted_coeff]
  let d : ℕ → F := fun v => coeff v (halfBinomial (a - (k-v : ℕ)))
  have hodd : ∀ j, d (2*j+1) = 0 := by
    intro j
    exact halfBinomial_odd_coeff _ j
  have he := sum_even_residual (F := F) k (centralCoeff x) d hodd
  have hleft : (∑ r ∈ range (k+1), centralCoeff x r * d (k-r)) =
      ∑ r ∈ range (k+1), centralCoeff x r * coeff (k-r) (halfBinomial (a-r)) := by
    apply sum_congr rfl
    intro r hr
    have hrk : r ≤ k := by exact mem_range_succ_iff.mp hr
    simp only [d, Nat.sub_sub_self hrk]
  rw [hleft] at he
  rw [he]
  apply sum_congr rfl
  intro j hj
  dsimp [d]
  rw [halfBinomial_even_coeff]
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
variable {F : Type*} [Field F] [CharZero F]
private lemma choose_shift_step (a : F) (j : ℕ) :
    Ring.choose (a + ((j : F) + 1)) (j + 1) =
      ((a + ((j : F) + 1)) / ((j : F) + 1)) * Ring.choose (a + j) j := by
  have h := Ring.choose_add_smul_choose (a + (j : F)) j 1
  have hh : ((j : F) + 1) * Ring.choose (a + (j : F) + 1) (j + 1) =
      (a + (j : F) + 1) * Ring.choose (a + (j : F)) j := by
    simpa only [Nat.choose_one_right, Ring.choose_one_right, Nat.cast_one,
      Nat.cast_add, nsmul_eq_mul] using h
  have hj : (j : F) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [← add_assoc]
  field_simp [hj]
  linear_combination hh
private lemma dfBinom_choose (a : ℤ) (ha : -1 ≤ a) (j : ℕ) :
    dfBinom (F := F) (a + 2 * j) (2 * j) =
      Ring.choose ((a : F) / 2 + (j : F)) j := by
  induction j with
  | zero => simp [dfBinom_zero]
  | succ j ih =>
    push_cast
    rw [dfBinom_step a ha j, ih]
    push_cast
    rw [choose_shift_step]
    congr 1
    field_simp <;> ring
end D5.S1.Recurrence.CentralFactorialTransferExpansion
namespace D5.S1.Recurrence.CentralFactorialTransferExpansion
open PowerSeries Finset
variable {F : Type*} [Field F] [CharZero F]
lemma central_spectral_coeff (m l k : ℕ) (hl : l ≤ m) (hk : k ≤ m) :
    coeff k ((1 + X : PowerSeries F) ^ (m-l) * (1-X) ^ l) =
      ∑ j ∈ range (k/2+1),
        (dfBinom (((m+1 : ℕ) : ℤ) - k - 2 + 2*j) (2*j) * (-1)^j /
          ((k-2*j).factorial : F)) *
          (mPoly (F := F) (k-2*j)).eval ((m : F)-2*l) := by
  have h := centralTransform_difference_nat (F := F) (m-l) l
  have he : ((m-l : ℕ) : F) + (l : F) - 1 = (m : F)-1 := by
    rw [Nat.cast_sub hl]; ring
  have hx : ((m-l : ℕ) : F) - (l : F) = (m : F)-2*l := by
    rw [Nat.cast_sub hl]; ring
  rw [he, hx] at h
  rw [← h, centralWeighted_coeff_even]
  apply sum_congr rfl
  intro j hj
  have hjk : 2*j ≤ k := by simp only [mem_range] at hj; omega
  have hd := dfBinom_choose (F := F) (((m+1 : ℕ) : ℤ)-k-2) (by omega) j
  have ha : (((((m+1 : ℕ) : ℤ)-k-2) : ℤ) : F)/2 + (j : F) =
      ((m : F)-1-((k-2*j : ℕ) : F))/2 := by
    rw [Nat.cast_sub hjk]
    push_cast
    ring
  rw [ha] at hd
  rw [hd]
  unfold centralCoeff
  ring
private noncomputable def spectralPolynomial (m l : ℕ) : Polynomial F :=
  (1 + Polynomial.X) ^ (m-l) * (1-Polynomial.X) ^ l
private lemma spectralPolynomial_degree (m l : ℕ) (hl : l ≤ m) :
    (spectralPolynomial (F := F) m l).natDegree < m+1 := by
  unfold spectralPolynomial
  have hd1 : (1 + Polynomial.X : Polynomial F).natDegree ≤ 1 := by
    compute_degree
  have hd2 : (1 - Polynomial.X : Polynomial F).natDegree ≤ 1 := by
    compute_degree
  have hh := Polynomial.natDegree_mul_le
    (p := (1 + Polynomial.X : Polynomial F) ^ (m-l)) (q := (1-Polynomial.X) ^ l)
  have h1 := Polynomial.natDegree_pow_le (p := (1+Polynomial.X : Polynomial F)) (n := m-l)
  have h2 := Polynomial.natDegree_pow_le (p := (1-Polynomial.X : Polynomial F)) (n := l)
  nlinarith [Nat.sub_add_cancel hl]
private lemma spectralPolynomial_eval_sum (m l : ℕ) (hl : l ≤ m) (t : F) :
    (1+t)^(m-l) * (1-t)^l =
      ∑ k ∈ range (m+1), coeff k ((1+X : PowerSeries F)^(m-l)*(1-X)^l) * t^k := by
  have h := PowerSeries.eval₂_trunc_eq_sum_range t (RingHom.id F) (m+1)
    ((spectralPolynomial (F := F) m l : Polynomial F) : PowerSeries F)
  rw [PowerSeries.trunc_coe_eq_self (spectralPolynomial_degree m l hl)] at h
  simpa [spectralPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow] using h
private lemma homogeneous_term (a b : F) (N k : ℕ) (hk : k ≤ N) (ha : a ≠ 0) :
    a^(N-k)*b^k = a^N*(b/a)^k := by
  rw [div_pow, ← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero k ha)).2
  calc
    _ = (a^(N-k)*a^k)*b^k := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]
noncomputable def scalarExpansion (m l : ℕ) (u : F) : F :=
  2 * ∑ k ∈ range (m+1), ((1+u^2)^(m+1-k)*(2*u)^k) *
    ∑ j ∈ range (k/2+1),
      (dfBinom (((m+1 : ℕ) : ℤ)-k-2+2*j) (2*j)*(-1)^j/
        ((k-2*j).factorial : F)) *
        (mPoly (F := F) (k-2*j)).eval ((m : F)-2*(l : F))
lemma scalar_settlement (m l : ℕ) (hl : l ≤ m) (u : F) :
    scalarEigenvalue m l u = scalarExpansion m l u := by
  by_cases hq : 1+u^2 = 0
  · unfold scalarEigenvalue scalarExpansion
    rw [hq]
    simp only [mul_zero, zero_mul]
    symm
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro k hk
    have hk' : 0 < m+1-k := Nat.pos_of_ne_zero (mem_range_sub_ne_zero hk)
    rw [zero_pow (Nat.ne_of_gt hk'), zero_mul, zero_mul]
  · have hs := spectralPolynomial_eval_sum (F := F) m l hl ((2*u)/(1+u^2))
    have he : scalarExpansion m l u =
        2*(1+u^2)^(m+1)*((1+(2*u)/(1+u^2))^(m-l)*(1-(2*u)/(1+u^2))^l) := by
      rw [hs]
      unfold scalarExpansion
      rw [Finset.mul_sum, Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ m := by exact mem_range_succ_iff.mp hk
      rw [central_spectral_coeff m l k hl hk', homogeneous_term _ _ _ _ (by omega) hq]
      ring
    rw [he]
    have hp : 1+(2*u)/(1+u^2) = (1+u)^2/(1+u^2) := by field_simp [hq]; ring
    have hm : 1-(2*u)/(1+u^2) = (1-u)^2/(1+u^2) := by field_simp [hq]; ring
    rw [hp, hm, div_pow, div_pow]
    unfold scalarEigenvalue
    have hadd : m-l+l=m := Nat.sub_add_cancel hl
    rw [pow_mul, pow_mul]
    have hpower : (1+u^2)^(m+1) =
        (1+u^2)*((1+u^2)^(m-l)*(1+u^2)^l) := by
      rw [← pow_add, hadd, pow_succ]
      ring
    rw [hpower]
    field_simp [hq]
    <;> ring
end D5.S1.Recurrence.CentralFactorialTransferExpansion
