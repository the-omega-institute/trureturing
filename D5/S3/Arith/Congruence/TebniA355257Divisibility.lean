/- GID: D5/S3/Arith/Congruence/TebniA355257Divisibility
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/TebniA355257Divisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Tebni's divisibility criterion for logarithmic coefficients. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25143
admission_basis: open-problem-resolution (#18639; Proved).
All theorem declarations have proof_shape: bind-only; escape_witness: none.
The shared coefficient and residue arguments belong to this settling module.
The quotient helpers are consumed by TebniA355257Quotient.result (#18640).
Direct frozen dependencies: LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime;
declaration identities and per-declaration consumers are listed below.
utility_reason: Universal symbolic series and divisibility arguments; the small
prime cases are parts of the universal proof, not separate certified instances.

Per-declaration judgement (the module basis above applies to each row):
name | proof_shape | Direct frozen dependencies | escape_witness | consumers
L | bind-only | none | none | TebniA355257Divisibility.coeff_L, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Divisibility.claim, TebniA355257Divisibility.A, TebniA355257Quotient.claim, TebniA355257Quotient.result
A | bind-only | none | none | TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Divisibility.claim, TebniA355257Quotient.claim, TebniA355257Quotient.result
log_derivative | bind-only | none | none | TebniA355257Divisibility.coeff_L, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.log_inv, TebniA355257Divisibility.log_mul, TebniA355257Divisibility.result, TebniA355257Quotient.result
log_mul | bind-only | none | none | TebniA355257Divisibility.coeff_L, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.log_inv, TebniA355257Divisibility.result, TebniA355257Quotient.result
log_inv | bind-only | none | none | TebniA355257Divisibility.coeff_L, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Quotient.result
coeff_log_linear | bind-only | none | none | TebniA355257Divisibility.coeff_L, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Quotient.result
coeff_L | bind-only | none | none | TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Quotient.result
inverse_coeff | bind-only | none | none | TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.result, TebniA355257Quotient.result
B_zero | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.T_self, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
B_one | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.T_pred, TebniA355257Quotient.result
T | bind-only | none | none | TebniA355257Divisibility.T_multiple, TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.Z, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.T_pred, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.T_self, TebniA355257Divisibility.T_lower, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
Z | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.A_eq_Z, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
A_eq_Z | bind-only | none | none | TebniA355257Divisibility.result, TebniA355257Quotient.result
quotient_multiple | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.T_lower, TebniA355257Divisibility.lower_pred_multiple, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
T_multiple | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.T_lower, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
T_self | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
T_lower | bind-only | none | none | TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.reduction, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
reduction | bind-only | none | none | TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Divisibility.prime_residue, TebniA355257Quotient.result
prime_residue | bind-only | none | none | TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Quotient.result
composite_factorial | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | TebniA355257Divisibility.composite_divides, TebniA355257Divisibility.even_pred_divides, TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff, TebniA355257Quotient.result
composite_divides | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | TebniA355257Divisibility.result, TebniA355257Divisibility.divides_iff
divides_iff | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | TebniA355257Divisibility.result
lower_pred_multiple | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.even_pred_divides, TebniA355257Quotient.result
T_pred | bind-only | none | none | TebniA355257Divisibility.pred_reduction, TebniA355257Divisibility.even_pred_divides, TebniA355257Quotient.result
pred_reduction | bind-only | none | none | TebniA355257Divisibility.even_pred_divides, TebniA355257Quotient.result
even_pred_divides | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | TebniA355257Quotient.result
claim | bind-only | none | none | TebniA355257Divisibility.result
result | bind-only | D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600 | none | source conjecture
-/

import Mathlib.RingTheory.PowerSeries.Log
import D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace D5.S3.Arith.Congruence.TebniA355257Divisibility
open PowerSeries Finset

/-- The logarithm in OEIS A355257. -/
noncomputable def L : ℚ⟦X⟧ := logOf ((1 - X) * (1 - 2 * X)⁻¹)

/-- The factorial-scaled coefficient in OEIS A355257. -/
noncomputable def A (n k : ℕ) : ℚ :=
  (k.factorial : ℚ) * coeff k (L * ((1 - X) ^ n)⁻¹)

private theorem log_derivative (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    PowerSeries.derivative (R := ℚ) (logOf f) * f = PowerSeries.derivative (R := ℚ) f := by
  have hs : HasSubst (f - 1) := .of_constantCoeff_zero (by
    change constantCoeff (f - 1) = 0
    simp [hf])
  have h := congrArg (subst (f - 1)) (derivative_log_mul_one_add_X (A := ℚ))
  have hm : (PowerSeries.derivative (R := ℚ) (log ℚ)).subst (f - 1) * f = 1 := by
    simpa [subst_mul hs, subst_add hs, subst_X hs, ← coe_substAlgHom hs] using h
  rw [logOf_eq, derivative_subst hs]
  simp only [map_sub, derivative_one, sub_zero]
  calc
    _ = ((PowerSeries.derivative (R := ℚ) (log ℚ)).subst (f - 1) * f) *
        PowerSeries.derivative (R := ℚ) f := by ring
    _ = _ := by rw [hm, one_mul]

private theorem log_mul (f g : PowerSeries ℚ) (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) : logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
  apply PowerSeries.derivative.ext
  · have hu : IsUnit (f * g) := by
      rw [isUnit_iff_constantCoeff, hfg]
      exact isUnit_one
    apply hu.mul_right_cancel
    rw [map_add, log_derivative _ hfg]
    have h1 := log_derivative f hf
    have h2 := log_derivative g hg
    calc
      PowerSeries.derivative (R := ℚ) (f * g) =
          PowerSeries.derivative (R := ℚ) f * g + f * PowerSeries.derivative (R := ℚ) g := by
        rw [Derivation.leibniz]; ring
      _ = (PowerSeries.derivative (R := ℚ) (logOf f) +
          PowerSeries.derivative (R := ℚ) (logOf g)) * (f * g) := by
        rw [← h1, ← h2]; ring
  · simp [constantCoeff_logOf, hf, hg, hfg]

private theorem log_inv (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    logOf f⁻¹ = - logOf f := by
  have hi : constantCoeff f⁻¹ = 1 := by simp [constantCoeff_inv, hf]
  have h := log_mul f f⁻¹ hf hi
  rw [PowerSeries.mul_inv_cancel f (by rw [hf]; norm_num)] at h
  have hzero : logOf (1 : PowerSeries ℚ) = 0 := by
    rw [logOf_eq, sub_self, subst_zero_of_constantCoeff_zero constantCoeff_log]
  rw [hzero] at h
  calc
    logOf f⁻¹ = (logOf f + logOf f⁻¹) - logOf f := by ring
    _ = -logOf f := by rw [← h]; ring

private theorem coeff_log_linear (a : ℚ) (k : ℕ) :
    coeff k (logOf (1 - C a * X)) = -(a ^ k) / k := by
  rw [logOf_eq, show (1 - C a * X : PowerSeries ℚ) - 1 = C (-a) * X by simp]
  rw [← smul_eq_C_mul, ← rescale_eq_subst, coeff_rescale, coeff_log]
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    change (-a)^k * ((-1 : ℚ)^(k+1) / (k : ℚ)) = -(a^k) / k
    rw [neg_pow]
    have hp : (-1 : ℚ)^k * (-1 : ℚ)^(k+1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℚ)^k * (-1 : ℚ)^(k+1)) * a^k / k := by ring
      _ = _ := by rw [hp]; ring

private theorem coeff_L (k : ℕ) : coeff k L = ((2 : ℚ)^k - 1) / k := by
  have h1 : constantCoeff (1 - X : PowerSeries ℚ) = 1 := by simp
  have h2 : constantCoeff (1 - 2 * X : PowerSeries ℚ) = 1 := by simp
  rw [L, log_mul _ _ h1 (by simp [constantCoeff_inv, h2]), log_inv _ h2]
  simp only [map_add, map_neg]
  have htwo : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  rw [show (1 - X : PowerSeries ℚ) = 1 - C (1 : ℚ) * X by simp,
    htwo, coeff_log_linear, coeff_log_linear]
  simp only [one_pow]
  ring


private theorem inverse_coeff (n k : ℕ) :
    coeff k (((1 - X : PowerSeries ℚ)^n)⁻¹) = ((coeff k (invOneSubPow ℤ n).val : ℤ) : ℚ) := by
  have hprod : (PowerSeries.map (Int.castRingHom ℚ) (invOneSubPow ℤ n).val) *
      (1 - X : PowerSeries ℚ)^n = 1 := by
    have h : (invOneSubPow ℤ n).val * (1 - X : PowerSeries ℤ)^n = 1 := by
      rw [← invOneSubPow_inv_eq_one_sub_pow]
      exact (invOneSubPow ℤ n).val_inv
    have hh := congrArg (PowerSeries.map (Int.castRingHom ℚ)) h
    simpa only [map_mul, map_pow, map_sub, map_one, map_X] using hh
  have heq : (PowerSeries.map (Int.castRingHom ℚ) (invOneSubPow ℤ n).val) =
      ((1 - X : PowerSeries ℚ)^n)⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr hprod
  rw [← heq, coeff_map]
  rfl

private theorem B_zero (n : ℕ) : coeff 0 (invOneSubPow ℤ n).val = 1 := by
  cases n with
  | zero => simp [invOneSubPow_zero]
  | succ n => simp [invOneSubPow_val_succ_eq_mk_add_choose]

private theorem B_one (n : ℕ) : coeff 1 (invOneSubPow ℤ n).val = n := by
  cases n with
  | zero => simp [invOneSubPow_zero]
  | succ n => simp [invOneSubPow_val_succ_eq_mk_add_choose, Nat.choose_succ_self_right]

noncomputable def T (n k j : ℕ) : ℤ :=
  (k.factorial / j : ℕ) * ((2 : ℤ)^j - 1) * coeff (k - j) (invOneSubPow ℤ n).val
noncomputable def Z (n k : ℕ) : ℤ := ∑ j ∈ range (k+1), T n k j

theorem A_eq_Z (n k : ℕ) : A n k = (Z n k : ℚ) := by
  rw [A, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_L, inverse_coeff, Z, Int.cast_sum, mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases hz : j = 0
  · simp [T, hz]
  · have hd : j ∣ k.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (by simpa using hj)
    simp only [T, Int.cast_mul, Int.cast_natCast,
      Nat.cast_div_charZero hd, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one]
    ring





open Finset

private theorem quotient_multiple (k j d : ℕ) (hj : 0 < j) (hjk : j ≤ k)
    (hd : d * j ∣ k.factorial) : d ∣ k.factorial / j := by
  exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_factorial hj hjk)).mpr (by simpa [mul_comm] using hd)

private theorem T_multiple (n k j d : ℕ) (hd : d ∣ k.factorial / j) :
    (d : ℤ) ∣ T n k j := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact_mod_cast hd

private theorem T_self (n k : ℕ) (hk : 0 < k) :
    T n k k = ((k-1).factorial : ℤ) * ((2 : ℤ)^k - 1) := by
  simp only [T, Nat.sub_self, B_zero, mul_one]
  congr 2
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hk), Nat.mul_div_right _ hk]

private theorem T_lower (n k j : ℕ) (hk : 0 < k) (hj : j < k) :
    (k : ℤ) ∣ T n k j := by
  by_cases hz : j = 0
  · simp [T, hz]
  · apply T_multiple
    apply quotient_multiple _ _ _ (Nat.pos_of_ne_zero hz) hj.le
    have hd := Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (show j ≤ k-1 by omega)
    simpa only [Nat.mul_factorial_pred (Nat.ne_of_gt hk)] using Nat.mul_dvd_mul_left k hd

private theorem reduction (n k : ℕ) (hk : 0 < k) :
    Z n k ≡ ((k-1).factorial : ℤ) * ((2 : ℤ)^k - 1) [ZMOD k] := by
  have hd : (k : ℤ) ∣ ∑ j ∈ range k, T n k j := by
    apply Finset.dvd_sum
    intro j hj
    exact T_lower n k j hk (mem_range.mp hj)
  unfold Z
  rw [sum_range_succ, T_self n k hk]
  simpa using hd.modEq_zero_int.add (Int.ModEq.refl
    (((k-1).factorial : ℤ) * ((2 : ℤ)^k - 1)))

theorem prime_residue (n p : ℕ) (hp : p.Prime) : Z n p ≡ -1 [ZMOD p] := by
  apply (reduction n p hp.pos).trans
  rw [← ZMod.intCast_eq_intCast_iff]
  let : Fact p.Prime := ⟨hp⟩
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_pow,
    Int.cast_ofNat, Int.cast_one, Int.cast_neg]
  rw [ZMod.wilsons_lemma p, ZMod.pow_card]
  ring

private theorem composite_factorial (k : ℕ) (hk : 1 < k) (h4 : k ≠ 4)
    (hnp : ¬k.Prime) : k ∣ (k-1).factorial := by
  rcases Nat.even_or_odd k with he | ho
  · have h2 : k ≠ 2 := by intro h; subst k; exact hnp Nat.prime_two
    have hk6 : 6 ≤ k := by
      have := he.two_dvd
      omega
    have hdiv : 2 * (k/2) = k := Nat.mul_div_cancel' he.two_dvd
    have hsum : 2 + k/2 ≤ k-1 := by omega
    rw [← hdiv]
    apply dvd_trans (Nat.mul_dvd_mul (show 2 ∣ (2:ℕ).factorial by norm_num)
      (Nat.dvd_factorial (by omega : 0 < k/2) le_rfl))
    exact (Nat.factorial_mul_factorial_dvd_factorial_add 2 (k/2)).trans
      (Nat.factorial_dvd_factorial (by omega))
  · have hkeq : k-1+1 = k := by omega
    have hf := D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime
      (n := k-1) (by omega) (by simpa [hkeq] using fun h : k.Prime ∧ Odd k => hnp h.1)
    apply dvd_trans _ hf
    rw [hkeq, mul_comm, Nat.mul_div_assoc _ (by
      have := Nat.Odd.sub_odd ho (show Odd (1:ℕ) by decide)
      exact this.two_dvd)]
    exact dvd_mul_right k ((k-1)/2)

private theorem composite_divides (n k : ℕ) (hk : 1 ≤ k) (h4 : k ≠ 4)
    (hnp : ¬k.Prime) : (k : ℤ) ∣ Z n k := by
  by_cases h1 : k = 1
  · simp [h1]
  · have hf : k ∣ (k-1).factorial := composite_factorial k (by omega) h4 hnp
    have hzero : ((k-1).factorial : ℤ) * ((2 : ℤ)^k-1) ≡ 0 [ZMOD k] := by
      apply Int.modEq_zero_iff_dvd.mpr
      apply dvd_mul_of_dvd_left
      exact_mod_cast hf
    exact Int.modEq_zero_iff_dvd.mp ((reduction n k (by omega)).trans hzero)

private theorem divides_iff (n k : ℕ) (hk : 1 ≤ k) (h4 : k ≠ 4) :
    (k : ℤ) ∣ Z n k ↔ ¬ k.Prime := by
  constructor
  · intro hd hp
    have hm := (prime_residue n k hp).symm.trans hd.modEq_zero_int
    have hdone : (k : ℤ) ∣ (-1 : ℤ) := Int.modEq_zero_iff_dvd.mp hm
    have : k ∣ 1 := by exact_mod_cast (dvd_neg.mp hdone)
    have := Nat.dvd_one.mp this
    exact hp.ne_one this
  · exact composite_divides n k hk h4

private theorem lower_pred_multiple (p j : ℕ) (hp : 2 ≤ p) (hj : 0 < j) (hjl : j < p-1) :
    p-1 ∣ p.factorial / j := by
  apply quotient_multiple _ _ _ hj (by omega)
  have hd : j ∣ (p-2).factorial := Nat.dvd_factorial hj (by omega)
  have hf : p.factorial = p * (p-1) * (p-2).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : p ≠ 0),
      ← Nat.mul_factorial_pred (by omega : p-1 ≠ 0)]
    simp only [Nat.sub_sub]
    ring
  rw [hf]
  exact dvd_trans (Nat.mul_dvd_mul_left (p-1) hd) (by
    refine ⟨p, ?_⟩
    ring)

private theorem T_pred (n p : ℕ) (hp : 2 ≤ p) :
    T n p (p-1) = (p : ℤ) * ((p-2).factorial : ℤ) *
      ((2 : ℤ)^(p-1) - 1) * n := by
  have hf : p.factorial = p * (p-1) * (p-2).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : p ≠ 0),
      ← Nat.mul_factorial_pred (by omega : p-1 ≠ 0)]
    simp only [Nat.sub_sub]
    ring
  have hq : p.factorial / (p-1) = p * (p-2).factorial := by
    rw [hf, show p * (p-1) * (p-2).factorial = (p-1) * (p * (p-2).factorial) by ring,
      Nat.mul_div_right _ (by omega : 0 < p-1)]
  simp only [T, hq, show p-(p-1) = 1 by omega, B_one, Nat.cast_mul]

private theorem pred_reduction (n p : ℕ) (hp : 2 ≤ p) :
    Z n p ≡ (p : ℤ) * ((p-2).factorial : ℤ) * ((2 : ℤ)^(p-1)-1) * n [ZMOD p-1] := by
  have hd : ((p:ℤ)-1) ∣ ∑ j ∈ range (p-1), T n p j := by
    apply Finset.dvd_sum
    intro j hj
    by_cases hz : j = 0
    · simp [T, hz]
    · have h := T_multiple n p j (p-1) (lower_pred_multiple p j hp (Nat.pos_of_ne_zero hz) (mem_range.mp hj))
      simpa [Nat.cast_sub (by omega : 1 ≤ p)] using h
  have ht : ((p:ℤ)-1) ∣ T n p p := by
    rw [T_self n p (by omega)]
    apply dvd_mul_of_dvd_left
    have : p-1 ∣ (p-1).factorial := Nat.dvd_factorial (by omega) le_rfl
    have hi : ((p-1 : ℕ) : ℤ) ∣ ((p-1).factorial : ℤ) := by exact_mod_cast this
    simpa only [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using hi
  have hp1 : p-1+1 = p := by omega
  unfold Z
  rw [sum_range_succ, ← hp1, sum_range_succ, hp1, T_pred n p hp]
  simpa using (hd.modEq_zero_int.add (Int.ModEq.refl
    ((p : ℤ) * ((p-2).factorial : ℤ) * ((2 : ℤ)^(p-1)-1) * n))).add ht.modEq_zero_int

theorem even_pred_divides (n p : ℕ) (hp : p.Prime) (hn : Even n) :
    ((p : ℤ)-1) ∣ Z n p := by
  have hmod := pred_reduction n p hp.two_le
  apply Int.modEq_zero_iff_dvd.mp
  apply hmod.trans
  apply Int.modEq_zero_iff_dvd.mpr
  by_cases h2 : p = 2
  · simp [h2]
  by_cases h3 : p = 3
  · subst p
    rcases hn with ⟨m, rfl⟩
    norm_num [Nat.factorial]
    exact ⟨9*m, by ring⟩
  by_cases h5 : p = 5
  · subst p
    rcases hn with ⟨m, rfl⟩
    norm_num [Nat.factorial]
    exact ⟨225*m, by ring⟩
  · have hp7 : 7 ≤ p := by
      have ht := hp.two_le
      rcases hp.odd_of_ne_two h2 with ⟨t, ht2⟩
      omega
    have hc : ¬(p-1).Prime := by
      have he := hp.even_sub_one h2
      intro hprime
      have hh := hprime.even_iff.mp he
      omega
    have hf := composite_factorial (p-1) (by omega) (by omega) hc
    have hf' : p-1 ∣ (p-2).factorial := by simpa [Nat.sub_sub] using hf
    have hfz : ((p:ℤ)-1) ∣ ((p-2).factorial : ℤ) := by
      have hi : ((p-1 : ℕ) : ℤ) ∣ ((p-2).factorial : ℤ) := by exact_mod_cast hf'
      simpa only [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using hi
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hfz _) _) _


/-- OEIS A355257, COMMENTS: "Conjecture: Let n >= 0, k >= 1 and k != 4. Then k divides A(n, k) if and only if k is not prime." -/
def claim : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≠ 4 → ∃ z : ℤ, (z : ℚ) = A n k ∧ ((k : ℤ) ∣ z ↔ ¬ k.Prime)

theorem result : claim := by
  intro n k hk h4
  exact ⟨Z n k, (A_eq_Z n k).symm, divides_iff n k hk h4⟩

end D5.S3.Arith.Congruence.TebniA355257Divisibility
