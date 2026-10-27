/- GID: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dold congruences imply integral formal exponential coefficients. -/

/-
proof_shape: content (IsRIntegralPS.dieudonneDwork_mpr,
local_exp_of_log_difference, integral_exp_of_dold); bind-only (all other lemmas).
escape_witness: IsRIntegralPS.dieudonneDwork_mpr.
admission_basis: escape-witness.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19891
Direct frozen dependencies: LinearExponentDyadicSupport.pow_change;
ParametricExponentialSquareCongruence.linear_ode_unique;
CubicFifteenSubstitutionParity.prime_power_subst;
HannaLogarithmicPowerClosure.IntegralSeries.
The coefficient induction in dieudonneDwork_mpr proves local integrality.
expSeries_nsmul is used by HannaSigmaProductExpModThree.B_eq_cube.
All remaining lemmas are used in the proof of integral_exp_of_dold.
utility: none; all indices are arbitrary and no finite certificate is used.

The rational local-integrality and Dieudonné–Dwork arguments are adapted from
CBirkbeck/AINTLIB, commit 1e63feb21e2dd9e54908d14c9c07058eff3ff1d4,
under Apache-2.0. Attribution and full license: Library/RecurrenceComposition/
aintlib2026dieudonnedwork.md. The port uses the current PowerSeries API and
replaces coefficient and uniqueness arguments with their existing D5 owners.
Retirement condition: the pinned Mathlib contains equivalent local-integrality
and exponential-integrality theorems; use those declarations directly then.

Declaration classification (names relative to this module):
declaration | proof_shape | escape_witness | direct consumers
IsRIntegralRat | bind-only | none | IsRIntegralPS, IsRIntegralPS.dieudonneDwork_mpr, IsRIntegralPS.dieudonneDwork_mpr._simp_1_1, IsRIntegralPS.mul, IsRIntegralPS.one, IsRIntegralPS.one._simp_1_1, IsRIntegralPS.one._simp_1_2, IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.sub, IsRIntegralPS.subst_X_pow, IsRIntegralPS.subst_X_pow._simp_1_1, IsRIntegralPS.toZModPS_mul, IsRIntegralPS.toZModPS_one, IsRIntegralPS.toZModPS_sub, IsRIntegralRat.add, IsRIntegralRat.den_mul_toZMod, IsRIntegralRat.eq_1, IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero, IsRIntegralRat.isUnit_den_zmod, IsRIntegralRat.mul, IsRIntegralRat.neg, IsRIntegralRat.sub, IsRIntegralRat.sum, IsRIntegralRat.toZMod, IsRIntegralRat.toZMod.congr_simp, IsRIntegralRat.toZMod.eq_1, IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_eq_of_den_mul_eq, IsRIntegralRat.toZMod_finset_sum, IsRIntegralRat.toZMod_mul, IsRIntegralRat.toZMod_neg, IsRIntegralRat.toZMod_sub, IsRMultipleIntegralPS, IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt, exp_multiple, integral_exp_of_dold, localRat_iff_val_nonneg, local_exp_of_log_difference, local_int_div_nat
IsRIntegralRat.zero | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr._simp_1_1, IsRIntegralPS.one._simp_1_2, IsRIntegralPS.subst_X_pow._simp_1_1, IsRIntegralRat.sum, IsRIntegralRat.toZMod_zero, IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt, exp_multiple, integral_exp_of_dold, local_int_div_nat
IsRIntegralRat.one | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr, IsRIntegralPS.one._simp_1_1, IsRIntegralRat.toZMod_one
IsRIntegralRat.add | bind-only | none | IsRIntegralRat.sub, IsRIntegralRat.sum, IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_finset_sum, IsRIntegralRat.toZMod_sub
IsRIntegralRat.neg | bind-only | none | IsRIntegralRat.sub, IsRIntegralRat.toZMod_neg, IsRIntegralRat.toZMod_sub
IsRIntegralRat.sub | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr, IsRIntegralPS.sub, IsRIntegralRat.toZMod_sub
IsRIntegralRat.mul | bind-only | none | IsRIntegralPS.mul, IsRIntegralPS.toZModPS_mul, IsRIntegralRat.toZMod_mul, IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt, exp_multiple
IsRIntegralRat.sum | bind-only | none | IsRIntegralPS.mul, IsRIntegralRat.toZMod_finset_sum, IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt, exp_multiple
IsRIntegralRat.toZMod | bind-only | none | IsRIntegralPS.coeff_toZModPS, IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.toZModPS, IsRIntegralPS.toZModPS_mul, IsRIntegralPS.toZModPS_one, IsRIntegralPS.toZModPS_sub, IsRIntegralPS.toZModPS_subst_X_pow, IsRIntegralRat.den_mul_toZMod, IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero, IsRIntegralRat.toZMod.congr_simp, IsRIntegralRat.toZMod.eq_1, IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_eq_of_den_mul_eq, IsRIntegralRat.toZMod_finset_sum, IsRIntegralRat.toZMod_mul, IsRIntegralRat.toZMod_neg, IsRIntegralRat.toZMod_one, IsRIntegralRat.toZMod_sub, IsRIntegralRat.toZMod_zero
IsRIntegralRat.toZMod_zero | bind-only | none | IsRIntegralPS.toZModPS_one
IsRIntegralRat.toZMod_one | bind-only | none | IsRIntegralPS.toZModPS_one
IsRIntegralRat.isUnit_den_zmod | bind-only | none | IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_eq_of_den_mul_eq, IsRIntegralRat.toZMod_mul
IsRIntegralRat.den_mul_toZMod | bind-only | none | IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero, IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_eq_of_den_mul_eq, IsRIntegralRat.toZMod_mul
IsRIntegralRat.toZMod_eq_of_den_mul_eq | bind-only | none | IsRIntegralRat.toZMod_add, IsRIntegralRat.toZMod_mul
IsRIntegralRat.toZMod_add | bind-only | none | IsRIntegralRat.toZMod_finset_sum, IsRIntegralRat.toZMod_sub
IsRIntegralRat.toZMod_neg | bind-only | none | IsRIntegralRat.toZMod_sub
IsRIntegralRat.toZMod_sub | bind-only | none | IsRIntegralPS.toZModPS_sub
IsRIntegralRat.toZMod_mul | bind-only | none | IsRIntegralPS.toZModPS_mul
IsRIntegralRat.toZMod_finset_sum | bind-only | none | IsRIntegralPS.toZModPS_mul
IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
powerSeries_expand_zmod | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
IsRIntegralPS | bind-only | none | IsRIntegralPS.coeff_toZModPS, IsRIntegralPS.dieudonneDwork_mpr, IsRIntegralPS.mul, IsRIntegralPS.pow, IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.sub, IsRIntegralPS.subst_X_pow, IsRIntegralPS.toZModPS, IsRIntegralPS.toZModPS.congr_simp, IsRIntegralPS.toZModPS.eq_1, IsRIntegralPS.toZModPS_congr_proof, IsRIntegralPS.toZModPS_eq_of_eq, IsRIntegralPS.toZModPS_mul, IsRIntegralPS.toZModPS_pow, IsRIntegralPS.toZModPS_sub, IsRIntegralPS.toZModPS_subst_X_pow, exp_multiple, integral_of_local, local_exp_of_log_difference
IsRIntegralPS.one | bind-only | none | IsRIntegralPS.pow, IsRIntegralPS.toZModPS_one, IsRIntegralPS.toZModPS_pow
IsRIntegralPS.sub | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.toZModPS_sub
IsRIntegralPS.mul | bind-only | none | IsRIntegralPS.pow, IsRIntegralPS.toZModPS_mul, IsRIntegralPS.toZModPS_pow
IsRIntegralPS.pow | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.toZModPS_pow, exp_multiple
IsRIntegralPS.subst_X_pow | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.toZModPS_subst_X_pow
IsRMultipleIntegralPS | bind-only | none | none
IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr
IsRIntegralPS.toZModPS | bind-only | none | IsRIntegralPS.coeff_toZModPS, IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul, IsRIntegralPS.toZModPS.congr_simp, IsRIntegralPS.toZModPS.eq_1, IsRIntegralPS.toZModPS_congr_proof, IsRIntegralPS.toZModPS_eq_of_eq, IsRIntegralPS.toZModPS_mul, IsRIntegralPS.toZModPS_one, IsRIntegralPS.toZModPS_pow, IsRIntegralPS.toZModPS_sub, IsRIntegralPS.toZModPS_subst_X_pow
IsRIntegralPS.coeff_toZModPS | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
IsRIntegralPS.toZModPS_congr_proof | bind-only | none | IsRIntegralPS.toZModPS_eq_of_eq, IsRIntegralPS.toZModPS_pow
IsRIntegralPS.toZModPS_eq_of_eq | bind-only | none | IsRIntegralPS.toZModPS_pow
IsRIntegralPS.toZModPS_one | bind-only | none | IsRIntegralPS.toZModPS_pow
IsRIntegralPS.toZModPS_sub | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
IsRIntegralPS.toZModPS_mul | bind-only | none | IsRIntegralPS.toZModPS_pow
IsRIntegralPS.toZModPS_pow | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
IsRIntegralPS.toZModPS_subst_X_pow | bind-only | none | IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul
IsRIntegralPS.pow_r_sub_subst_X_pow_r_in_r_smul | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr
IsRIntegralPS.coeff_pow_eq_trunc_add | bind-only | none | IsRIntegralPS.dieudonneDwork_mpr
IsRIntegralPS.dieudonneDwork_mpr | content | D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralPS.dieudonneDwork_mpr | local_exp_of_log_difference
localRat_iff_val_nonneg | bind-only | none | exp_multiple, local_int_div_nat
integral_of_local | bind-only | none | integral_exp_of_dold
expSeries_coeff | bind-only | none | exp_multiple
expSeries_constant | bind-only | none | expSeries_add, expSeries_neg, exp_multiple, local_exp_of_log_difference
expSeries_derivative | bind-only | none | expSeries_add
first_order_unique | bind-only | none | expSeries_add
expSeries_add | bind-only | none | expSeries_neg, local_exp_of_log_difference
expSeries_nsmul | bind-only | none | local_exp_of_log_difference, D5.S3.Arith.Robin.HannaSigmaProductExpModThree.B_eq_cube
expSeries_neg | bind-only | none | local_exp_of_log_difference
expSeries_subst | bind-only | none | local_exp_of_log_difference
exp_multiple | bind-only | none | local_exp_of_log_difference
local_exp_of_log_difference | content | D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralPS.dieudonneDwork_mpr | integral_exp_of_dold
local_int_div_nat | bind-only | none | integral_exp_of_dold
Dold | bind-only | none | integral_exp_of_dold, D5.S3.Arith.Robin.HannaSigmaProductExpModThree.Arithmetic.dold_mul, D5.S3.Arith.Robin.HannaSigmaProductExpModThree.Arithmetic.dold_scale
logInput | bind-only | none | integral_exp_of_dold, logInput.eq_1, logInput_zero, D5.S3.Arith.Robin.HannaSigmaProductExpModThree.AIntegral
logInput_zero | bind-only | none | integral_exp_of_dold
integral_exp_of_dold | content | D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralPS.dieudonneDwork_mpr | D5.S3.Arith.Robin.HannaSigmaProductExpModThree.AIntegral
-/

import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

noncomputable section

namespace D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

private def IsRIntegralRat (r : ℕ) (q : ℚ) : Prop := (q.den : ℕ).Coprime r

private theorem IsRIntegralRat.zero (r : ℕ) : IsRIntegralRat r 0 := by
  simp [IsRIntegralRat]

private theorem IsRIntegralRat.one (r : ℕ) : IsRIntegralRat r 1 := by
  simp [IsRIntegralRat]

private theorem IsRIntegralRat.add {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ + q₂) := by
  simp only [IsRIntegralRat] at h₁ h₂ ⊢
  exact (h₁.mul_left h₂).coprime_dvd_left (Rat.add_den_dvd q₁ q₂)

private theorem IsRIntegralRat.neg {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q) :
    IsRIntegralRat r (-q) := by
  simp only [IsRIntegralRat] at h ⊢
  rwa [Rat.neg_den]

private theorem IsRIntegralRat.sub {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

private theorem IsRIntegralRat.mul {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ * q₂) := by
  simp only [IsRIntegralRat] at h₁ h₂ ⊢
  exact (h₁.mul_left h₂).coprime_dvd_left (Rat.mul_den_dvd q₁ q₂)

private theorem IsRIntegralRat.sum {r : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (hf : ∀ i ∈ s, IsRIntegralRat r (f i)) : IsRIntegralRat r (∑ i ∈ s, f i) :=
  Finset.sum_induction f _ (fun _ _ => IsRIntegralRat.add) (IsRIntegralRat.zero r) hf

namespace IsRIntegralRat

private noncomputable def toZMod {r : ℕ} (q : ℚ) (_h : IsRIntegralRat r q) : ZMod r :=
  (q.num : ZMod r) * (q.den : ZMod r)⁻¹

@[simp]
private theorem toZMod_zero (r : ℕ) : toZMod (r := r) 0 (IsRIntegralRat.zero r) = 0 := by
  simp [toZMod]

@[simp]
private theorem toZMod_one (r : ℕ) : toZMod (r := r) 1 (IsRIntegralRat.one r) = 1 := by
  simp [toZMod]

private theorem isUnit_den_zmod {r : ℕ} (q : ℚ) (h : IsRIntegralRat r q) :
    IsUnit (q.den : ZMod r) :=
  (ZMod.isUnit_iff_coprime q.den r).mpr h

private theorem den_mul_toZMod {r : ℕ} (q : ℚ) (h : IsRIntegralRat r q) :
    (q.den : ZMod r) * toZMod q h = (q.num : ZMod r) := by
  simp only [toZMod]
  calc
    (q.den : ZMod r) * ((q.num : ZMod r) * (q.den : ZMod r)⁻¹)
        = (q.num : ZMod r) * ((q.den : ZMod r) * (q.den : ZMod r)⁻¹) := by ring
    _ = (q.num : ZMod r) := by rw [ZMod.coe_mul_inv_eq_one q.den h, mul_one]

private theorem toZMod_eq_of_den_mul_eq {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q)
    {x : ZMod r} (hx : (q.den : ZMod r) * x = (q.num : ZMod r)) :
    x = toZMod q h :=
  (isUnit_den_zmod q h).mul_left_cancel (by rw [hx, den_mul_toZMod])

private theorem toZMod_add {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ + q₂) (h₁.add h₂) = toZMod q₁ h₁ + toZMod q₂ h₂ := by
  let d₁ : ZMod r := q₁.den
  let d₂ : ZMod r := q₂.den
  let D : ZMod r := (q₁ + q₂).den
  let n₁ : ZMod r := q₁.num
  let n₂ : ZMod r := q₂.num
  let N : ZMod r := (q₁ + q₂).num
  let x₁ : ZMod r := toZMod q₁ h₁
  let x₂ : ZMod r := toZMod q₂ h₂
  have hden₁ : d₁ * x₁ = n₁ := by
    simpa [d₁, x₁, n₁] using den_mul_toZMod q₁ h₁
  have hden₂ : d₂ * x₂ = n₂ := by
    simpa [d₂, x₂, n₂] using den_mul_toZMod q₂ h₂
  have hcross : N * d₁ * d₂ = (n₁ * d₂ + n₂ * d₁) * D := by
    simpa [N, d₁, d₂, n₁, n₂, D, mul_assoc] using
      (congrArg (fun z : ℤ => (z : ZMod r)) (Rat.add_num_den' q₁ q₂))
  symm
  refine toZMod_eq_of_den_mul_eq (h₁.add h₂) ?_
  change D * (x₁ + x₂) = N
  have hunit : IsUnit (d₁ * d₂) := by
    simpa [d₁, d₂] using IsUnit.mul (isUnit_den_zmod q₁ h₁) (isUnit_den_zmod q₂ h₂)
  exact hunit.mul_left_cancel <| by
    calc
      (d₁ * d₂) * (D * (x₁ + x₂))
          = ((d₁ * x₁) * d₂ + (d₂ * x₂) * d₁) * D := by ring
      _ = (n₁ * d₂ + n₂ * d₁) * D := by rw [hden₁, hden₂]
      _ = N * (d₁ * d₂) := by rw [← hcross]; ring
      _ = (d₁ * d₂) * N := by ring

private theorem toZMod_neg {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q) :
    toZMod (-q) h.neg = -toZMod q h := by
  simp [toZMod]

private theorem toZMod_sub {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ - q₂) (h₁.sub h₂) = toZMod q₁ h₁ - toZMod q₂ h₂ := by
  simpa [sub_eq_add_neg, toZMod_neg h₂] using toZMod_add h₁ h₂.neg

private theorem toZMod_mul {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ * q₂) (h₁.mul h₂) = toZMod q₁ h₁ * toZMod q₂ h₂ := by
  let d₁ : ZMod r := q₁.den
  let d₂ : ZMod r := q₂.den
  let D : ZMod r := (q₁ * q₂).den
  let n₁ : ZMod r := q₁.num
  let n₂ : ZMod r := q₂.num
  let N : ZMod r := (q₁ * q₂).num
  let x₁ : ZMod r := toZMod q₁ h₁
  let x₂ : ZMod r := toZMod q₂ h₂
  have hden₁ : d₁ * x₁ = n₁ := by
    simpa [d₁, x₁, n₁] using den_mul_toZMod q₁ h₁
  have hden₂ : d₂ * x₂ = n₂ := by
    simpa [d₂, x₂, n₂] using den_mul_toZMod q₂ h₂
  have hcross : N * d₁ * d₂ = (n₁ * n₂) * D := by
    simpa [N, d₁, d₂, n₁, n₂, D, mul_assoc] using
      (congrArg (fun z : ℤ => (z : ZMod r)) (Rat.mul_num_den' q₁ q₂))
  symm
  refine toZMod_eq_of_den_mul_eq (h₁.mul h₂) ?_
  change D * (x₁ * x₂) = N
  have hunit : IsUnit (d₁ * d₂) := by
    simpa [d₁, d₂] using IsUnit.mul (isUnit_den_zmod q₁ h₁) (isUnit_den_zmod q₂ h₂)
  exact hunit.mul_left_cancel <| by
    calc
      (d₁ * d₂) * (D * (x₁ * x₂))
          = ((d₁ * x₁) * (d₂ * x₂)) * D := by ring
      _ = (n₁ * n₂) * D := by rw [hden₁, hden₂]
      _ = N * (d₁ * d₂) := by rw [← hcross]; ring
      _ = (d₁ * d₂) * N := by ring

private theorem toZMod_finset_sum {r : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, IsRIntegralRat r (f i))
    (hsum : IsRIntegralRat r (Finset.sum s f)) :
    toZMod (Finset.sum s f) hsum =
      Finset.sum s (fun i => ((f i).num : ZMod r) * ((f i).den : ZMod r)⁻¹) := by
  classical
  revert hf hsum
  refine Finset.induction_on s ?empty ?insert
  · intro _ _
    simp [toZMod]
  · intro a s ha ih hf hsum
    have hfa : IsRIntegralRat r (f a) := hf a (by simp [ha])
    have hfs : ∀ i ∈ s, IsRIntegralRat r (f i) := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hsum_s : IsRIntegralRat r (Finset.sum s f) := IsRIntegralRat.sum hfs
    calc
      toZMod (Finset.sum (insert a s) f) hsum
          = toZMod (f a + Finset.sum s f) (hfa.add hsum_s) := by
            simp [toZMod, Finset.sum_insert ha]
      _ = toZMod (f a) hfa + toZMod (Finset.sum s f) hsum_s := by
            rw [toZMod_add hfa hsum_s]
      _ = Finset.sum (insert a s)
          (fun i => ((f i).num : ZMod r) * ((f i).den : ZMod r)⁻¹) := by
            rw [ih hfs hsum_s, Finset.sum_insert ha]
            rfl

private theorem exists_eq_natCast_mul_of_toZMod_eq_zero {r : ℕ} {q : ℚ}
    (h : IsRIntegralRat r q) (hz : toZMod q h = 0) :
    ∃ q' : ℚ, IsRIntegralRat r q' ∧ q = (r : ℚ) * q' := by
  have hnum_zmod : (q.num : ZMod r) = 0 := by
    rw [← den_mul_toZMod q h, hz, mul_zero]
  have hnum_dvd : (r : ℤ) ∣ q.num := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd q.num r).mp hnum_zmod
  rcases hnum_dvd with ⟨k, hk⟩
  refine ⟨Rat.divInt k (q.den : ℤ), ?_, ?_⟩
  · unfold IsRIntegralRat
    refine Nat.Coprime.coprime_dvd_left ?_ h
    have hden_dvd_int : (((Rat.divInt k (q.den : ℤ)).den : ℕ) : ℤ) ∣ (q.den : ℤ) :=
      Rat.den_dvd k (q.den : ℤ)
    exact Int.natCast_dvd_natCast.mp hden_dvd_int
  · calc
      q = Rat.divInt q.num (q.den : ℤ) := (Rat.num_divInt_den q).symm
      _ = Rat.divInt ((r : ℤ) * k) (q.den : ℤ) := by rw [hk]
      _ = (r : ℚ) * Rat.divInt k (q.den : ℤ) := by
        rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
        push_cast
        ring

end IsRIntegralRat

private theorem powerSeries_expand_zmod {p : ℕ} [Fact p.Prime] (F : PowerSeries (ZMod p)) :
    PowerSeries.expand p ((Fact.out : Nat.Prime p).ne_zero) F = F ^ p := by
  exact (PowerSeries.expand_apply p (Fact.out : Nat.Prime p).ne_zero F).trans
    (D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst p F).symm

private def IsRIntegralPS (r : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) n) F)

private theorem IsRIntegralPS.one (r : ℕ) : IsRIntegralPS r 1 := fun n => by
  rw [PowerSeries.coeff_one]
  by_cases h : n = 0
  · simp [h, IsRIntegralRat.one]
  · simp [h, IsRIntegralRat.zero]

private theorem IsRIntegralPS.sub {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    IsRIntegralPS r (F - G) := fun n => by
  rw [map_sub]
  exact (hF n).sub (hG n)

private theorem IsRIntegralPS.mul {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    IsRIntegralPS r (F * G) := fun n => by
  rw [PowerSeries.coeff_mul]


  exact IsRIntegralRat.sum fun ⟨i, j⟩ _ => (hF i).mul (hG j)

private theorem IsRIntegralPS.pow {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (k : ℕ) : IsRIntegralPS r (F ^ k) := by
  induction k with
  | zero => simpa using IsRIntegralPS.one r
  | succ k ih => rw [pow_succ]; exact ih.mul hF

private theorem IsRIntegralPS.subst_X_pow {r k : ℕ} (hk : k ≠ 0) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    IsRIntegralPS r (PowerSeries.subst (PowerSeries.X ^ k) F) := fun n => by
  rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hk F n]
  by_cases hkn : k ∣ n
  · simp [hkn, hF (n / k)]
  · simp [hkn, IsRIntegralRat.zero]
private def IsRMultipleIntegralPS (r : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, IsRIntegralRat r q ∧
    (PowerSeries.coeff (R := ℚ) n) F = (r : ℚ) * q

namespace IsRMultipleIntegralPS

private theorem coeff_mul_left_multiple_pos_right_integral_lt {r n : ℕ} {F G : PowerSeries ℚ}
    (hF0 : (PowerSeries.coeff (R := ℚ) 0) F = 0)
    (hFpos : ∀ i : ℕ, 1 ≤ i →
      ∃ q : ℚ, IsRIntegralRat r q ∧
        (PowerSeries.coeff (R := ℚ) i) F = (r : ℚ) * q)
    (hGlt : ∀ j : ℕ, j < n →
      IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) j) G)) :
    ∃ q : ℚ, IsRIntegralRat r q ∧
      (PowerSeries.coeff (R := ℚ) n) (F * G) = (r : ℚ) * q := by
  classical
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal n
  let qTerm : ℕ × ℕ → ℚ := fun p =>
    if hp0 : p.1 = 0 then 0
    else
      (hFpos p.1 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0))).choose *
        (PowerSeries.coeff (R := ℚ) p.2) G
  refine ⟨Finset.sum s qTerm, ?_, ?_⟩
  · refine IsRIntegralRat.sum fun p hp => ?_
    by_cases hp0 : p.1 = 0
    · rw [dif_pos hp0]
      exact IsRIntegralRat.zero r
    · have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp0
      have hp2lt : p.2 < n := by
        have hsum : p.1 + p.2 = n := by
          exact List.Nat.mem_antidiagonal.mp hp
        rw [← hsum]
        exact Nat.lt_add_of_pos_left hp1pos
      rw [dif_neg hp0]
      exact ((hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose_spec.1).mul
        (hGlt p.2 hp2lt)
  · calc
      (PowerSeries.coeff (R := ℚ) n) (F * G)
          = Finset.sum s (fun p =>
              (PowerSeries.coeff (R := ℚ) p.1) F *
                (PowerSeries.coeff (R := ℚ) p.2) G) := by
            simp [s, PowerSeries.coeff_mul]
      _ = Finset.sum s (fun p => (r : ℚ) * qTerm p) := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hp0 : p.1 = 0
            · dsimp [qTerm]
              rw [dif_pos hp0]
              simp [hp0, hF0]
            · have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp0
              have hcoeff :=
                (hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose_spec.2
              dsimp [qTerm]
              rw [dif_neg hp0]
              calc
                (PowerSeries.coeff (R := ℚ) p.1) F *
                    (PowerSeries.coeff (R := ℚ) p.2) G
                    = ((r : ℚ) *
                        (hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose) *
                        (PowerSeries.coeff (R := ℚ) p.2) G :=
                      congrArg
                        (fun x : ℚ => x * (PowerSeries.coeff (R := ℚ) p.2) G)
                        hcoeff
                _ = (r : ℚ) *
                      ((hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose *
                        (PowerSeries.coeff (R := ℚ) p.2) G) := by
                      ring
      _ = (r : ℚ) * Finset.sum s qTerm := by
            rw [Finset.mul_sum]

end IsRMultipleIntegralPS

namespace IsRIntegralPS
private noncomputable def toZModPS {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F) :
    PowerSeries (ZMod r) :=
  PowerSeries.mk fun n =>
    IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) n) F) (hF n)

@[simp]
private theorem coeff_toZModPS {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (n : ℕ) :
    (PowerSeries.coeff (R := ZMod r) n) hF.toZModPS =
      IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) n) F) (hF n) := by
  simp [toZModPS]
end IsRIntegralPS
end D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

namespace D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

namespace IsRIntegralPS

private theorem toZModPS_congr_proof {r : ℕ} {F : PowerSeries ℚ}
    (hF hF' : IsRIntegralPS r F) : hF.toZModPS = hF'.toZModPS := by
  exact PowerSeries.ext (congrFun rfl)

private theorem toZModPS_eq_of_eq {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) (h : F = G) :
    hF.toZModPS = hG.toZModPS := by
  subst h
  exact toZModPS_congr_proof hF hG

@[simp]
private theorem toZModPS_one (r : ℕ) :
    (IsRIntegralPS.one r).toZModPS = (1 : PowerSeries (ZMod r)) := by
  ext n
  rcases eq_or_ne n 0 with hn | hn <;> simp [toZModPS, hn]

private theorem toZModPS_sub {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.sub hG).toZModPS = hF.toZModPS - hG.toZModPS := by
  ext n
  simpa [toZModPS, map_sub] using IsRIntegralRat.toZMod_sub (hF n) (hG n)

private theorem toZModPS_mul {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.mul hG).toZModPS = hF.toZModPS * hG.toZModPS := by
  classical
  ext n
  let f : ℕ × ℕ → ℚ := fun p =>
    ((PowerSeries.coeff (R := ℚ) p.1) F) *
      ((PowerSeries.coeff (R := ℚ) p.2) G)
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal n
  have hsum : IsRIntegralRat r (Finset.sum s f) := by
    simpa [s, f, PowerSeries.coeff_mul] using (hF.mul hG n)
  calc
    (PowerSeries.coeff (R := ZMod r) n) (hF.mul hG).toZModPS
        = IsRIntegralRat.toZMod (Finset.sum s f) hsum := by
          simp [toZModPS, IsRIntegralRat.toZMod, s, f, PowerSeries.coeff_mul]
    _ = Finset.sum s (fun p => ((f p).num : ZMod r) * ((f p).den : ZMod r)⁻¹) :=
          IsRIntegralRat.toZMod_finset_sum s f
            (fun p _ => (hF p.1).mul (hG p.2)) hsum
    _ = Finset.sum s (fun p =>
          IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) p.1) F) (hF p.1) *
            IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) p.2) G) (hG p.2)) := by
          apply Finset.sum_congr rfl
          intro p _
          simpa [f, IsRIntegralRat.toZMod] using
            IsRIntegralRat.toZMod_mul (hF p.1) (hG p.2)
    _ = (PowerSeries.coeff (R := ZMod r) n) (hF.toZModPS * hG.toZModPS) := by
          simp [s, toZModPS, PowerSeries.coeff_mul]

private theorem toZModPS_pow {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (k : ℕ) :
    (hF.pow k).toZModPS = hF.toZModPS ^ k := by
  induction k with
  | zero =>
      calc
        (hF.pow 0).toZModPS = (IsRIntegralPS.one r).toZModPS :=
          toZModPS_congr_proof _ _
        _ = 1 := toZModPS_one r
        _ = hF.toZModPS ^ 0 := by simp
  | succ k ih =>
      have hmul : IsRIntegralPS r (F ^ k * F) := (hF.pow k).mul hF
      calc
        (hF.pow (k + 1)).toZModPS
            = hmul.toZModPS :=
              toZModPS_eq_of_eq _ _ (by rw [pow_succ])
        _ = (hF.pow k).toZModPS * hF.toZModPS := toZModPS_mul (hF.pow k) hF
        _ = hF.toZModPS ^ (k + 1) := by rw [ih, pow_succ]

private theorem toZModPS_subst_X_pow {r k : ℕ} (hk : k ≠ 0) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    (hF.subst_X_pow hk).toZModPS =
      PowerSeries.subst (PowerSeries.X ^ k) hF.toZModPS := by
  ext n
  rcases em (k ∣ n) with hkn | hkn <;>
    simp [toZModPS, PowerSeries.coeff_subst_X_pow, hk, hkn, IsRIntegralRat.toZMod]

private theorem pow_r_sub_subst_X_pow_r_in_r_smul
    (r : ℕ) [Fact (Nat.Prime r)] {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (n : ℕ) :
    ∃ q : ℚ, IsRIntegralRat r q ∧
      (PowerSeries.coeff (R := ℚ) n)
        (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F) = (r : ℚ) * q := by
  let hr : r ≠ 0 := (Fact.out : Nat.Prime r).ne_zero
  let hSub : IsRIntegralPS r (PowerSeries.subst (PowerSeries.X ^ r) F) :=
    hF.subst_X_pow hr
  let hDiff : IsRIntegralPS r (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F) :=
    (hF.pow r).sub hSub
  have hfresh :
      PowerSeries.subst (PowerSeries.X ^ r) hF.toZModPS = hF.toZModPS ^ r := by
    rw [← PowerSeries.expand_apply (p := r) (hp := hr)]
    exact powerSeries_expand_zmod hF.toZModPS
  have hred : hDiff.toZModPS = 0 := by
    calc
      hDiff.toZModPS
          = (hF.pow r).toZModPS - hSub.toZModPS := toZModPS_sub (hF.pow r) hSub
      _ = hF.toZModPS ^ r -
            PowerSeries.subst (PowerSeries.X ^ r) hF.toZModPS := by
              rw [toZModPS_pow hF r, toZModPS_subst_X_pow hr hF]
      _ = 0 := by rw [hfresh, sub_self]
  have hz :
      IsRIntegralRat.toZMod
        ((PowerSeries.coeff (R := ℚ) n)
          (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F))
        (hDiff n) = 0 := by
    have hc := congrArg ((PowerSeries.coeff (R := ZMod r) n)) hred
    simpa [hDiff] using hc
  exact IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero (hDiff n) hz

private theorem coeff_pow_eq_trunc_add
    {F : PowerSeries ℚ} {n k : ℕ} (hn : 0 < n)
    (hF0 : PowerSeries.constantCoeff F = 1) :
    (PowerSeries.coeff (R := ℚ) n) (F ^ k) =
      (PowerSeries.coeff (R := ℚ) n)
        (((PowerSeries.trunc n F : Polynomial ℚ) : PowerSeries ℚ) ^ k) +
        (k : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
  let A : PowerSeries ℚ := ((PowerSeries.trunc n F : Polynomial ℚ) : PowerSeries ℚ)
  have hA0 : PowerSeries.constantCoeff A = 1 := by
    simp [A, PowerSeries.coeff_trunc, hn, hF0]
  have hc : PowerSeries.coeff n (F ^ k) - PowerSeries.coeff n (A ^ k) =
      (k : ℚ) * (PowerSeries.coeff n F - PowerSeries.coeff n A) := by
    apply D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.pow_change hF0 hA0
    intro j hj
    simp [A, PowerSeries.coeff_trunc, hj]
  have hAn : PowerSeries.coeff n A = 0 := by simp [A, PowerSeries.coeff_trunc]
  rw [hAn, sub_zero] at hc
  change PowerSeries.coeff n (F ^ k) = PowerSeries.coeff n (A ^ k) + _
  linear_combination hc

private theorem dieudonneDwork_mpr
    (r : ℕ) [Fact (Nat.Prime r)] {F : PowerSeries ℚ}
    (hF1 : PowerSeries.constantCoeff F = 1)
    (hQuotient : ∀ n : ℕ, 1 ≤ n →
      ∃ q : ℚ, IsRIntegralRat r q ∧
        (PowerSeries.coeff (R := ℚ) n)
          (F ^ r * (PowerSeries.subst (PowerSeries.X ^ r) F)⁻¹ - 1) =
            (r : ℚ) * q) :
    IsRIntegralPS r F := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0, PowerSeries.coeff_zero_eq_constantCoeff, hF1] using
          IsRIntegralRat.one r
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        let hr : r ≠ 0 := (Fact.out : Nat.Prime r).ne_zero
        let SF : PowerSeries ℚ := PowerSeries.subst (PowerSeries.X ^ r) F
        let Q : PowerSeries ℚ := F ^ r * SF⁻¹ - 1
        have hS0 : PowerSeries.constantCoeff SF = 1 := by
          show PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.X ^ r) F) = 1
          rw [PowerSeries.constantCoeff_subst_X_pow hr, hF1, map_one]
        have hQ0 : (PowerSeries.coeff (R := ℚ) 0) Q = 0 := by
          simp [Q, SF, hF1, hS0]
        have hQpos :
            ∀ i : ℕ, 1 ≤ i →
              ∃ q : ℚ, IsRIntegralRat r q ∧
                (PowerSeries.coeff (R := ℚ) i) Q = (r : ℚ) * q := by
          intro i hi
          simpa [Q, SF] using hQuotient i hi
        have hS_lower :
            ∀ j : ℕ, j < n →
              IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) j) SF) := by
          intro j hj
          change IsRIntegralRat r
            ((PowerSeries.coeff (R := ℚ) j)
              (PowerSeries.subst (PowerSeries.X ^ r) F))
          rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr F j]
          by_cases hdiv : r ∣ j
          · have hjdiv : j / r < n :=
              lt_of_le_of_lt (Nat.div_le_self j r) hj
            simpa [hdiv] using ih (j / r) hjdiv
          · simp [hdiv, IsRIntegralRat.zero]
        have hQS : Q * SF = F ^ r - SF := by
          calc
            Q * SF = (F ^ r * SF⁻¹ - 1) * SF := rfl
            _ = F ^ r * (SF⁻¹ * SF) - SF := by ring
            _ = F ^ r - SF := by
              rw [PowerSeries.inv_mul_cancel SF (by simp [hS0])]
              ring
        rcases IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt
            hQ0 hQpos hS_lower with ⟨qD, hqD, hqDcoeffQS⟩
        have hqDcoeff :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) = (r : ℚ) * qD := by
          simpa [hQS] using hqDcoeffQS
        let A : PowerSeries ℚ := ((PowerSeries.trunc n F : Polynomial ℚ) : PowerSeries ℚ)
        have hA_integral : IsRIntegralPS r A := by
          intro m
          by_cases hm : m < n
          · simpa [A, PowerSeries.coeff_trunc, hm] using ih m hm
          · simp [A, PowerSeries.coeff_trunc, hm, IsRIntegralRat.zero]
        have hSubstA :
            (PowerSeries.coeff (R := ℚ) n) SF =
              (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) A) := by
          change
            (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) F) =
              (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) A)
          rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr F n,
            PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr A n]
          by_cases hdiv : r ∣ n
          · have hdivlt : n / r < n :=
              Nat.div_lt_self hn (Fact.out : Nat.Prime r).one_lt
            simp [hdiv, A, PowerSeries.coeff_trunc, hdivlt]
          · simp [hdiv]
        have hPow :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r) =
              (PowerSeries.coeff (R := ℚ) n) (A ^ r) +
                (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
          simpa [A] using coeff_pow_eq_trunc_add (F := F) (n := n) (k := r) hn hF1
        have hDiff :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ r - PowerSeries.subst (PowerSeries.X ^ r) A) +
                (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
          rw [map_sub, map_sub, hPow, hSubstA]
          ring
        rcases pow_r_sub_subst_X_pow_r_in_r_smul r hA_integral n with
          ⟨qA, hqA, hqAcoeff⟩
        have hmain :
            (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F =
              (r : ℚ) * (qD - qA) := by
          calc
            (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F
                =
                  (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) -
                    (PowerSeries.coeff (R := ℚ) n)
                      (A ^ r - PowerSeries.subst (PowerSeries.X ^ r) A) := by
                    rw [hDiff]
                    ring
            _ = (r : ℚ) * qD - (r : ℚ) * qA := by
                  rw [hqDcoeff, hqAcoeff]
            _ = (r : ℚ) * (qD - qA) := by ring
        have hrQ : (r : ℚ) ≠ 0 := by
          exact_mod_cast (Fact.out : Nat.Prime r).ne_zero
        have hcoeff :
            (PowerSeries.coeff (R := ℚ) n) F = qD - qA :=
          mul_left_cancel₀ hrQ hmain
        rw [hcoeff]
        exact hqD.sub hqA
end IsRIntegralPS

end D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
open PowerSeries Finset
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

private theorem localRat_iff_val_nonneg (p : ℕ) (hp : p.Prime) (q : ℚ) :
    IsRIntegralRat p q ↔ 0 ≤ padicValRat p q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd0 : q.den ≠ 0 := q.den_nz
  have he : IsRIntegralRat p q ↔ padicValNat p q.den = 0 := by
    rw [IsRIntegralRat, Nat.coprime_comm, hp.coprime_iff_not_dvd, padicValNat.eq_zero_iff]
    simp [hp.ne_one, hd0]
  rw [he, padicValRat_def]
  constructor
  · intro h
    simp [h]
  · intro h
    rcases q.num_or_den_zero_padicVal hp with hn | hd
    · rw [hn] at h
      omega
    · exact hd

private theorem integral_of_local (f : PowerSeries ℚ)
    (h : ∀ p : ℕ, p.Prime → IsRIntegralPS p f) : IntegralSeries f := by
  intro n
  have hd : (coeff n f).den = 1 := by
    by_contra hn
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn
    have hc := (h p hp n).symm
    exact (hp.coprime_iff_not_dvd.mp hc) hdvd
  exact ⟨(coeff n f).num, ((Rat.den_eq_one_iff _).mp hd).symm⟩


private theorem expSeries_coeff (h : PowerSeries ℚ) (hh : constantCoeff h = 0) (n : ℕ) :
    coeff n ((PowerSeries.subst h (exp ℚ))) =
      ∑ j ∈ range (n + 1), coeff n (h ^ j) / (j.factorial : ℚ) := by
  classical
  rw [coeff_subst' (.of_constantCoeff_zero hh)]
  simp only [coeff_exp, smul_eq_mul]
  rw [finsum_eq_sum_of_support_subset]
  · apply sum_congr rfl
    intro j hj
    simp
    ring
  · intro j hj
    by_contra hjn
    have hlt : n < j := by simp only [mem_coe, mem_range] at hjn; omega
    have hz : coeff n (h ^ j) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hh) j) n hlt
    exact hj (by simp [hz])

private theorem expSeries_constant {h : PowerSeries ℚ} (hh : constantCoeff h = 0) :
    constantCoeff ((PowerSeries.subst h (exp ℚ))) = 1 := by
  change MvPowerSeries.constantCoeff _ = _
  rw [constantCoeff_subst_of_constantCoeff_zero hh]
  simp

private theorem expSeries_derivative {h : PowerSeries ℚ} (hh : constantCoeff h = 0) :
    derivative ((PowerSeries.subst h (exp ℚ))) = (PowerSeries.subst h (exp ℚ)) * derivative h := by
  rw [derivative_subst (.of_constantCoeff_zero hh), derivative_exp]


private theorem first_order_unique {f g a : PowerSeries ℚ}
    (hf0 : constantCoeff f = 1) (hg0 : constantCoeff g = 1)
    (hf : derivative f = f * a) (hg : derivative g = g * a) : f = g := by
  apply D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique f g a
  · simp [coeff_zero_eq_constantCoeff, hf0, hg0]
  · simpa [mul_comm] using hf
  · simpa [mul_comm] using hg

private theorem expSeries_add {f g : PowerSeries ℚ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (PowerSeries.subst (f + g) (exp ℚ)) = (PowerSeries.subst f (exp ℚ)) * (PowerSeries.subst g (exp ℚ)) := by
  apply first_order_unique (a := derivative f + derivative g)
  · apply expSeries_constant
    simp [hf, hg]
  · simp [expSeries_constant hf, expSeries_constant hg]
  · rw [expSeries_derivative (by simp [hf, hg]), map_add]
  · rw [Derivation.leibniz, expSeries_derivative hf, expSeries_derivative hg]
    simp only [smul_eq_mul]
    ring

theorem expSeries_nsmul {f : PowerSeries ℚ} (hf : constantCoeff f = 0) (n : ℕ) :
    (PowerSeries.subst (n • f) (exp ℚ)) = (PowerSeries.subst f (exp ℚ)) ^ n := by
  let hs : HasSubst f := .of_constantCoeff_zero hf
  rw [← subst_pow hs, exp_pow_eq_rescale_exp, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' (n : ℚ)) hs,
    subst_smul hs, subst_X hs, Nat.cast_smul_eq_nsmul]

private theorem expSeries_neg {f : PowerSeries ℚ} (hf : constantCoeff f = 0) :
    (PowerSeries.subst (-f) (exp ℚ)) = ((PowerSeries.subst f (exp ℚ)))⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by rw [expSeries_constant hf]; norm_num)).mpr
  rw [← expSeries_add (by simp [hf]) hf, neg_add_cancel]
  simp [subst_zero_eq_C_constantCoeff]

private theorem expSeries_subst (h : PowerSeries ℚ) (hh : constantCoeff h = 0)
    (p : ℕ) (hp : p ≠ 0) :
    (PowerSeries.subst (h.subst ((X : PowerSeries ℚ) ^ p)) (exp ℚ)) = PowerSeries.subst ((X : PowerSeries ℚ) ^ p) (PowerSeries.subst h (exp ℚ)) := by
  exact (subst_comp_subst_apply (.of_constantCoeff_zero hh) (.X_pow hp) _).symm

private theorem exp_multiple (p : ℕ) (hp : p.Prime) (g : PowerSeries ℚ)
    (hg : constantCoeff g = 0) (hl : IsRIntegralPS p g) :
    IsRMultipleIntegralPS p ((PowerSeries.subst (C (p : ℚ) * g) (exp ℚ)) - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro n
  refine ⟨coeff n ((PowerSeries.subst (C (p : ℚ) * g) (exp ℚ)) - 1) / p, ?_, ?_⟩
  · by_cases hn : n = 0
    · subst n
      simp only [map_sub, coeff_zero_eq_constantCoeff,
        expSeries_constant (show constantCoeff (C (p : ℚ) * g) = 0 by simp [hg]),
        map_one, sub_self, zero_div]
      exact IsRIntegralRat.zero p
    · rw [map_sub, coeff_one, if_neg hn, sub_zero,
        expSeries_coeff _ (by simp [hg]), sum_div]
      apply IsRIntegralRat.sum
      intro j hj
      have hc : coeff n ((C (p : ℚ) * g) ^ j) / (j.factorial : ℚ) / p =
          ((p : ℚ) ^ j / (j.factorial : ℚ) / p) * coeff n (g ^ j) := by
        rw [mul_pow, ← map_pow, coeff_C_mul]
        ring
      rw [hc]
      by_cases hj0 : j = 0
      · subst j
        simp only [pow_zero, coeff_one, if_neg hn, mul_zero]
        exact IsRIntegralRat.zero p
      · refine IsRIntegralRat.mul ?_ (hl.pow j n)
        apply (localRat_iff_val_nonneg p hp _).mpr
        rw [padicValRat.div (div_ne_zero (pow_ne_zero _ hpQ)
          (by exact_mod_cast Nat.factorial_ne_zero j)) hpQ,
          padicValRat.div (pow_ne_zero _ hpQ) (by exact_mod_cast Nat.factorial_ne_zero j),
          padicValRat.pow, padicValRat.self hp.one_lt, mul_one, padicValRat.of_nat]
        have hj := padicValNat_factorial_lt_of_ne_zero p hj0
        omega
  · field_simp

private theorem local_exp_of_log_difference (p : ℕ) (hp : p.Prime)
    (h : PowerSeries ℚ) (hh : constantCoeff h = 0)
    (hl : IsRIntegralPS p (h - C ((p : ℚ)⁻¹) * h.subst ((X : PowerSeries ℚ) ^ p))) :
    IsRIntegralPS p ((PowerSeries.subst h (exp ℚ))) := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := h - C ((p : ℚ)⁻¹) * h.subst ((X : PowerSeries ℚ) ^ p)
  have hg : constantCoeff g = 0 := by
    dsimp [g]
    rw [map_sub, map_mul, constantCoeff_C, constantCoeff_subst_X_pow hp.ne_zero, hh]
    simp
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs0 : constantCoeff (h.subst ((X : PowerSeries ℚ) ^ p)) = 0 := by
    rw [constantCoeff_subst_X_pow hp.ne_zero, hh, map_zero]
  have he : C (p : ℚ) * g = p • h + -(h.subst ((X : PowerSeries ℚ) ^ p)) := by
    dsimp [g]
    rw [mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hpQ, map_one, one_mul,
      map_natCast, nsmul_eq_mul, sub_eq_add_neg]
  have hexp : (PowerSeries.subst (C (p : ℚ) * g) (exp ℚ)) =
      ((PowerSeries.subst h (exp ℚ))) ^ p * (PowerSeries.subst ((X : PowerSeries ℚ) ^ p) (PowerSeries.subst h (exp ℚ)))⁻¹ := by
    rw [he, expSeries_add (by simp [hh]) (by simp [hs0]),
      expSeries_nsmul hh, expSeries_neg hs0,
      expSeries_subst h hh p hp.ne_zero]
  apply IsRIntegralPS.dieudonneDwork_mpr p (expSeries_constant hh)
  intro n hn
  have hm := exp_multiple p hp g hg hl n
  rw [hexp] at hm
  exact hm

private theorem local_int_div_nat (p : ℕ) (hp : p.Prime) (z : ℤ) (n : ℕ)
    (hn : n ≠ 0) (hz : (p : ℤ) ^ padicValNat p n ∣ z) :
    IsRIntegralRat p ((z : ℚ) / n) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hz0 : z = 0
  · subst z
    simpa using IsRIntegralRat.zero p
  · apply (localRat_iff_val_nonneg p hp _).mpr
    rw [padicValRat.div (by exact_mod_cast hz0) (by exact_mod_cast hn),
      padicValRat.of_int, padicValRat.of_nat]
    have hv := ((padicValInt_dvd_iff _ _).mp hz).resolve_left hz0
    omega

def Dold (c : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m : ℕ, m ≠ 0 →
    (p : ℤ) ^ (padicValNat p m + 1) ∣ c (p*m) - c m

noncomputable def logInput (c : ℕ → ℤ) : PowerSeries ℚ :=
  mk fun n => (c n : ℚ) / n

private theorem logInput_zero (c : ℕ → ℤ) : constantCoeff (logInput c) = 0 := by
  simp [logInput]

theorem integral_exp_of_dold (c : ℕ → ℤ) (hc : Dold c) :
    IntegralSeries ((PowerSeries.subst (logInput c) (exp ℚ))) := by
  apply integral_of_local
  intro p hp
  apply local_exp_of_log_difference p hp _ (logInput_zero c)
  intro n
  letI : Fact p.Prime := ⟨hp⟩
  rw [map_sub, coeff_C_mul, coeff_subst_X_pow hp.ne_zero]
  simp only [Algebra.algebraMap_self_apply]
  by_cases hn : n = 0
  · subst n
    simp [logInput]
    exact IsRIntegralRat.zero p
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    have hdiv : n / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos)
    have hnv : padicValNat p n = padicValNat p (n / p) + 1 := by
      conv_lhs => rw [← Nat.mul_div_cancel' hpn]
      rw [padicValNat.mul hp.ne_zero hdiv, padicValNat.self hp.one_lt]
      omega
    have hd : (p : ℤ) ^ padicValNat p n ∣ c n - c (n/p) := by
      rw [hnv]
      simpa only [Nat.mul_div_cancel' hpn] using hc p hp (n/p) hdiv
    have he : coeff n (logInput c) - (p : ℚ)⁻¹ * coeff (n/p) (logInput c) =
        ((c n - c (n/p) : ℤ) : ℚ) / n := by
      simp only [logInput, coeff_mk, Int.cast_sub]
      have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hdQ : ((n/p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdiv
      have heQ : (n : ℚ) = p * (n/p : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hpn).symm
      have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [heQ]
      field_simp
    rw [he]
    exact local_int_div_nat p hp _ n hn hd
  · rw [if_neg hpn, mul_zero, sub_zero]
    simp only [logInput, coeff_mk]
    apply local_int_div_nat p hp _ n hn
    simp [padicValNat.eq_zero_of_not_dvd hpn]

end D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
