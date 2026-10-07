/- GID: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge
   mirror-E: none(waiver:formal-series-identities-without-numerical-certificate)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: Proves the formal Catalan inverse used in recovery and an arbitrary rational-series coefficient transform using the original Lagrange supplier. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative

namespace P13CatalanLagrangeBridge

open PowerSeries

noncomputable section

abbrev PS := PowerSeries ℚ

def catalanUnit : PS := PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)

def q : PS := catalanUnit - 1

theorem catalanUnit_equation : catalanUnit ^ 2 * X + 1 = catalanUnit := by
  simpa [catalanUnit] using congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    PowerSeries.catalanSeries_sq_mul_X_add_one

theorem catalanUnit_constantCoeff : constantCoeff catalanUnit = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [catalanUnit]

theorem q_constantCoeff : constantCoeff q = 0 := by
  simp [q, catalanUnit_constantCoeff]

theorem q_equation : q = X * (1 + q) ^ 2 := by
  calc
    q = catalanUnit - 1 := rfl
    _ = catalanUnit ^ 2 * X := by
      have h := congrArg (fun t : PS => t - 1) catalanUnit_equation
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.symm
    _ = X * catalanUnit ^ 2 := by ring
    _ = X * (1 + q) ^ 2 := by simp [q]

def sourceUnitSq : PS := (1 + X) ^ 2

def sourceUnitSqInv : PS :=
  PowerSeries.invOfUnit sourceUnitSq (Units.mk0 (1 : ℚ) one_ne_zero)

def zeta : PS := X * sourceUnitSqInv

theorem sourceUnitSq_inv_right : sourceUnitSq * sourceUnitSqInv = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp [sourceUnitSq]

theorem sourceUnitSq_inv_left : sourceUnitSqInv * sourceUnitSq = 1 := by
  apply PowerSeries.invOfUnit_mul
  simp [sourceUnitSq]

theorem zeta_constantCoeff : constantCoeff zeta = 0 := by
  simp [zeta]

theorem zeta_subst_q : subst q zeta = X := by
  let substitution : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
  have hmap := congrArg (substAlgHom substitution) sourceUnitSq_inv_right
  have hmap' : (1 + q) ^ 2 * subst q sourceUnitSqInv = 1 := by
    have hmap'' : subst q (sourceUnitSq * sourceUnitSqInv) = subst q (1 : PS) := by
      simpa only [coe_substAlgHom] using hmap
    rw [sourceUnitSq, subst_mul substitution, subst_pow substitution,
      subst_add substitution, subst_X substitution] at hmap''
    have h_one : subst q (1 : PS) = 1 := by
      rw [← coe_substAlgHom substitution, map_one]
    rw [h_one] at hmap''
    simpa using hmap''
  calc
    subst q zeta = subst q (X * sourceUnitSqInv) := by rfl
    _ = subst q X * subst q sourceUnitSqInv := by rw [subst_mul substitution]
    _ = q * subst q sourceUnitSqInv := by rw [subst_X substitution]
    _ = (X * (1 + q) ^ 2) * subst q sourceUnitSqInv := by
      exact congrArg (fun t : PS => t * subst q sourceUnitSqInv) q_equation
    _ = X := by rw [mul_assoc, hmap', mul_one]

def catalanFactor : PS := (1 + X) ^ 2

theorem q_factor_equation : q = X * subst q catalanFactor := by
  let substitution : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
  have hsubst : subst q catalanFactor = (1 + q) ^ 2 := by
    rw [show catalanFactor = (1 + X) ^ 2 by rfl,
      subst_pow substitution, subst_add substitution, subst_X substitution]
    have h_one : subst q (1 : PS) = 1 := by
      rw [← coe_substAlgHom substitution, map_one]
    rw [h_one]
  calc
    q = X * (1 + q) ^ 2 := q_equation
    _ = X * subst q catalanFactor := by rw [hsubst]

theorem binomialCoefficient (exponent index : ℕ) :
    coeff index ((1 + X : PS) ^ exponent) = (exponent.choose index : ℚ) := by
  have polynomial : ((1 + X : PS) ^ exponent) =
      ((1 + Polynomial.X : Polynomial ℚ) ^ exponent : Polynomial ℚ) := by simp
  rw [polynomial, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem one_sub_X_power_coefficient (exponent index : ℕ) :
    coeff index ((1 - X : PS) * (1 + X) ^ exponent) =
      if index = 0 then 1 else
        (exponent.choose index : ℚ) - (exponent.choose (index - 1) : ℚ) := by
  by_cases hindex : index = 0
  · subst index
    simp
  · rw [show (1 - X : PS) * (1 + X) ^ exponent =
      (1 + X) ^ exponent - X * (1 + X) ^ exponent by ring]
    rw [map_sub]
    cases index with
    | zero => contradiction
    | succ index =>
      rw [coeff_succ_X_mul, binomialCoefficient, binomialCoefficient]
      simp

theorem q_power_coefficient_bridge (degree power : ℕ) (positive : 1 ≤ power)
    (bounded : power ≤ degree) :
    coeff degree (q ^ power) =
      coeff (degree - power) ((1 - X) * (1 + X) ^ (2 * degree - 1)) := by
  have hlag := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient q catalanFactor q_constantCoeff q_factor_equation
    degree power positive bounded
  have hfactor : catalanFactor ^ degree = (1 + X) ^ (2 * degree) := by
    simp [catalanFactor, pow_mul]
  rw [hfactor] at hlag
  have hcoeff := one_sub_X_power_coefficient (2 * degree - 1) (degree - power)
  by_cases edge : degree = power
  · subst degree
    have hc : coeff power (q ^ power) = 1 := by
      apply mul_left_cancel₀ (show (power : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt positive))
      simpa using hlag
    simpa using hc
  have mpos : 0 < degree - power := by omega
  rw [if_neg (Nat.ne_of_gt mpos)] at hcoeff
  have choose_pascal :
      (2 * degree).choose (degree - power) =
        (2 * degree - 1).choose (degree - power) +
          (2 * degree - 1).choose (degree - power - 1) := by
    have top : 2 * degree - 1 + 1 = 2 * degree := by omega
    have bottom : degree - power - 1 + 1 = degree - power := by omega
    simpa only [top, bottom, add_comm] using
      Nat.choose_succ_succ' (2 * degree - 1) (degree - power - 1)
  have choose_ratio :
      ((2 * degree - 1).choose (degree - power) : ℚ) * (degree - power) =
        ((2 * degree - 1).choose (degree - power - 1) : ℚ) * (degree + power) := by
    have h := Nat.choose_succ_right_eq (2 * degree - 1) (degree - power - 1)
    have hsub : (2 * degree - 1) - (degree - power - 1) = degree + power := by omega
    rw [Nat.sub_add_cancel (show 1 ≤ degree - power by omega), hsub] at h
    exact_mod_cast h
  rw [binomialCoefficient, choose_pascal] at hlag
  push_cast at hlag choose_ratio
  have degree_nonzero : (degree : ℚ) ≠ 0 := by
    exact_mod_cast (show degree ≠ 0 by omega)
  have scaled : (degree : ℚ) *
      (coeff degree (q ^ power) -
        coeff (degree - power) ((1 - X) * (1 + X) ^ (2 * degree - 1))) = 0 := by
    rw [hcoeff]
    linear_combination hlag - choose_ratio
  exact sub_eq_zero.mp ((mul_eq_zero.mp scaled).resolve_left degree_nonzero)

theorem q_zero_power_coefficient_bridge (degree : ℕ) (positive : 1 ≤ degree) :
    coeff degree (q ^ 0) =
      coeff degree ((1 - X) * (1 + X) ^ (2 * degree - 1)) := by
  have hcoeff := one_sub_X_power_coefficient (2 * degree - 1) degree
  rw [pow_zero]
  rw [coeff_one]
  simp only [if_neg (Nat.ne_of_gt positive)]
  rw [hcoeff]
  have hs : (2 * degree - 1).choose degree = (2 * degree - 1).choose (degree - 1) := by
    exact Nat.choose_symm_of_eq_add (by omega)
  simp [Nat.ne_of_gt positive, hs]

theorem q_subst_coefficient_transform (G : PS) (degree : ℕ) (positive : 1 ≤ degree) :
    coeff degree (G.subst q) =
      coeff degree ((1 - X) * (1 + X) ^ (2 * degree - 1) * G) := by
  classical
  have substitution : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
  have vanishes (index : ℕ) (bound : degree < index) : coeff degree (q ^ index) = 0 := by
    apply coeff_of_lt_order
    exact (show (degree : ENat) < (index : ENat) by exact_mod_cast bound).trans_le
      (le_order_pow_of_constantCoeff_eq_zero index q_constantCoeff)
  have finiteSubstitution : coeff degree (G.subst q) =
      ∑ index ∈ Finset.range (degree + 1), coeff index G * coeff degree (q ^ index) := by
    rw [coeff_subst' substitution]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro index supported
    apply Finset.mem_range.mpr
    by_contra unbounded
    exact supported (by simp [vanishes index (by omega)])
  have coefficient_product :
      coeff degree ((1 - X) * (1 + X) ^ (2 * degree - 1) * G) =
        ∑ index ∈ Finset.range (degree + 1),
          coeff index G * coeff (degree - index) ((1 - X) * (1 + X) ^ (2 * degree - 1)) := by
    rw [show (1 - X) * (1 + X) ^ (2 * degree - 1) * G =
      G * ((1 - X) * (1 + X) ^ (2 * degree - 1)) by ring]
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [finiteSubstitution, coefficient_product]
  apply Finset.sum_congr rfl
  intro index member
  have indexBound : index ≤ degree := by
    have bound := Finset.mem_range.mp member
    omega
  by_cases zeroIndex : index = 0
  · subst index
    simp only [Nat.sub_zero]
    rw [q_zero_power_coefficient_bridge degree positive]
  · rw [q_power_coefficient_bridge degree index (by omega) indexBound]

end

end P13CatalanLagrangeBridge
