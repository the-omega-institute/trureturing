/- GID: D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lagrange substitution and Frobenius pairing prove Hanna's six A352700 congruences. -/

/-
admission_basis: open-problem-resolution (#23834; Proved)
proof_shape: bind-only; escape_witness: none (all 61 declarations).
claim states the preregistered A352700 conventions, with
  CatalanCompositionSquareParity.catalanUnit the unique integral Catalan series owner and
  BilateralProductModFour.geometric the series (1 + X)⁻¹.
Escape audit: https://github.com/the-omega-institute/trureturing/issues/23867
  declared_unresolved; IE-C050 ClosedTruthReadout; rule=source.selection_missing.
D5 prerequisites (declaration GID + declaration statement_id):
  F1,F2: publicized in-delivery on baseline-frozen owner
    D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.
  F1 = D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanUnit
       sha256:b9c8fb3591b39d2488babe09d2c3241fe8016583066562d7cfb3e97346a8aac5
  F2 = D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalan_unit_zero
       sha256:70709e3692915e025286726aaf9081b9c8488968b06e87218c79617890269594
  F3 = D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric
       sha256:80ed9523b58a8a0f4a0c74044ec4c610bf38e0367af73a0f45716e77b91034ad
  F4 = D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_spec
       sha256:4d70f360961d373830d24491955d96c375f2d50e16d1447fe4ae3e9a2d5b99fc
  F5 = D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_coeff
       sha256:c5b3060aa86400d269cb4da4399efbdbda36f9c063ded8848c47f5b9c8e84af6
  F6 = D5/S3/Analytic/AlternatingPoleCoefficients.alternating_pole_coefficients
       sha256:e29b792d0ed8e1a7ad34da1d4fd3aa3f3657194cd8840c35e66096e8c56f1a37
  F7 = D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.inverse_exists
       sha256:699ca6de84d9aa85427498d9c48e49a817ebc2d7c58d1ec212f59a1dcd6ac523
  F8 = D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.prime_power_subst
       sha256:2962076255eafd8a6f2925bf977ca6619ae05c3bc48a2e476b60e3972c3c2466
Public defs (proof_shape: bind-only; escape_witness: none; name -> consumers):
  catalanInvZ -> catalanInvZ_eq, catalanInvZ_subst_zetaZ, catalanZ_mul_inv, coeffA,
  dvd_seriesA_sub_truncA, geometric_subst_qZ, seriesMod_three_diff_zero, truncA, truncA_subst_zetaZ,
  zetaZ_subst_qZ; catalanMod -> catalanMod_cubic_eq_linear, claim, result,
  seriesMod_three_eq_linear, seriesMod_two_eq; claim -> result; coeffA -> claim,
  dvd_seriesA_sub_truncA, result, seriesA; raneyTerm -> claim, coeff_linear_catalanZ,
  raneyTerm_succ_succ_add_catalan, result; seriesA -> dvd_seriesA_sub_truncA, result,
  seriesA_eq_subst, seriesA_subst_zetaZ, seriesMod, seriesMod_three_diff_zero,
  seriesMod_three_eq_linear, seriesMod_two_eq; seriesMod -> claim, result,
  seriesMod_three_eq_linear, seriesMod_two_eq; weight -> coeffA, coeffB, coeffB_eq,
  coeffB_mod_three_tail_zero, coeffB_mod_two_succ_succ, coeffB_one, coeffB_zero, coeff_trunc_eq,
  dvd_seriesA_sub_truncA, mul_weight, seriesA_subst_zetaZ, seriesB_mod_three, succ_mul_weight,
  truncA, truncA_subst_zetaZ, truncB, weight_choose_split, weight_mod_three_eq_zero_of_mod_ne_one,
  weight_three_mul_add_one_mod_three.
Public theorem (proof_shape: bind-only; escape_witness: none; name -> consumers):
  result -> none (sole root).
Private defs (proof_shape: bind-only; escape_witness: none; name -> consumers):
  coeffB -> coeffB_eq, coeffB_mod_two_succ_succ, coeffB_one, coeffB_zero, seriesA_subst_zetaZ,
  seriesB, seriesB_mod_three, seriesB_mod_two; qZ -> catalanInvZ_subst_zetaZ, constantCoeff_qZ,
  geometric_subst_qZ, hasSubst_qZ_map, qZ_subst_zetaZ, seriesA_eq_subst, seriesMod_three_diff_zero,
  seriesMod_two_eq, zetaZ_subst_qZ; seriesB -> seriesA_eq_subst, seriesA_subst_zetaZ,
  seriesB_mod_three, seriesB_mod_two, seriesMod_three_diff_zero, seriesMod_two_eq; truncA ->
  dvd_seriesA_sub_truncA, seriesA_subst_zetaZ, truncA_subst_zetaZ; truncB -> seriesA_subst_zetaZ,
  truncA_subst_zetaZ; zetaZ -> catalanInvZ_subst_zetaZ, coeff_one_zetaZ, constantCoeff_zetaZ,
  qZ_subst_zetaZ, seriesA_eq_subst, seriesA_subst_zetaZ, truncA_subst_zetaZ, zetaZ_subst_qZ.
Private theorems (proof_shape: bind-only; escape_witness: none; name -> consumers):
  catalanInvZ_eq -> seriesMod_three_diff_zero; catalanInvZ_subst_zetaZ -> truncA_subst_zetaZ;
  catalanMod_cubic_eq_linear -> result; catalanZ_eq -> catalanInvZ_eq, catalan_cubic_linear_eq_Z,
  zetaZ_subst_qZ; catalanZ_mul_inv -> catalanInvZ_eq, catalanInvZ_subst_zetaZ, geometric_subst_qZ,
  zetaZ_subst_qZ; catalan_cubic_linear_eq_Z -> catalanMod_cubic_eq_linear; choose_add_mul_prime_pow
  -> mod_three_quadratic_choose_sum_zero, mod_two_quadratic_choose_sum_zero;
  choose_mul_prime_pow_add -> choose_prime_pow_decomp, mod_two_quadratic_choose_sum_zero;
  choose_prime_pow_decomp -> choose_add_mul_prime_pow, coeffB_mod_three_tail_zero,
  mod_three_quadratic_choose_sum_zero, weight_mod_three_eq_zero_of_mod_ne_one,
  weight_three_mul_add_one_mod_three; choose_three_mul_mod_three ->
  weight_mod_three_eq_zero_of_mod_ne_one; choose_two_mul_add_one_div -> coeff_linear_catalanZ;
  coeffB_eq -> coeffB_mod_two_succ_succ, coeffB_one, coeffB_zero, seriesB_mod_three;
  coeffB_mod_three_tail_zero -> seriesB_mod_three; coeffB_mod_two_succ_succ -> seriesB_mod_two;
  coeffB_one -> seriesB_mod_three, seriesB_mod_two; coeffB_zero -> seriesB_mod_three,
  seriesB_mod_two; coeff_geometric_pow -> coeffB_eq; coeff_linear_catalanZ -> result;
  coeff_one_zetaZ -> qZ_subst_zetaZ; coeff_trunc_eq -> dvd_seriesA_sub_truncA, seriesA_subst_zetaZ;
  constantCoeff_qZ -> geometric_subst_qZ, hasSubst_qZ_map, qZ_subst_zetaZ, seriesA_eq_subst,
  seriesMod_three_diff_zero, seriesMod_two_eq, zetaZ_subst_qZ; constantCoeff_zetaZ ->
  catalanInvZ_subst_zetaZ, qZ_subst_zetaZ, seriesA_eq_subst, seriesA_subst_zetaZ,
  truncA_subst_zetaZ; dvd_seriesA_sub_truncA -> seriesA_subst_zetaZ; geometric_pow_eq_rescale ->
  coeff_geometric_pow; geometric_subst_qZ -> seriesMod_three_diff_zero, zetaZ_subst_qZ;
  hasSubst_qZ_map -> seriesMod_three_diff_zero, seriesMod_two_eq;
  mod_three_quadratic_choose_sum_zero -> coeffB_mod_three_tail_zero;
  mod_two_quadratic_choose_sum_zero -> coeffB_mod_two_succ_succ; mul_weight -> succ_mul_weight,
  weight_choose_split, weight_mod_three_eq_zero_of_mod_ne_one; qZ_subst_zetaZ ->
  catalanInvZ_subst_zetaZ; raneyTerm_succ_succ_add_catalan -> coeff_linear_catalanZ;
  seriesA_eq_subst -> seriesMod_three_diff_zero, seriesMod_two_eq; seriesA_subst_zetaZ ->
  seriesA_eq_subst; seriesB_mod_three -> seriesMod_three_diff_zero; seriesB_mod_two ->
  seriesMod_two_eq; seriesMod_three_diff_zero -> result, seriesMod_three_eq_linear;
  seriesMod_three_eq_linear -> result; seriesMod_two_eq -> result; succ_mul_weight ->
  weight_three_mul_add_one_mod_three; sum_range_three_step -> coeffB_mod_three_tail_zero;
  truncA_subst_zetaZ -> seriesA_subst_zetaZ; weight_choose_split -> coeffB_mod_two_succ_succ;
  weight_dvd -> mul_weight; weight_mod_three_eq_zero_of_mod_ne_one -> coeffB_mod_three_tail_zero;
  weight_three_mul_add_one_mod_three -> coeffB_mod_three_tail_zero; zetaZ_subst_qZ ->
  qZ_subst_zetaZ, seriesA_eq_subst.
-/

import D5.S1.Recurrence.Bilateral.BilateralProductModFour
import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree
import D5.S3.Analytic.AlternatingPoleCoefficients
import Mathlib.Data.Nat.Choose.Lucas

/-! # Hanna's modulo 2 and modulo 3 conjectures for OEIS A352700 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Finset PowerSeries

namespace D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences
/-- Exact integer weight `binomial((m+1)(2m+1), m) / (2m+1)` in OEIS A352700. -/
def weight (m : ℕ) : ℕ := Nat.choose ((m + 1) * (2 * m + 1)) m / (2 * m + 1)
/-- Multiplicative inverse `C(X)⁻¹` of the integral Catalan series in `ℤ⟦X⟧`. -/
def catalanInvZ : PowerSeries ℤ := PowerSeries.invOfUnit
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit 1
/-- Coefficient sequence `a(n) = [X^n] A(X)` of OEIS A352700. -/
def coeffA (n : ℕ) : ℤ :=
  ∑ m ∈ range (n + 1),
    (weight m : ℤ) * coeff (n - m) (catalanInvZ ^ (m * (2 * m + 1) + 1))
/-- Integral generating series `A(X) = ∑_{n≥0} a(n) X^n` of OEIS A352700. -/
def seriesA : PowerSeries ℤ := PowerSeries.mk coeffA
/-- Coefficientwise reduction of `A(X)` modulo `p`. -/
def seriesMod (p : ℕ) : PowerSeries (ZMod p) := seriesA.map (Int.castRingHom (ZMod p))
/-- Coefficientwise reduction of `C(X)` modulo `p`. -/
def catalanMod (p : ℕ) : PowerSeries (ZMod p) :=
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit.map (Int.castRingHom
    (ZMod p))
/-- Second term `3 * binomial(2n-1, n-2) / (2n-1)` of conjecture (4), zero for `n < 2`. -/
def raneyTerm (n : ℕ) : ℕ :=
  if n < 2 then 0 else (3 * Nat.choose (2 * n - 1) (n - 2)) / (2 * n - 1)
/-- Conjunction of Paul D. Hanna's six numbered conjectures (1)–(6) in OEIS A352700. -/
def claim : Prop :=
  (seriesMod 3 ^ 3 = (seriesMod 3).subst (X ^ 3)) ∧
  (seriesMod 3 = catalanMod 3 + X ^ 2 * catalanMod 3 ^ 3 ∧
    catalanMod 3 + X ^ 2 * catalanMod 3 ^ 3 = (2 - X) * catalanMod 3 - 1) ∧
  (seriesMod 2 = catalanMod 2) ∧
  (∀ n : ℕ, Int.ModEq 3 (coeffA n)
    (((Nat.choose (2 * n + 1) n / (2 * n + 1) : ℕ) : ℤ) + (raneyTerm n : ℤ))) ∧
  (∀ n : ℕ, 1 ≤ n → Int.ModEq 3 (coeffA n)
    (2 * (catalan n : ℤ) - (catalan (n - 1) : ℤ))) ∧
  (∀ n : ℕ, Int.ModEq 2 (coeffA n) (catalan n : ℤ))
private theorem weight_dvd (m : ℕ) :
    (2 * m + 1) ∣ Nat.choose ((m + 1) * (2 * m + 1)) m := by
  cases m with
  | zero => simp
  | succ k =>
    have hEq : (2 * k ^ 2 + 7 * k + 5) + 1 = (k + 2) * (2 * k + 3) := by ring
    have hmul := Nat.add_one_mul_choose_eq (2 * k ^ 2 + 7 * k + 5) k
    rw [hEq] at hmul
    have hdvd : (2 * (k + 1) + 1) ∣ Nat.choose ((k + 2) * (2 * k + 3)) (k + 1) * (k + 1) := by
      rw [← hmul]
      exact ⟨(k + 2) * Nat.choose (2 * k ^ 2 + 7 * k + 5) k, by ring⟩
    exact ((Nat.coprime_mul_right_add_left 1 (k + 1) 2).mpr
      (Nat.coprime_one_left (k + 1))).dvd_of_dvd_mul_right hdvd
private theorem mul_weight (m : ℕ) :
    (2 * m + 1) * weight m = Nat.choose ((m + 1) * (2 * m + 1)) m :=
  Nat.mul_div_cancel' (weight_dvd m)
private theorem succ_mul_weight (k : ℕ) :
    (k + 1) * weight (k + 1) = (k + 2) * Nat.choose (2 * (k + 1) * (k + 2) + k + 1) k := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * (k + 1) + 1)
  have hw := mul_weight (k + 1)
  have hEq : (2 * (k + 1) * (k + 2) + k + 1) + 1 = (k + 2) * (2 * k + 3) := by ring
  have hmul := Nat.add_one_mul_choose_eq (2 * (k + 1) * (k + 2) + k + 1) k
  rw [hEq] at hmul
  calc
    (2 * (k + 1) + 1) * ((k + 1) * weight (k + 1))
        = ((2 * (k + 1) + 1) * weight (k + 1)) * (k + 1) := by ring
    _ = Nat.choose ((k + 2) * (2 * k + 3)) (k + 1) * (k + 1) := by
        rw [hw, show 2 * (k + 1) + 1 = 2 * k + 3 by omega, show k + 1 + 1 = k + 2 by omega]
    _ = ((k + 2) * (2 * k + 3)) * Nat.choose (2 * (k + 1) * (k + 2) + k + 1) k := hmul.symm
    _ = (2 * (k + 1) + 1) * ((k + 2) * Nat.choose (2 * (k + 1) * (k + 2) + k + 1) k) := by ring
private theorem catalanZ_eq : D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit
    = 1 + X * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  change D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit ^ 2 * X + 1 =
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit at h
  linear_combination -h
private theorem catalanZ_mul_inv :
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit * catalanInvZ = 1 :=
  PowerSeries.mul_invOfUnit D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit 1
      (by simpa using D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_unit_zero)
private theorem catalanInvZ_eq : catalanInvZ = 1 - X *
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit := by
  have h1 : D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit * (1 - X *
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit) = 1 := by
      linear_combination catalanZ_eq
  calc
    catalanInvZ = catalanInvZ *
        (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit * (1 - X *
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit)) := by rw [h1,
        mul_one]
    _ = (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit * catalanInvZ) * (1
        - X * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit) := by ring
    _ = 1 - X * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit := by rw
        [catalanZ_mul_inv, one_mul]
private theorem geometric_pow_eq_rescale (d : ℕ) :
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1) = rescale (-1 : ℤ)
        (invOneSubPow ℤ (d + 1)).val := by
  let g := rescale (-1 : ℤ) (invOneSubPow ℤ (d + 1)).val
  have hu : (1 - X : PowerSeries ℤ) ^ (d + 1) * (invOneSubPow ℤ (d + 1)).val = 1 :=
    (invOneSubPow ℤ (d + 1)).inv_val
  have hr := congrArg (rescale (-1 : ℤ)) hu
  simp only [map_mul, map_pow, map_sub, map_one, rescale_X, map_neg, neg_one_mul,
    sub_neg_eq_add] at hr
  change (1 + X : PowerSeries ℤ) ^ (d + 1) * g = 1 at hr
  have hl : D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1) * (1 + X :
      PowerSeries ℤ) ^ (d + 1) = 1 := by
    rw [← mul_pow, D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric_spec, one_pow]
  calc
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1) =
        D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1) * ((1 + X) ^ (d + 1)
        * g) := by rw [hr, mul_one]
    _ = (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1) * (1 + X) ^ (d + 1))
        * g := by ring
    _ = g := by rw [hl, one_mul]
private theorem coeff_geometric_pow (d k : ℕ) :
    coeff k (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ (d + 1)) = (-1 : ℤ) ^ k
        * (Nat.choose (d + k) k : ℤ) := by
  rw [geometric_pow_eq_rescale,
    D5.S3.Analytic.AlternatingPoleCoefficients.alternating_pole_coefficients,
    Nat.choose_symm_add]
private def qZ : PowerSeries ℤ :=
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1
private def zetaZ : PowerSeries ℤ := X *
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ 2
private theorem constantCoeff_qZ : constantCoeff qZ = 0 := by simp [qZ,
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_unit_zero]
private theorem constantCoeff_zetaZ : constantCoeff zetaZ = 0 := by simp [zetaZ]
private theorem coeff_one_zetaZ : coeff 1 zetaZ = 1 := by
  have hc : coeff 0 (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ 2) = 1 := by
    rw [coeff_zero_eq_constantCoeff, map_pow, ← coeff_zero_eq_constantCoeff,
      D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric_coeff]
    norm_num
  simpa [zetaZ, coeff_succ_X_mul] using hc
private theorem geometric_subst_qZ :
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric.subst qZ = catalanInvZ := by
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  have h := congrArg (fun f : PowerSeries ℤ => f.subst qZ)
    (by simpa only [mul_comm] using
      D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric_spec :
      (1 + X : PowerSeries ℤ) * D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric = 1)
  have h1 : (1 : PowerSeries ℤ).subst qZ = 1 := by rw [← coe_substAlgHom hsq, map_one]
  rw [subst_mul hsq, subst_add hsq, h1, subst_X hsq, show 1 + qZ =
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit by simp [qZ]] at h
  calc
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric.subst qZ = (catalanInvZ *
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit) *
        D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric.subst qZ := by
      rw [mul_comm catalanInvZ
          D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit, catalanZ_mul_inv,
          one_mul]
    _ = catalanInvZ * (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit *
        D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric.subst qZ) := by ring
    _ = catalanInvZ := by rw [h, mul_one]
private theorem zetaZ_subst_qZ : zetaZ.subst qZ = X := by
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  unfold zetaZ
  rw [subst_mul hsq, subst_X hsq, subst_pow hsq, geometric_subst_qZ]
  have hq : qZ = X * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit ^ 2 :=
      by unfold qZ; linear_combination catalanZ_eq
  calc
    qZ * catalanInvZ ^ 2 = X *
        (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit * catalanInvZ) ^ 2
        := by rw [hq]; ring
    _ = X := by rw [catalanZ_mul_inv, one_pow, mul_one]
private theorem qZ_subst_zetaZ : qZ.subst zetaZ = X := by
  obtain ⟨b, _, _, _, hbz⟩ :=
      D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.inverse_exists zetaZ
      constantCoeff_zetaZ coeff_one_zetaZ
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  have hsz : HasSubst zetaZ := .of_constantCoeff_zero constantCoeff_zetaZ
  have h1 : b = b.subst (zetaZ.subst qZ) := by
    rw [zetaZ_subst_qZ]
    exact (X_subst b).symm
  have hassoc := subst_comp_subst_apply (R := ℤ) (S := ℤ) (T := ℤ)
    (a := zetaZ) (b := qZ) hsz hsq b
  have h2 := congrArg (PowerSeries.subst (R := ℤ) qZ) hbz
  have h3 : PowerSeries.subst qZ (X : PowerSeries ℤ) = qZ := subst_X (R := ℤ) hsq
  have hbq : b = qZ := by
    with_reducible exact h1.trans (hassoc.symm.trans (h2.trans h3))
  exact hbq ▸ hbz
private theorem catalanInvZ_subst_zetaZ : catalanInvZ.subst zetaZ =
    D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric := by
  have hsz : HasSubst zetaZ := .of_constantCoeff_zero constantCoeff_zetaZ
  have h1 : (1 : PowerSeries ℤ).subst zetaZ = 1 := by rw [← coe_substAlgHom hsz, map_one]
  have hcat : D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit.subst zetaZ = 1
      + X := by
    rw [show D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit = 1 + qZ by
        unfold qZ; ring, subst_add hsz, h1, qZ_subst_zetaZ]
  have hm := congrArg (fun f : PowerSeries ℤ => f.subst zetaZ) catalanZ_mul_inv
  rw [subst_mul hsz, hcat, h1] at hm
  calc
    catalanInvZ.subst zetaZ = (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric * (1 +
        X)) * catalanInvZ.subst zetaZ := by
      rw [D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric_spec, one_mul]
    _ = D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric * ((1 + X) * catalanInvZ.subst
        zetaZ) := by ring
    _ = D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric := by rw [hm, mul_one]
private def coeffB (n : ℕ) : ℤ :=
  ∑ m ∈ range (n + 1), (weight m : ℤ) * coeff (n - m)
      (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ ((m + 1) * (2 * m + 1)))
private def seriesB : PowerSeries ℤ := PowerSeries.mk coeffB
private def truncA (N : ℕ) : PowerSeries ℤ :=
  ∑ m ∈ range (N + 1), C (weight m : ℤ) * X ^ m * catalanInvZ ^ (m * (2 * m + 1) + 1)
private def truncB (N : ℕ) : PowerSeries ℤ :=
  ∑ m ∈ range (N + 1), C (weight m : ℤ) * X ^ m *
      D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ ((m + 1) * (2 * m + 1))
private theorem coeff_trunc_eq {N n : ℕ} (hn : n ≤ N) (F : ℕ → PowerSeries ℤ) :
    coeff n (∑ m ∈ range (N + 1), C (weight m : ℤ) * X ^ m * F m) =
      ∑ m ∈ range (n + 1), (weight m : ℤ) * coeff (n - m) (F m) := by
  rw [map_sum, show N + 1 = (n + 1) + (N - n) by omega, Finset.sum_range_add _ (n + 1) (N - n)]
  have htail : ∑ x ∈ range (N - n),
      coeff n (C (weight (n + 1 + x) : ℤ) * X ^ (n + 1 + x) * F (n + 1 + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hnot : ¬ n + 1 + x ≤ n := by omega
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    simp only [hnot, ↓reduceIte, mul_zero]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [hmn, ↓reduceIte]
private theorem dvd_seriesA_sub_truncA (N : ℕ) :
    (X : PowerSeries ℤ) ^ (N + 1) ∣ seriesA - truncA N := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [map_sub, seriesA, coeff_mk, truncA, coeff_trunc_eq (Nat.lt_succ_iff.mp hn), coeffA, sub_self]
private theorem truncA_subst_zetaZ (N : ℕ) : (truncA N).subst zetaZ = truncB N := by
  have hsz : HasSubst zetaZ := .of_constantCoeff_zero constantCoeff_zetaZ
  unfold truncA truncB
  rw [← coe_substAlgHom hsz, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [map_mul, map_pow, coe_substAlgHom hsz]
  have hc : (C (weight m : ℤ)).subst zetaZ = C (weight m : ℤ) := subst_C (a := zetaZ) _
  rw [hc, subst_X hsz, catalanInvZ_subst_zetaZ]
  unfold zetaZ
  rw [mul_pow, ← pow_mul, ← mul_assoc (C (weight m : ℤ)), mul_assoc (C (weight m : ℤ) * X ^ m),
    ← pow_add, show 2 * m + (m * (2 * m + 1) + 1) = (m + 1) * (2 * m + 1) by ring]
private theorem seriesA_subst_zetaZ : seriesA.subst zetaZ = seriesB := by
  have hsz : HasSubst zetaZ := .of_constantCoeff_zero constantCoeff_zetaZ
  ext N
  obtain ⟨R, hR⟩ := dvd_seriesA_sub_truncA N
  have hsub := congrArg (fun f : PowerSeries ℤ => f.subst zetaZ) hR
  rw [subst_sub hsz, subst_mul hsz, subst_pow hsz, subst_X hsz, truncA_subst_zetaZ] at hsub
  have hdvd : (X : PowerSeries ℤ) ^ (N + 1) ∣ seriesA.subst zetaZ - truncB N := by
    rw [hsub]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd
        ⟨D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric ^ 2, rfl⟩ (N + 1)) _
  have hc0 : coeff N (seriesA.subst zetaZ - truncB N) = 0 :=
    (X_pow_dvd_iff.mp hdvd) N (Nat.lt_succ_self N)
  rw [map_sub, sub_eq_zero] at hc0
  rw [hc0, truncB, coeff_trunc_eq (le_refl N), seriesB, coeff_mk, coeffB]
private theorem seriesA_eq_subst : seriesA = seriesB.subst qZ := by
  have hsz : HasSubst zetaZ := .of_constantCoeff_zero constantCoeff_zetaZ
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  have h1 := congrArg (PowerSeries.subst (R := ℤ) qZ) seriesA_subst_zetaZ.symm
  have hassoc := subst_comp_subst_apply (R := ℤ) (S := ℤ) (T := ℤ)
    (a := zetaZ) (b := qZ) hsz hsq seriesA
  have h2 := congrArg
    (fun u : PowerSeries ℤ => PowerSeries.subst (R := ℤ) u seriesA) zetaZ_subst_qZ
  have h3 : PowerSeries.subst (X : PowerSeries ℤ) seriesA = seriesA := X_subst seriesA
  with_reducible exact (h1.trans (hassoc.trans (h2.trans h3))).symm
private theorem coeffB_eq (n : ℕ) :
    coeffB n = ∑ m ∈ range (n + 1),
      (-1 : ℤ) ^ (n - m) * (weight m : ℤ) * (Nat.choose (2 * m * (m + 1) + n) (n - m) : ℤ) := by
  unfold coeffB
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show (m + 1) * (2 * m + 1) = (2 * m * (m + 1) + m) + 1 by ring, coeff_geometric_pow,
    show (2 * m * (m + 1) + m) + (n - m) = 2 * m * (m + 1) + n by omega]
  ring
private theorem coeffB_zero : coeffB 0 = 1 := by simp [coeffB_eq, weight]
private theorem coeffB_one : coeffB 1 = 1 := by
  rw [coeffB_eq, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [weight]
/-! ### Frobenius binomial identities in `PowerSeries (ZMod p)` -/
private theorem choose_mul_prime_pow_add (p : ℕ) [Fact p.Prime]
    (d k R j M : ℕ) (hR : R < p ^ k) (hM : M < p ^ k) :
    ((d * p ^ k + R).choose (j * p ^ k + M) : ZMod p) =
      (d.choose j : ZMod p) * (R.choose M : ZMod p) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpk_pos : 0 < p ^ k := pow_pos hp_pos k
  have h1 := Choose.choose_modEq_choose_mul_prod_range_choose
    (n := d * p ^ k + R) (k := j * p ^ k + M) (p := p) k
  have hdiv1 : (d * p ^ k + R) / p ^ k = d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpk_pos, Nat.div_eq_of_lt hR, zero_add]
  have hdiv2 : (j * p ^ k + M) / p ^ k = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpk_pos, Nat.div_eq_of_lt hM, zero_add]
  have hdigit (c S i : ℕ) (hi : i < k) : (c * p ^ k + S) / p ^ i % p = S / p ^ i % p := by
    have hpi : 0 < p ^ i := pow_pos hp_pos i
    have hk : c * p ^ k + S = S + (c * p ^ (k - i - 1) * p) * p ^ i := by
      rw [mul_assoc (c * p ^ (k - i - 1)) p (p ^ i), ← pow_succ',
        mul_assoc c, ← pow_add, show k - i - 1 + (i + 1) = k by omega, add_comm]
    rw [hk, Nat.add_mul_div_right _ _ hpi, Nat.add_mul_mod_self_right]
  have hprod : (∏ i ∈ range k,
      ((d * p ^ k + R) / p ^ i % p).choose ((j * p ^ k + M) / p ^ i % p)) =
      ∏ i ∈ range k, (R / p ^ i % p).choose (M / p ^ i % p) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hdigit d R i (Finset.mem_range.mp hi), hdigit j M i (Finset.mem_range.mp hi)]
  rw [hdiv1, hdiv2, hprod, Nat.cast_prod] at h1
  have h2 := h1.trans ((Int.ModEq.refl ((d.choose j : ℕ) : ℤ)).mul
    (Choose.choose_modEq_prod_range_choose (p := p) hR hM).symm)
  have h3 := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h2
  simpa only [Int.cast_mul, Int.cast_natCast] using h3
private theorem choose_prime_pow_decomp (p : ℕ) [Fact p.Prime]
    {A B d k R j M : ℕ} (hA : A = d * p ^ k + R) (hB : B = j * p ^ k + M)
    (hR : R < p ^ k) (hM : M < p ^ k) :
    (A.choose B : ZMod p) = (d.choose j : ZMod p) * (R.choose M : ZMod p) := by
  subst hA; subst hB
  exact choose_mul_prime_pow_add p d k R j M hR hM
private theorem choose_add_mul_prime_pow (p : ℕ) [Fact p.Prime]
    (A q k N : ℕ) (hN : N < p ^ k) :
    ((A + q * p ^ k).choose N : ZMod p) = (A.choose N : ZMod p) := by
  have hR : A % p ^ k < p ^ k := Nat.mod_lt A (pow_pos (Fact.out : p.Prime).pos k)
  have hA : A = (A / p ^ k) * p ^ k + A % p ^ k := by
    rw [mul_comm]; exact (Nat.div_add_mod A (p ^ k)).symm
  have hAq : A + q * p ^ k = (A / p ^ k + q) * p ^ k + A % p ^ k := by
    conv_lhs => arg 1; rw [hA]
    ring
  rw [choose_prime_pow_decomp p hAq (show N = 0 * p ^ k + N by simp) hR hN,
    choose_prime_pow_decomp p hA (show N = 0 * p ^ k + N by simp) hR hN,
    Nat.choose_zero_right, Nat.choose_zero_right]
/-! ### Modulo 2 reduction: `seriesB ≡ 1 + X (mod 2)` -/
private theorem weight_choose_split (N k : ℕ) (hk : k ≤ N) :
    (2 * (k + 1) + 1) * weight (k + 1) *
        Nat.choose (2 * (k + 1) * (k + 2) + (N + 1)) (N - k) =
      Nat.choose (N + 1) (k + 1) * Nat.choose (2 * (k + 1) * (k + 2) + (N + 1)) (N + 1) +
        Nat.choose N k * Nat.choose (2 * (k + 1) * (k + 2) + 1 + N) N := by
  set B : ℕ := 2 * (k + 1) * (k + 2)
  rw [mul_weight (k + 1), show (k + 1 + 1) * (2 * (k + 1) + 1) = (B + k + 1) + 1 by
    dsimp [B]; ring, Nat.choose_succ_succ' (B + k + 1) k, Nat.add_mul]
  have h1 : Nat.choose (B + k + 1) (k + 1) * Nat.choose (B + (N + 1)) (N - k) =
      Nat.choose (N + 1) (k + 1) * Nat.choose (B + (N + 1)) (N + 1) := by
    have hcm := @Nat.choose_mul (B + (N + 1)) (N + 1) (N - k) (by omega)
    rw [show B + (N + 1) - (N - k) = B + k + 1 by omega,
      show N + 1 - (N - k) = k + 1 by omega] at hcm
    rw [mul_comm, ← hcm, Nat.choose_symm_of_eq_add (by omega : N + 1 = (N - k) + (k + 1)),
      mul_comm]
  have h2 : Nat.choose (B + k + 1) k * Nat.choose (B + (N + 1)) (N - k) =
      Nat.choose N k * Nat.choose (B + 1 + N) N := by
    rw [show B + (N + 1) = B + 1 + N by omega]
    have hcm := @Nat.choose_mul (B + 1 + N) N (N - k) (by omega)
    rw [show B + 1 + N - (N - k) = B + k + 1 by omega,
      show N - (N - k) = k by omega] at hcm
    rw [mul_comm, ← hcm, Nat.choose_symm_of_eq_add (by omega : N = (N - k) + k), mul_comm]
  rw [h1, h2, add_comm]
private theorem mod_two_quadratic_choose_sum_zero (L c d : ℕ) (hL : 1 ≤ L) :
    ∑ j ∈ range (L + 1),
      (L.choose j : ZMod 2) *
        ((2 * (j + c) * (j + c + 1) + d + L).choose L : ZMod 2) = 0 := by
  let k : ℕ := Nat.log 2 L
  have hk1 : 2 ^ k ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hk2 : L < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) L
  have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  let F : ℕ → ZMod 2 := fun j =>
    (L.choose j : ZMod 2) * ((2 * (j + c) * (j + c + 1) + d + L).choose L : ZMod 2)
  change ∑ j ∈ range (L + 1), F j = 0
  have hext : ∑ j ∈ range (L + 1), F j = ∑ j ∈ range (2 ^ k + 2 ^ k), F j := by
    symm
    rw [show 2 ^ k + 2 ^ k = (L + 1) + (2 ^ (k + 1) - (L + 1)) by omega,
      Finset.sum_range_add F (L + 1) (2 ^ (k + 1) - (L + 1))]
    have htail : ∑ x ∈ range (2 ^ (k + 1) - (L + 1)), F (L + 1 + x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      dsimp [F]
      rw [Nat.choose_eq_zero_of_lt (by omega : L < L + 1 + x), Nat.cast_zero, zero_mul]
    rw [htail, add_zero]
  rw [hext, Finset.sum_range_add F (2 ^ k) (2 ^ k), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt : j < 2 ^ k := Finset.mem_range.mp hj
  set R : ℕ := L - 2 ^ k
  have hR : R < 2 ^ k := by omega
  have hLR : L = 2 ^ k + R := by omega
  dsimp [F]
  have hf1 : (L.choose (2 ^ k + j) : ZMod 2) = (L.choose j : ZMod 2) := by
    have ha := choose_mul_prime_pow_add 2 1 k R 1 j hR hjlt
    have hb := choose_mul_prime_pow_add 2 1 k R 0 j hR hjlt
    simp only [one_mul, zero_mul, zero_add, Nat.choose_self, Nat.choose_zero_right,
      Nat.cast_one] at ha hb
    rw [hLR, ha, hb]
  have hf2 :
      ((2 * (2 ^ k + j + c) * (2 ^ k + j + c + 1) + d + L).choose L : ZMod 2) =
        ((2 * (j + c) * (j + c + 1) + d + L).choose L : ZMod 2) := by
    rw [show 2 * (2 ^ k + j + c) * (2 ^ k + j + c + 1) + d + L =
      (2 * (j + c) * (j + c + 1) + d + L) + (2 * (j + c) + 1 + 2 ^ k) * 2 ^ (k + 1) by
        rw [pow_succ]; ring]
    exact choose_add_mul_prime_pow 2 _ _ (k + 1) L hk2
  rw [hf1, hf2]
  have hchar : (2 : ZMod 2) = 0 := rfl
  linear_combination ((L.choose j : ZMod 2) *
    ((2 * (j + c) * (j + c + 1) + d + L).choose L : ZMod 2)) * hchar
private theorem coeffB_mod_two_succ_succ (N : ℕ) : (coeffB (N + 2) : ZMod 2) = 0 := by
  let n : ℕ := N + 1
  have hn : 1 ≤ n := by omega
  rw [show N + 2 = n + 1 from rfl, coeffB_eq]
  push_cast
  simp_rw [show ∀ k : ℕ, (-1 : ZMod 2) ^ k = 1 from fun k => by
    rw [show (-1 : ZMod 2) = 1 from rfl, one_pow], one_mul]
  rw [Finset.sum_range_succ']
  have h0 : (weight 0 : ZMod 2) * ((2 * 0 * (0 + 1) + (n + 1)).choose (n + 1 - 0) : ZMod 2) =
      ((n + 1).choose 0 : ZMod 2) * ((2 * 0 * (0 + 1) + (n + 1)).choose (n + 1) : ZMod 2) := by
    simp [weight]
  have hstep :
      (∑ k ∈ range (n + 1), (weight (k + 1) : ZMod 2) *
          ((2 * (k + 1) * (k + 1 + 1) + (n + 1)).choose (n + 1 - (k + 1)) : ZMod 2)) =
      (∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ZMod 2) *
          ((2 * (k + 1) * (k + 2) + (n + 1)).choose (n + 1) : ZMod 2)) +
      (∑ k ∈ range (n + 1), (n.choose k : ZMod 2) *
          ((2 * (k + 1) * (k + 2) + 1 + n).choose n : ZMod 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hws := congrArg (fun x : ℕ => (x : ZMod 2))
      (weight_choose_split n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    push_cast at hws
    rw [show (2 * ((k : ZMod 2) + 1) + 1) = 1 by
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add], one_mul] at hws
    simpa [Nat.succ_sub_succ_eq_sub, show k + 1 + 1 = k + 2 by omega] using hws
  rw [h0, hstep, add_comm _ ((n + 1).choose 0 * _ : ZMod 2), ← add_assoc]
  have hcomb :
      (((n + 1).choose 0 : ZMod 2) * ((2 * 0 * (0 + 1) + (n + 1)).choose (n + 1) : ZMod 2) +
        ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ZMod 2) *
          ((2 * (k + 1) * (k + 2) + (n + 1)).choose (n + 1) : ZMod 2)) =
      ∑ m ∈ range ((n + 1) + 1), ((n + 1).choose m : ZMod 2) *
        ((2 * (m + 0) * (m + 0 + 1) + 0 + (n + 1)).choose (n + 1) : ZMod 2) := by
    symm; rw [Finset.sum_range_succ', add_comm]; simp only [add_zero, zero_add]
  rw [hcomb, mod_two_quadratic_choose_sum_zero (n + 1) 0 0 (by omega), zero_add]
  simpa only [show ∀ k : ℕ, 2 * (k + 1) * (k + 2) = 2 * (k + 1) * (k + 1 + 1) from fun _ => rfl]
    using mod_two_quadratic_choose_sum_zero n 1 1 hn
private theorem seriesB_mod_two :
    seriesB.map (Int.castRingHom (ZMod 2)) = 1 + X := by
  ext n
  cases n with
  | zero => simp [seriesB, coeffB_zero]
  | succ m =>
    cases m with
    | zero => simp [seriesB, coeffB_one]
    | succ N =>
      change coeff (N + 2) (seriesB.map (Int.castRingHom (ZMod 2))) = coeff (N + 2) (1 + X)
      simp only [coeff_map, seriesB, coeff_mk, Int.coe_castRingHom, coeffB_mod_two_succ_succ N]
      simp [coeff_one, coeff_X, show N + 2 ≠ 1 by omega]
/-! ### Modulo 3 reduction: `seriesB ≡ (1 + X)⁻¹ + 2 X (mod 3)` -/
private theorem choose_three_mul_mod_three (r : ℕ) (hr : 1 ≤ r) (u : ℕ) :
    ((3 * r * u).choose r : ZMod 3) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
  cases u with
  | zero => simp
  | succ v =>
    let M : ℕ := 3 * k * v + 3 * k + 3 * v + 2
    have hM : M + 1 = 3 * (k + 1) * (v + 1) := by dsimp [M]; ring
    have hmul := Nat.add_one_mul_choose_eq M k
    rw [hM] at hmul
    have hdiv : (3 * (k + 1) * (v + 1)).choose (k + 1) = 3 * ((v + 1) * M.choose k) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos k)
      calc
        (3 * (k + 1) * (v + 1)).choose (k + 1) * (k + 1)
            = 3 * (k + 1) * (v + 1) * M.choose k := hmul.symm
        _ = 3 * ((v + 1) * M.choose k) * (k + 1) := by ring
    rw [hdiv, Nat.cast_mul, show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
private theorem weight_mod_three_eq_zero_of_mod_ne_one {m : ℕ}
    (hm : 1 ≤ m) (hmod : m % 3 ≠ 1) : (weight m : ZMod 3) = 0 := by
  have hcases : m % 3 = 0 ∨ m % 3 = 2 := by omega
  rcases hcases with hm0 | hm2
  · obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero hm0
    have hw := congrArg (fun x : ℕ => (x : ZMod 3)) (mul_weight (3 * r))
    have hodd : ((2 * (3 * r) + 1 : ℕ) : ZMod 3) = 1 := by
      rw [show 2 * (3 * r) + 1 = 3 * (2 * r) + 1 by ring]
      push_cast; have h3 : (3 : ZMod 3) = 0 := rfl; rw [h3, zero_mul, zero_add]
    rw [Nat.cast_mul, hodd, one_mul] at hw
    rw [hw, choose_prime_pow_decomp 3
      (show (3 * r + 1) * (2 * (3 * r) + 1) = (3 * r * (2 * r + 1)) * 3 ^ 1 + 1 by ring)
      (show 3 * r = r * 3 ^ 1 + 0 by ring) (by omega) (by omega),
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact choose_three_mul_mod_three r (by omega) (2 * r + 1)
  · set q : ℕ := m / 3
    have hq : m = 3 * q + 2 := by have := Nat.div_add_mod m 3; dsimp [q]; omega
    have hodd : ((2 * m + 1 : ℕ) : ZMod 3) = 2 := by
      rw [hq, show 2 * (3 * q + 2) + 1 = 3 * (2 * q + 1) + 2 by ring]
      push_cast; have h3 : (3 : ZMod 3) = 0 := rfl; rw [h3, zero_mul, zero_add]
    have hw := congrArg (fun x : ℕ => (x : ZMod 3)) (mul_weight m)
    rw [Nat.cast_mul, hodd, choose_prime_pow_decomp 3
      (show (m + 1) * (2 * m + 1) = ((q + 1) * (2 * m + 1)) * 3 ^ 1 + 0 by
        conv_lhs => arg 1; rw [hq]
        ring)
      (show m = q * 3 ^ 1 + 2 by omega) (by omega) (by omega),
      Nat.choose_eq_zero_of_lt (by omega : 0 < 2), Nat.cast_zero, mul_zero] at hw
    have h2 : (2 : ZMod 3) * 2 = 1 := by decide
    calc
      (weight m : ZMod 3) = ((2 : ZMod 3) * 2) * (weight m : ZMod 3) := by rw [h2, one_mul]
      _ = 2 * (2 * (weight m : ZMod 3)) := by ring
      _ = 0 := by rw [hw, mul_zero]
private theorem weight_three_mul_add_one_mod_three (M : ℕ) :
    (weight (3 * M + 1) : ZMod 3) =
      2 * ((6 * M * (M + 1) + 1 + M).choose M : ZMod 3) := by
  have hs := congrArg (fun x : ℕ => (x : ZMod 3)) (succ_mul_weight (3 * M))
  have h1 : ((3 * M + 1 : ℕ) : ZMod 3) = 1 := by
    push_cast; have h3 : (3 : ZMod 3) = 0 := rfl; rw [h3, zero_mul, zero_add]
  have h2 : ((3 * M + 2 : ℕ) : ZMod 3) = 2 := by
    push_cast; have h3 : (3 : ZMod 3) = 0 := rfl; rw [h3, zero_mul, zero_add]
  rw [Nat.cast_mul, Nat.cast_mul, h1, one_mul, h2] at hs
  rw [hs, choose_prime_pow_decomp 3
    (show 2 * (3 * M + 1) * (3 * M + 2) + 3 * M + 1 =
      (6 * M * (M + 1) + 1 + M) * 3 ^ 1 + 2 by ring)
    (show 3 * M = M * 3 ^ 1 + 0 by ring) (by omega) (by omega),
    Nat.choose_zero_right, Nat.cast_one, mul_one]
private theorem mod_three_quadratic_choose_sum_zero (N : ℕ) (hN : 1 ≤ N) :
    ∑ M ∈ range (N + 1),
      (-1 : ZMod 3) ^ (N - M) * (N.choose M : ZMod 3) *
        ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3) = 0 := by
  let k : ℕ := Nat.log 3 N
  have hk1 : 3 ^ k ≤ N := Nat.pow_log_le_self 3 (by omega)
  have hk2 : N < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) N
  let G : ℕ → ZMod 3 := fun M =>
    (-1 : ZMod 3) ^ (N + M) * (N.choose M : ZMod 3) *
      ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3)
  have hext :
      (∑ M ∈ range (N + 1),
        (-1 : ZMod 3) ^ (N - M) * (N.choose M : ZMod 3) *
          ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3)) =
      ∑ M ∈ range (2 * 3 ^ k + 3 ^ k), G M := by
    have hsign_eq :
        (∑ M ∈ range (N + 1),
          (-1 : ZMod 3) ^ (N - M) * (N.choose M : ZMod 3) *
            ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3)) =
        ∑ M ∈ range (N + 1), G M := by
      apply Finset.sum_congr rfl
      intro M hM
      have hMN : M ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
      dsimp [G]
      have hsq : (-1 : ZMod 3) ^ (2 * M) = 1 := by rw [pow_mul]; norm_num
      rw [show N + M = (N - M) + 2 * M by omega, pow_add, hsq, mul_one]
    rw [hsign_eq]
    symm
    rw [show 2 * 3 ^ k + 3 ^ k = (N + 1) + (3 ^ (k + 1) - (N + 1)) by rw [pow_succ]; omega,
      Finset.sum_range_add G (N + 1) (3 ^ (k + 1) - (N + 1))]
    have htail : ∑ x ∈ range (3 ^ (k + 1) - (N + 1)), G (N + 1 + x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      dsimp [G]
      rw [Nat.choose_eq_zero_of_lt (by omega : N < N + 1 + x), Nat.cast_zero, mul_zero, zero_mul]
    rw [htail, add_zero]
  rw [hext, Finset.sum_range_add G (2 * 3 ^ k) (3 ^ k),
    show 2 * 3 ^ k = 3 ^ k + 3 ^ k by omega,
    Finset.sum_range_add G (3 ^ k) (3 ^ k),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro M hM
  have hMlt : M < 3 ^ k := Finset.mem_range.mp hM
  set d : ℕ := N / 3 ^ k
  set R : ℕ := N % 3 ^ k
  have hR : R < 3 ^ k := Nat.mod_lt N (Nat.pos_of_ne_zero (pow_ne_zero k (by omega)))
  have hNR : N = d * 3 ^ k + R := by rw [mul_comm]; exact (Nat.div_add_mod N (3 ^ k)).symm
  have hd_cases : d = 1 ∨ d = 2 := by
    have hd1 : 1 ≤ d := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
    have hd2 : d < 3 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      (by simpa [pow_succ, mul_comm] using hk2)
    omega
  have hodd3k : (-1 : ZMod 3) ^ (3 ^ k) = -1 := Odd.neg_one_pow (Odd.pow (by decide : Odd 3))
  have hquad (j : ℕ) :
      ((6 * (j * 3 ^ k + M) * (j * 3 ^ k + M + 1) + 1 + N).choose N : ZMod 3) =
        ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3) := by
    rw [show 6 * (j * 3 ^ k + M) * (j * 3 ^ k + M + 1) + 1 + N =
      (6 * M * (M + 1) + 1 + N) + (2 * j * (j * 3 ^ k + 2 * M + 1)) * 3 ^ (k + 1) by
        rw [pow_succ]; ring]
    exact choose_add_mul_prime_pow 3 _ _ (k + 1) N hk2
  have hbin (j : ℕ) :
      (N.choose (j * 3 ^ k + M) : ZMod 3) = (d.choose j : ZMod 3) * (R.choose M : ZMod 3) :=
    choose_prime_pow_decomp 3 hNR rfl hR hMlt
  dsimp [G]
  have ht0 := hbin 0; have ht1 := hbin 1; have ht2 := hbin 2
  have hq1 := hquad 1; have hq2 := hquad 2
  simp only [zero_mul, zero_add, one_mul] at ht0 ht1 hq1
  rw [show 3 ^ k + 3 ^ k + M = 2 * 3 ^ k + M by omega, ht0, ht1, ht2, hq1, hq2]
  have hs1 : (-1 : ZMod 3) ^ (N + (3 ^ k + M)) = -((-1 : ZMod 3) ^ (N + M)) := by
    rw [show N + (3 ^ k + M) = (N + M) + 3 ^ k by omega, pow_add, hodd3k, mul_neg_one]
  have hs2 : (-1 : ZMod 3) ^ (N + (2 * 3 ^ k + M)) = (-1 : ZMod 3) ^ (N + M) := by
    rw [show N + (2 * 3 ^ k + M) = (N + M) + 3 ^ k + 3 ^ k by omega, pow_add, pow_add, hodd3k]
    ring
  rw [hs1, hs2]
  have hvanish : ((d.choose 0 : ZMod 3) - (d.choose 1 : ZMod 3) + (d.choose 2 : ZMod 3)) = 0 := by
    rcases hd_cases with hd | hd <;> rw [hd] <;> decide
  linear_combination ((-1 : ZMod 3) ^ (N + M) * (R.choose M : ZMod 3) *
    ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3)) * hvanish
private theorem sum_range_three_step {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (hf : ∀ k, (k + 1) % 3 ≠ 1 → f k = 0) (L : ℕ) :
    ∑ k ∈ range (3 * L + 1), f k = ∑ M ∈ range (L + 1), f (3 * M) := by
  induction L with
  | zero => simp
  | succ K ih =>
    rw [show 3 * (K + 1) + 1 = (3 * K + 1) + 1 + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      hf (3 * K + 1) (by omega), hf (3 * K + 1 + 1) (by omega), add_zero, add_zero,
      show 3 * K + 1 + 1 + 1 = 3 * (K + 1) by omega,
      Finset.sum_range_succ (fun M => f (3 * M)) (K + 1)]
private theorem coeffB_mod_three_tail_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n,
      (-1 : ZMod 3) ^ (n - (k + 1)) * (weight (k + 1) : ZMod 3) *
        ((2 * (k + 1) * (k + 2) + n).choose (n - (k + 1)) : ZMod 3) = 0 := by
  by_cases hn1 : n % 3 = 1
  · set N : ℕ := n / 3
    have hn_eq : n = 3 * N + 1 := by have := Nat.div_add_mod n 3; dsimp [N]; omega
    have hN : 1 ≤ N := by omega
    let term : ℕ → ZMod 3 := fun k =>
      (-1 : ZMod 3) ^ (n - (k + 1)) * (weight (k + 1) : ZMod 3) *
        ((2 * (k + 1) * (k + 2) + n).choose (n - (k + 1)) : ZMod 3)
    have hstep := sum_range_three_step term
      (fun k hk => by
        dsimp [term]
        rw [weight_mod_three_eq_zero_of_mod_ne_one (by omega) hk, mul_zero, zero_mul]) N
    change ∑ k ∈ range n, term k = 0
    rw [hn_eq, hstep]
    have hrewrite :
        (∑ M ∈ range (N + 1), term (3 * M)) =
          (2 : ZMod 3) * ∑ M ∈ range (N + 1),
            (-1 : ZMod 3) ^ (N - M) * (N.choose M : ZMod 3) *
              ((6 * M * (M + 1) + 1 + N).choose N : ZMod 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      have hMN : M ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
      dsimp [term]
      rw [hn_eq, show 3 * N + 1 - (3 * M + 1) = 3 * (N - M) by omega,
        weight_three_mul_add_one_mod_three M]
      have hsign : (-1 : ZMod 3) ^ (3 * (N - M)) = (-1 : ZMod 3) ^ (N - M) := by
        rw [pow_mul, show (-1 : ZMod 3) ^ 3 = -1 by decide]
      rw [hsign, choose_prime_pow_decomp 3
        (show 2 * (3 * M + 1) * (3 * M + 2) + (3 * N + 1) =
          (6 * M * (M + 1) + 1 + N) * 3 ^ 1 + 2 by ring)
        (show 3 * (N - M) = (N - M) * 3 ^ 1 + 0 by ring) (by omega) (by omega),
        Nat.choose_zero_right, Nat.cast_one, mul_one]
      have hcm := @Nat.choose_mul (6 * M * (M + 1) + 1 + N) N (N - M) (by omega)
      rw [show 6 * M * (M + 1) + 1 + N - (N - M) = 6 * M * (M + 1) + 1 + M by omega,
        show N - (N - M) = M by omega] at hcm
      have hprod :
          Nat.choose (6 * M * (M + 1) + 1 + M) M *
              Nat.choose (6 * M * (M + 1) + 1 + N) (N - M) =
            Nat.choose N M * Nat.choose (6 * M * (M + 1) + 1 + N) N := by
        rw [mul_comm, ← hcm, Nat.choose_symm_of_eq_add (by omega : N = (N - M) + M), mul_comm]
      have hprod3 := congrArg (fun x : ℕ => (x : ZMod 3)) hprod
      push_cast at hprod3
      linear_combination 2 * (-1 : ZMod 3) ^ (N - M) * hprod3
    rw [hrewrite, mod_three_quadratic_choose_sum_zero N hN, mul_zero]
  · apply Finset.sum_eq_zero
    intro k hk
    have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
    by_cases hkm : (k + 1) % 3 = 1
    · set M : ℕ := k / 3
      set Q : ℕ := n / 3
      have hk_eq : k + 1 = 3 * M + 1 := by have := Nat.div_add_mod k 3; dsimp [M]; omega
      have hk2_eq : k + 2 = 3 * M + 2 := by omega
      have hcases : n % 3 = 0 ∨ n % 3 = 2 := by omega
      rcases hcases with hn0 | hn2
      · have hn_eq : n = 3 * Q := by have := Nat.div_add_mod n 3; dsimp [Q]; omega
        rw [choose_prime_pow_decomp 3
          (show 2 * (k + 1) * (k + 2) + n = (6 * M * (M + 1) + 1 + Q) * 3 ^ 1 + 1 by
            rw [hk_eq, hk2_eq, hn_eq]; ring)
          (show n - (k + 1) = (Q - M - 1) * 3 ^ 1 + 2 by omega) (by omega) (by omega),
          Nat.choose_eq_zero_of_lt (by omega : 1 < 2), Nat.cast_zero, mul_zero, mul_zero]
      · have hn_eq : n = 3 * Q + 2 := by have := Nat.div_add_mod n 3; dsimp [Q]; omega
        rw [choose_prime_pow_decomp 3
          (show 2 * (k + 1) * (k + 2) + n = (6 * M * (M + 1) + 2 + Q) * 3 ^ 1 + 0 by
            rw [hk_eq, hk2_eq, hn_eq]; ring)
          (show n - (k + 1) = (Q - M) * 3 ^ 1 + 1 by omega) (by omega) (by omega),
          Nat.choose_eq_zero_of_lt (by omega : 0 < 1), Nat.cast_zero, mul_zero, mul_zero]
    · rw [weight_mod_three_eq_zero_of_mod_ne_one (by omega) hkm, mul_zero, zero_mul]
private theorem seriesB_mod_three :
    (seriesB - (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric + 2 * X)).map
        (Int.castRingHom (ZMod 3)) = 0 := by
  ext n
  rw [coeff_map, map_sub, map_add, seriesB, coeff_mk,
      D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric_coeff, map_zero,
      Int.coe_castRingHom]
  have h2x : coeff n (2 * X : PowerSeries ℤ) = if n = 1 then 2 else 0 := by
    rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C_mul, coeff_X]
    split_ifs <;> ring
  rw [h2x]
  cases n with
  | zero => simp [coeffB_zero]
  | succ m =>
    cases m with
    | zero =>
      change ((coeffB 1 - ((-1 : ℤ) ^ 1 + if (1 : ℕ) = 1 then 2 else 0) : ℤ) : ZMod 3) = 0
      rw [coeffB_one]
      decide
    | succ N =>
      have hne : N + 2 ≠ 1 := by omega
      change ((coeffB (N + 2) - ((-1 : ℤ) ^ (N + 2) + if N + 2 = 1 then 2 else 0) : ℤ) :
        ZMod 3) = 0
      simp only [hne, ↓reduceIte, add_zero, Int.cast_sub, sub_eq_zero]
      rw [coeffB_eq, Finset.sum_range_succ']
      push_cast
      have htail : ∑ k ∈ range (N + 2),
          (-1 : ZMod 3) ^ (N + 2 - (k + 1)) * (weight (k + 1) : ZMod 3) *
            ((2 * (k + 1) * (k + 1 + 1) + (N + 2)).choose (N + 2 - (k + 1)) : ZMod 3) = 0 :=
        coeffB_mod_three_tail_zero (N + 2) (by omega)
      simp only [Nat.succ_sub_succ_eq_sub] at htail
      rw [htail, zero_add]
      simp [weight]
/-! ### Deduction of all six conjectures (1)–(6) -/
private theorem catalan_cubic_linear_eq_Z :
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit + X ^ 2 *
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit ^ 3 = (2 - X) *
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1 := by
  linear_combination -(1 + X *
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit) * catalanZ_eq
private theorem hasSubst_qZ_map (p : ℕ) :
    HasSubst (qZ.map (Int.castRingHom (ZMod p))) := by
  have h0 : constantCoeff (qZ.map (Int.castRingHom (ZMod p))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      constantCoeff_qZ, map_zero]
  exact .of_constantCoeff_zero h0
private theorem seriesMod_two_eq : seriesMod 2 = catalanMod 2 := by
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  have hsq2 : HasSubst (qZ.map (Int.castRingHom (ZMod 2))) := hasSubst_qZ_map 2
  have hm : seriesMod 2 =
      (seriesB.map (Int.castRingHom (ZMod 2))).subst (qZ.map (Int.castRingHom (ZMod 2))) := by
    unfold seriesMod
    rw [seriesA_eq_subst]
    exact map_subst hsq seriesB
  rw [hm, seriesB_mod_two]
  have hq2 : qZ.map (Int.castRingHom (ZMod 2)) = catalanMod 2 - 1 := by
    unfold qZ catalanMod
    simp only [map_sub, map_one]
  have h1 : (1 : PowerSeries (ZMod 2)).subst (qZ.map (Int.castRingHom (ZMod 2))) = 1 := by
    rw [← coe_substAlgHom hsq2, map_one]
  rw [subst_add hsq2, h1, subst_X hsq2, hq2]
  ring
private theorem seriesMod_three_diff_zero :
    (seriesA - ((2 - X) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit -
        1)).map (Int.castRingHom (ZMod 3)) = 0 := by
  have hsq : HasSubst qZ := .of_constantCoeff_zero constantCoeff_qZ
  have hsq3 : HasSubst (qZ.map (Int.castRingHom (ZMod 3))) := hasSubst_qZ_map 3
  have hsub : (seriesB - (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric + 2 *
      X)).subst qZ = seriesA - ((2 - X) *
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1) := by
    have h2 : (2 : PowerSeries ℤ).subst qZ = 2 := by rw [← coe_substAlgHom hsq, map_ofNat]
    rw [subst_sub hsq, ← seriesA_eq_subst, subst_add hsq, geometric_subst_qZ,
      subst_mul hsq, h2, subst_X hsq, catalanInvZ_eq]
    unfold qZ; ring
  have hms : (PowerSeries.map (Int.castRingHom (ZMod 3)))
      ((seriesB - (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric + 2 * X)).subst qZ)
          =
      ((seriesB - (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric + 2 * X)).map
          (Int.castRingHom (ZMod 3))).subst
        (qZ.map (Int.castRingHom (ZMod 3))) := map_subst hsq (seriesB -
            (D5.S1.Recurrence.Bilateral.BilateralProductModFour.geometric + 2 * X))
  rw [← hsub, hms, seriesB_mod_three, ← coe_substAlgHom hsq3, map_zero]
private theorem seriesMod_three_eq_linear :
    seriesMod 3 = (2 - X) * catalanMod 3 - 1 := by
  have h := seriesMod_three_diff_zero
  simp only [map_sub, map_mul, map_ofNat, map_X, map_one] at h
  exact sub_eq_zero.mp h
private theorem catalanMod_cubic_eq_linear :
    catalanMod 3 + X ^ 2 * catalanMod 3 ^ 3 = (2 - X) * catalanMod 3 - 1 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) catalan_cubic_linear_eq_Z
  simpa only [catalanMod, map_add, map_sub, map_mul, map_pow, map_X, map_ofNat, map_one] using h
private theorem choose_two_mul_add_one_div (n : ℕ) :
    Nat.choose (2 * n + 1) n / (2 * n + 1) = catalan n := by
  have hmul : (2 * n + 1) * catalan n = Nat.choose (2 * n + 1) n := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 1)
    have h1 := Nat.add_one_mul_choose_eq (2 * n) n
    rw [Nat.choose_symm_half n] at h1
    have h2 : Nat.choose (2 * n) n = (n + 1) * catalan n := by
      simpa [Nat.centralBinom] using (succ_mul_catalan_eq_centralBinom n).symm
    calc
      ((2 * n + 1) * catalan n) * (n + 1) = (2 * n + 1) * ((n + 1) * catalan n) := by ring
      _ = (2 * n + 1) * Nat.choose (2 * n) n := by rw [h2]
      _ = Nat.choose (2 * n + 1) n * (n + 1) := h1
  rw [← hmul, Nat.mul_div_right _ (by omega : 0 < 2 * n + 1)]
private theorem raneyTerm_succ_succ_add_catalan (k : ℕ) :
    raneyTerm (k + 2) + catalan (k + 1) = catalan (k + 2) := by
  have hrec : (k + 3) * catalan (k + 2) = 2 * (2 * k + 3) * catalan (k + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 2)
    calc
      (k + 2) * ((k + 3) * catalan (k + 2))
          = (k + 2) * (k + 2).centralBinom := by rw [succ_mul_catalan_eq_centralBinom (k + 2)]
      _ = 2 * (2 * (k + 1) + 1) * (k + 1).centralBinom := Nat.succ_mul_centralBinom_succ (k + 1)
      _ = 2 * (2 * (k + 1) + 1) * ((k + 2) * catalan (k + 1)) := by
            rw [← succ_mul_catalan_eq_centralBinom (k + 1)]
      _ = (k + 2) * (2 * (2 * k + 3) * catalan (k + 1)) := by ring
  have hch1 : Nat.choose (2 * k + 2) k = (k + 1) * catalan (k + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 2)
    have hcent : Nat.choose (2 * k + 2) (k + 1) = (k + 2) * catalan (k + 1) := by
      simpa [Nat.centralBinom, show 2 * (k + 1) = 2 * k + 2 by omega] using
        (succ_mul_catalan_eq_centralBinom (k + 1)).symm
    calc
      (k + 2) * Nat.choose (2 * k + 2) k = Nat.choose (2 * k + 2) (k + 2) * (k + 2) := by
            rw [Nat.choose_symm_of_eq_add (by omega : 2 * k + 2 = k + (k + 2)), mul_comm]
      _ = (2 * k + 2) * Nat.choose (2 * k + 1) (k + 1) :=
            (Nat.add_one_mul_choose_eq (2 * k + 1) (k + 1)).symm
      _ = (2 * k + 2) * Nat.choose (2 * k + 1) k := by rw [Nat.choose_symm_half k]
      _ = Nat.choose (2 * k + 2) (k + 1) * (k + 1) := Nat.add_one_mul_choose_eq (2 * k + 1) k
      _ = (k + 2) * ((k + 1) * catalan (k + 1)) := by rw [hcent]; ring
  have hch2 : (k + 3) * Nat.choose (2 * k + 3) k = (2 * k + 3) * ((k + 1) * catalan (k + 1)) := by
    calc
      (k + 3) * Nat.choose (2 * k + 3) k = Nat.choose (2 * k + 3) (k + 3) * (k + 3) := by
            rw [Nat.choose_symm_of_eq_add (by omega : 2 * k + 3 = k + (k + 3)), mul_comm]
      _ = (2 * k + 3) * Nat.choose (2 * k + 2) (k + 2) :=
            (Nat.add_one_mul_choose_eq (2 * k + 2) (k + 2)).symm
      _ = (2 * k + 3) * ((k + 1) * catalan (k + 1)) := by
            rw [Nat.choose_symm_of_eq_add (by omega : 2 * k + 2 = (k + 2) + k), hch1]
  have hthree : 3 * Nat.choose (2 * k + 3) k + (2 * k + 3) * catalan (k + 1) =
      (2 * k + 3) * catalan (k + 2) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 3)
    calc
      (k + 3) * (3 * Nat.choose (2 * k + 3) k + (2 * k + 3) * catalan (k + 1))
          = 3 * ((k + 3) * Nat.choose (2 * k + 3) k) +
              (k + 3) * (2 * k + 3) * catalan (k + 1) := by ring
      _ = (2 * k + 3) * (2 * (2 * k + 3) * catalan (k + 1)) := by rw [hch2]; ring
      _ = (k + 3) * ((2 * k + 3) * catalan (k + 2)) := by rw [← hrec]; ring
  have hle : catalan (k + 1) ≤ catalan (k + 2) :=
    Nat.le_of_mul_le_mul_left (by omega : (2 * k + 3) * catalan (k + 1) ≤ _) (by omega)
  have hnum : 3 * Nat.choose (2 * k + 3) k =
      (2 * k + 3) * (catalan (k + 2) - catalan (k + 1)) := by
    rw [Nat.mul_sub_left_distrib]; omega
  have hnot : ¬ k + 2 < 2 := by omega
  have hr : raneyTerm (k + 2) = catalan (k + 2) - catalan (k + 1) := by
    unfold raneyTerm
    simp only [hnot, ↓reduceIte]
    rw [show 2 * (k + 2) - 1 = 2 * k + 3 by omega, show k + 2 - 2 = k by omega,
      hnum, Nat.mul_div_right _ (by omega : 0 < 2 * k + 3)]
  omega
private theorem coeff_linear_catalanZ (n : ℕ) :
    coeff n ((2 - X) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1) =
      (((Nat.choose (2 * n + 1) n / (2 * n + 1) : ℕ) : ℤ) + (raneyTerm n : ℤ)) := by
  rw [choose_two_mul_add_one_div]
  have expand : (2 - X) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1
      = C (2 : ℤ) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - X *
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1 := by
    rw [map_ofNat]; ring
  rw [expand, map_sub, map_sub, coeff_C_mul]
  cases n with
  | zero => simp [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit,
      catalan_zero, raneyTerm]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_one]
    simp only [Nat.succ_ne_zero m, ↓reduceIte, sub_zero]
    cases m with
    | zero => simp [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit,
        catalan_zero, catalan_one, raneyTerm]
    | succ k =>
      rw [show coeff (k + 2)
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit =
          (catalan (k + 2) : ℤ) by
            simp [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit],
        show coeff (k + 1)
          D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit =
            (catalan (k + 1) : ℤ) by
              simp [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit]]
      have hr := congrArg (fun x : ℕ => (x : ℤ)) (raneyTerm_succ_succ_add_catalan k)
      push_cast at hr
      linarith
/-- Proof of all six of Paul D. Hanna's numbered conjectures (1)–(6) for OEIS A352700. -/
theorem result : claim := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree.prime_power_subst 3
      (seriesMod 3)
  · exact seriesMod_three_eq_linear.trans catalanMod_cubic_eq_linear.symm
  · exact catalanMod_cubic_eq_linear
  · exact seriesMod_two_eq
  · intro n
    apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have h0 := congrArg (coeff n) seriesMod_three_diff_zero
    rw [coeff_map, map_zero, map_sub, coeff_linear_catalanZ, seriesA, coeff_mk,
      map_sub, sub_eq_zero, Int.coe_castRingHom] at h0
    exact h0
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have hc : coeff (m + 1) ((2 - X) *
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1) =
        2 * (catalan (m + 1) : ℤ) - (catalan m : ℤ) := by
      have expand : (2 - X) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit
          - 1 = C (2 : ℤ) * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit -
          X * D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit - 1 := by
        rw [map_ofNat]; ring
      rw [expand, map_sub, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_one]
      simp [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit]
    have h0 := congrArg (coeff (m + 1)) seriesMod_three_diff_zero
    rw [coeff_map, map_zero, map_sub, hc, seriesA, coeff_mk,
      map_sub, sub_eq_zero, Int.coe_castRingHom] at h0
    exact h0
  · intro n
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    have h := congrArg (coeff n) seriesMod_two_eq
    simpa [seriesMod, catalanMod, seriesA,
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit] using h
end D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences
