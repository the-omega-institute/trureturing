/- GID: D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/HannaLagrangeParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Triangular inversion determines Hanna's integral series and dyadic odd support. -/

/-
result:
  proof_shape: content (strong induction reconstructs the inverse coefficients)
  escape_witness: none
  admission_basis: open-problem-resolution (#18829; Proved)
Direct frozen dependencies:
  D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius
    declaration statement_id: sha256:c14027d96353cb11d580e4a417ec6f198feb0c6381ea739f21378160778c8d16
  D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius_zero
    declaration statement_id: sha256:2c75cbb4c50525e77c0a07cb812cb601ad1a36ba2d253fd08756244e890618c5
  D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius_denominator
    declaration statement_id: sha256:ea2185ba8a7b4378f0ccbba219bd7077c7c6c148eee12eb3493d263b4dddccd1
  D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.geometric_inverse
    declaration statement_id: sha256:9525f01e017fb1c9a0b2ce2b637f99278274ce4571130d1c72eb8cbcb336a1c8
  D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.diagonal_multiplier
    declaration statement_id: sha256:57e2e1c010c8d02b295cb9e2873e73fd1b159472dfb37446bd3cc3abc1774718
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.square_subst
    declaration statement_id: sha256:2a00cc0abc9161023b52344bca922b1fd191fc523d345719f2fda2aa737144b3
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.lacunary_coeff
    declaration statement_id: sha256:8c6dbdb9d439b678ca9d08177e32dbd8d3df06daf089e329a922c1c1c98b153b
  D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient
    declaration statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19951.
The source predicates retain their defining expressions. Mobius substitutions use
CompositionalIterateCongruence.mobius; normalized geometric factors use rescale and mk.
The statement is unbounded; no finite enumeration or computational certificate is used.
Declaration classifications (same-delivery helpers inlined; escape_witness: none):
  Core.AZ: proof_shape: bind-only; consumers: Core.AZ_constant, canonicalA, Core.X_AZ, canonical_reversion, Core.AZ_parity, canonicalA_constant, result.
  Core.AZ_constant: proof_shape: bind-only; consumers: canonicalA_constant.
  Core.AZ_parity: proof_shape: bind-only; consumers: result.
  Core.HZ: proof_shape: bind-only; consumers: Core.AZ_constant, Core.AZ, Core.X_AZ, canonical_reversion, Core.reversion, Core.mod_two_H, Core.AZ_parity, Core.HZ_one, Core.HZ_zero.
  Core.HZ_one: proof_shape: bind-only; consumers: Core.AZ_constant, Core.AZ_parity.
  Core.HZ_zero: proof_shape: bind-only; consumers: Core.X_AZ, canonical_reversion, Core.mod_two_H, Core.AZ_parity.
  Core.RZ: proof_shape: bind-only; consumers: canonicalR, Core.RZ_one, canonicalR_equation, canonical_reversion, Core.reversion, Core.mod_two_H, Core.mod_two_R, Core.HZ, Core.RZ_zero, Core.RZ_equation, Core.HZ_one, Core.HZ_zero.
  Core.RZ_equation: proof_shape: bind-only; consumers: canonicalR_equation, Core.mod_two_R.
  Core.RZ_one: proof_shape: bind-only; consumers: Core.HZ, Core.HZ_one, Core.HZ_zero, Core.reversion.
  Core.RZ_zero: proof_shape: bind-only; consumers: Core.reversion.
  Core.X_AZ: proof_shape: bind-only; consumers: canonical_reversion.
  Core.mod_two_H: proof_shape: bind-only; consumers: Core.AZ_parity.
  Core.mod_two_R: proof_shape: bind-only; consumers: Core.mod_two_H.
  Core.reversion: proof_shape: bind-only; consumers: canonical_reversion, Core.mod_two_H.
  IsGF: proof_shape: bind-only; consumers: solution_unique, canonicalA_isGF, claim, result.
  Lagrange.inversion_coefficient: proof_shape: bind-only; consumers: canonicalA_isGF.
  Mobius.diagonal_coefficient: proof_shape: bind-only; consumers: canonicalA_isGF.
  Mobius.geom_mul: proof_shape: bind-only; consumers: Mobius.geom_subst.
  Mobius.geom_square_coeff: proof_shape: bind-only; consumers: Mobius.diagonal_coefficient.
  Mobius.geom_subst: proof_shape: bind-only; consumers: Mobius.transformed_partial.
  Mobius.partial_fraction: proof_shape: bind-only; consumers: Mobius.transformed_partial.
  Mobius.subst_one: proof_shape: bind-only; consumers: Mobius.transformed_partial, shifted_reversion, Mobius.geom_subst.
  Mobius.subst_three: proof_shape: bind-only; consumers: Mobius.transformed_partial.
  Mobius.subst_two: proof_shape: bind-only; consumers: Mobius.transformed_partial.
  Mobius.transformed_partial: proof_shape: bind-only; consumers: Mobius.diagonal_coefficient.
  canonicalA: proof_shape: bind-only; consumers: canonical_reversion, canonicalA_isGF, canonicalA_constant, result.
  canonicalA_constant: proof_shape: bind-only; consumers: canonicalA_isGF.
  canonicalA_isGF: proof_shape: bind-only; consumers: result.
  canonicalR: proof_shape: bind-only; consumers: canonicalR_equation, canonical_reversion, canonicalA_isGF.
  canonicalR_equation: proof_shape: bind-only; consumers: canonicalA_isGF.
  canonical_reversion: proof_shape: bind-only; consumers: canonicalA_isGF.
  claim: proof_shape: bind-only; consumers: result.
  normalized_power: proof_shape: bind-only; consumers: solution_unique, canonicalA_isGF.
  result: proof_shape: content; consumers: settling result.
  shifted_reversion: proof_shape: bind-only; consumers: canonicalA_isGF.
  solution_unique: proof_shape: content; consumers: result.
-/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd

set_option autoImplicit false

namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity

open _root_.PowerSeries

/-- OEIS A365574: "Expansion of g.f. A(x) satisfying [x^(n-1)] (1 + (n+1)*x*A(x))^n / A(x)^n =
n*(n+2)^(n-2) for n > 1", offset 0, a(0) = 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    ∀ n : ℕ, 1 < n →
      coeff (n - 1) ((1 + C ((n : ℚ) + 1) * X * A) ^ n * (A ^ n)⁻¹) = (n : ℚ) * ((n : ℚ) + 2) ^ (n - 2)

/-- OEIS A365574 (P. D. Hanna), "Conjecture 1: a(k) is odd iff k = 2^n - 2 for n >= 1." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ k : ℕ, ∃ m : ℤ, coeff k A = m ∧ (Odd m ↔ ∃ n : ℕ, 1 ≤ n ∧ k = 2 ^ n - 2)

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity

set_option maxHeartbeats 800000
namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Lagrange
open _root_.PowerSeries

private theorem inversion_coefficient (a r : PowerSeries ℚ) (ha : constantCoeff a = 1)
    (hr : r.subst (X * a) = X) (n : ℕ) :
    (n + 1 : ℚ) * coeff (n + 1) r = coeff n (a⁻¹ ^ (n + 1)) := by
  let P : PowerSeries ℚ := X * a
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hP1 : IsUnit (coeff 1 P) := by
    change IsUnit (coeff (0 + 1) (X * a))
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff, ha]
    exact isUnit_one
  let q := P.substInvOfIsUnit hP1
  have hq : HasSubst q := HasSubst.substInvOfIsUnit P hP1
  have hPq : P.subst q = X := subst_substInvOfIsUnit_right P hP0 hP1
  have he : r = q := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst q) hr
    rw [subst_comp_subst_apply (.of_constantCoeff_zero hP0) hq, hPq, X_subst,
      subst_X hq] at h
    exact h
  have hr0 : constantCoeff r = 0 := by rw [he]; exact constantCoeff_substInvOfIsUnit P hP1
  have hrSub : HasSubst r := .of_constantCoeff_zero hr0
  have hback : (X * a).subst r = X := by rw [he]; exact hPq
  have hi := congrArg (substAlgHom hrSub)
    (PowerSeries.mul_inv_cancel a (by rw [ha]; norm_num))
  simp only [map_mul, map_one, coe_substAlgHom] at hi
  rw [subst_mul hrSub, subst_X hrSub] at hback
  have heq : r = X * a⁻¹.subst r := by
    linear_combination -r * hi + a⁻¹.subst r * hback
  have h := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
    r a⁻¹ hr0 heq (n + 1) 1 (by omega) (by omega)
  simpa only [pow_one, Nat.cast_one, one_mul, Nat.add_sub_cancel, Nat.cast_add] using h

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Lagrange
namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Mobius
open _root_.PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (mobius mobius_zero mobius_denominator)


private theorem subst_one (u : PowerSeries ℚ) : (1 : PowerSeries ℚ).subst u = 1 := by
  rw [← map_one (C (R := ℚ)), subst_C]
  rfl

private theorem subst_two (u : PowerSeries ℚ) : (2 : PowerSeries ℚ).subst u = 2 := by
  rw [← map_ofNat (C (R := ℚ)) 2, subst_C]
  rfl

private theorem subst_three (u : PowerSeries ℚ) : (3 : PowerSeries ℚ).subst u = 3 := by
  rw [← map_ofNat (C (R := ℚ)) 3, subst_C]
  rfl

private theorem geom_mul (b : ℚ) : rescale b (mk 1 : PowerSeries ℚ) * (1 - C b * X) = 1 :=
  D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.geometric_inverse b

private theorem geom_square_coeff (b : ℚ) (n : ℕ) : coeff n ((rescale b (mk 1 : PowerSeries ℚ)) ^ 2) = (n + 1 : ℚ) * b ^ n := by
  have h := congrArg (fun F : PowerSeries ℚ => coeff n (rescale b F))
    (mk_one_pow_eq_mk_choose_add (S := ℚ) (d := 1))
  simpa [map_pow, coeff_rescale, Nat.choose_one_right, add_comm, mul_comm] using h

private theorem geom_subst (b c : ℚ) :
    ((rescale b (mk 1 : PowerSeries ℚ))).subst (mobius c) = (1 - C c * X) * (rescale (c + b) (mk 1 : PowerSeries ℚ)) := by
  let U := mobius c
  let Z : PowerSeries ℚ := 1 - C c * X
  let P := (rescale (c + b) (mk 1 : PowerSeries ℚ))
  have hu : HasSubst U := .of_constantCoeff_zero (mobius_zero c)
  have hZ : U * Z = X := mobius_denominator c
  have hlin : (1 - C b * U) * Z = 1 - C (c + b) * X := by
    rw [map_add]
    dsimp only [Z]
    linear_combination -C b * hZ
  have hi : ((rescale b (mk 1 : PowerSeries ℚ))).subst U * (1 - C b * U) = 1 := by
    have h := congrArg (fun F : PowerSeries ℚ => F.subst U) (geom_mul b)
    have hC : (C b).subst U = C b := subst_C b
    simpa only [subst_mul hu, subst_sub hu, subst_one U, hC, subst_X hu] using h
  have hj : Z * P * (1 - C b * U) = 1 := by
    calc
      _ = P * ((1 - C b * U) * Z) := by ring
      _ = 1 := by rw [hlin]; exact geom_mul (c + b)
  change ((rescale b (mk 1 : PowerSeries ℚ))).subst U = Z * P
  linear_combination Z * P * hi - ((rescale b (mk 1 : PowerSeries ℚ))).subst U * hj

private theorem partial_fraction (r : PowerSeries ℚ)
    (hr : r * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) = X * (1 - 2 * X ^ 2 - 2 * X ^ 3)) :
    3 * r = X * ((1 - 2 * X) * (rescale 1 (mk 1 : PowerSeries ℚ)) ^ 2 + (2 + 2 * X) * (rescale (-2) (mk 1 : PowerSeries ℚ)) ^ 2) := by
  have hD : IsUnit ((1 - X : PowerSeries ℚ) ^ 2 * (1 + 2 * X) ^ 2) := by
    rw [isUnit_iff_constantCoeff]
    norm_num
  have h1s : (rescale 1 (mk 1 : PowerSeries ℚ)) ^ 2 * (1 - X) ^ 2 = 1 := by
    have h := congrArg (rescale (1 : ℚ))
      (mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 1))
    rw [← mk_one_pow_eq_mk_choose_add] at h
    simpa [map_pow, rescale_X] using h
  have h2s : (rescale (-2) (mk 1 : PowerSeries ℚ)) ^ 2 * (1 + 2 * X) ^ 2 = 1 := by
    have h := congrArg (rescale (-2 : ℚ))
      (mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 1))
    rw [← mk_one_pow_eq_mk_choose_add] at h
    simpa [map_pow, rescale_X, map_ofNat] using h
  apply hD.mul_left_cancel
  calc
    ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) * (3 * r) =
      3 * (r * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2)) := by ring
    _ = 3 * (X * (1 - 2 * X ^ 2 - 2 * X ^ 3)) := by rw [hr]
    _ = X * ((1 - 2 * X) * (1 + 2 * X) ^ 2 + (2 + 2 * X) * (1 - X) ^ 2) := by ring
    _ = X * ((1 - 2 * X) * ((rescale 1 (mk 1 : PowerSeries ℚ)) ^ 2 * (1 - X) ^ 2) * (1 + 2 * X) ^ 2 +
      (2 + 2 * X) * ((rescale (-2) (mk 1 : PowerSeries ℚ)) ^ 2 * (1 + 2 * X) ^ 2) * (1 - X) ^ 2) := by rw [h1s, h2s]; ring
    _ = _ := by ring

private theorem transformed_partial (r : PowerSeries ℚ)
    (hr : r * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) = X * (1 - 2 * X ^ 2 - 2 * X ^ 3))
    (c : ℚ) :
    3 * r.subst (mobius c) = X * ((1 - C (c + 2) * X) * (rescale (c + 1) (mk 1 : PowerSeries ℚ)) ^ 2 +
      2 * (1 - C (c - 1) * X) * (rescale (c - 2) (mk 1 : PowerSeries ℚ)) ^ 2) := by
  let U := mobius c
  let Z : PowerSeries ℚ := 1 - C c * X
  have hu : HasSubst U := .of_constantCoeff_zero (mobius_zero c)
  have hZ : U * Z = X := mobius_denominator c
  have hlin1 : (1 - 2 * U) * Z = 1 - C (c + 2) * X := by
    simp only [map_add, map_ofNat]
    dsimp only [Z]
    linear_combination -2 * hZ
  have hlin2 : (2 + 2 * U) * Z = 2 * (1 - C (c - 1) * X) := by
    simp only [map_sub, map_one]
    dsimp only [Z]
    linear_combination 2 * hZ
  have h := congrArg (fun F : PowerSeries ℚ => F.subst U) (partial_fraction r hr)
  simp only [subst_mul hu, subst_add hu, subst_sub hu, subst_one U, subst_two U, subst_three U,
    subst_pow hu, subst_X hu] at h
  have hg1 : ((rescale 1 (mk 1 : PowerSeries ℚ))).subst U = Z * (rescale (c + 1) (mk 1 : PowerSeries ℚ)) := geom_subst 1 c
  have hg2 : ((rescale (-2) (mk 1 : PowerSeries ℚ))).subst U = Z * (rescale (c - 2) (mk 1 : PowerSeries ℚ)) := by
    dsimp only [U, Z]
    simpa only [sub_eq_add_neg] using geom_subst (-2) c
  rw [hg1, hg2] at h
  change 3 * r.subst U = _
  calc
    3 * r.subst U = U * ((1 - 2 * U) * (Z * (rescale (c + 1) (mk 1 : PowerSeries ℚ))) ^ 2 +
      (2 + 2 * U) * (Z * (rescale (c - 2) (mk 1 : PowerSeries ℚ))) ^ 2) := h
    _ = (U * Z) * (((1 - 2 * U) * Z) * (rescale (c + 1) (mk 1 : PowerSeries ℚ)) ^ 2 +
      ((2 + 2 * U) * Z) * (rescale (c - 2) (mk 1 : PowerSeries ℚ)) ^ 2) := by ring
    _ = _ := by rw [hZ, hlin1, hlin2]

private theorem diagonal_coefficient (r : PowerSeries ℚ)
    (hr : r * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) = X * (1 - 2 * X ^ 2 - 2 * X ^ 3))
    (m : ℕ) : coeff (m + 2) (r.subst (mobius (m + 3 : ℚ))) = (m + 4 : ℚ) ^ m := by
  have h := congrArg (coeff (m + 2)) (transformed_partial r hr (m + 3))
  rw [coeff_ofNat_mul, show m + 2 = (m + 1) + 1 by omega, coeff_succ_X_mul] at h
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_ofNat_mul, coeff_succ_X_mul, geom_square_coeff] at h
  have hp1 : (m + 3 : ℚ) + 1 = m + 4 := by ring
  have hp2 : (m + 3 : ℚ) - 2 = m + 1 := by ring
  rw [hp1, hp2, pow_succ, pow_succ] at h
  push_cast at h
  linarith

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Mobius
namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core
open _root_.PowerSeries

private noncomputable def RZ : PowerSeries ℤ :=
  X * (1 - 2 * X ^ 2 - 2 * X ^ 3) *
    invOfUnit ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) 1

private theorem RZ_zero : constantCoeff RZ = 0 := by simp [RZ]
private theorem RZ_one : coeff 1 RZ = 1 := by
  simpa only [RZ, mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff] using
    (show constantCoeff ((1 - 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℤ) *
      invOfUnit ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) 1) = 1 by simp)

private theorem RZ_equation : RZ * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) =
    X * (1 - 2 * X ^ 2 - 2 * X ^ 3) := by
  rw [RZ, mul_assoc, invOfUnit_mul _ _ (by simp), mul_one]

private noncomputable def HZ : PowerSeries ℤ := RZ.substInvOfIsUnit (RZ_one ▸ isUnit_one)
private noncomputable def AZ : PowerSeries ℤ := mk fun n => coeff (n + 1) HZ

private theorem HZ_zero : constantCoeff HZ = 0 := constantCoeff_substInvOfIsUnit _ _
private theorem HZ_one : coeff 1 HZ = 1 := by
  rw [HZ, coeff_one_substInvOfIsUnit]
  change ((IsUnit.unit (RZ_one ▸ isUnit_one))⁻¹ : ℤˣ).val = 1
  have hu : (IsUnit.unit (RZ_one ▸ isUnit_one) : ℤ) = 1 :=
    (IsUnit.unit_spec _).trans RZ_one
  have he : IsUnit.unit (RZ_one ▸ isUnit_one) = 1 := Units.ext hu
  rw [he]
  simp

private theorem AZ_constant : constantCoeff AZ = 1 := by
  simpa only [AZ, constantCoeff_mk, zero_add] using HZ_one

private theorem X_AZ : X * AZ = HZ := by
  have h := sub_const_eq_X_mul_shift HZ
  simpa only [HZ_zero, map_zero, sub_zero, AZ] using h.symm

private theorem reversion : RZ.subst HZ = X :=
  subst_substInvOfIsUnit_right RZ RZ_zero _

open D5.S1.Recurrence.Invariants.UnitReversionSquareParity (lacunary_coeff square_subst)

private theorem mod_two_R : RZ.map (Int.castRingHom (ZMod 2)) * (1 + X ^ 2) = X := by
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) RZ_equation
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 from CharP.cast_eq_zero (ZMod 2) 2)
  have hm : (1 - X : PowerSeries (ZMod 2)) ^ 2 = 1 + X ^ 2 := by
    linear_combination -X * htwo
  simpa only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, map_X, htwo,
    zero_mul, sub_zero, add_zero, one_pow, mul_one, hm] using h

private theorem mod_two_H : HZ.map (Int.castRingHom (ZMod 2)) =
    X * (1 + HZ.map (Int.castRingHom (ZMod 2)) ^ 2) := by
  let hom := Int.castRingHom (ZMod 2)
  let H := HZ.map hom
  have hz : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, HZ_zero, map_zero]
  have hr : (RZ.map hom).subst H = X := by
    have hh := congrArg (PowerSeries.map hom) reversion
    change (MvPowerSeries.map hom) (RZ.subst HZ) = (map hom) X at hh
    rw [PowerSeries.map_subst (.of_constantCoeff_zero HZ_zero), map_X] at hh
    exact hh
  have h := congrArg (fun F : PowerSeries (ZMod 2) => F.subst H) mod_two_R
  rw [subst_mul (.of_constantCoeff_zero hz), hr, subst_add (.of_constantCoeff_zero hz),
    (show (1 : PowerSeries (ZMod 2)).subst H = 1 by
      rw [← map_one (C (R := ZMod 2)), subst_C]; exact map_one _), subst_pow (.of_constantCoeff_zero hz), subst_X (.of_constantCoeff_zero hz)] at h
  exact h.symm

private theorem AZ_parity (k : ℕ) : Odd (coeff k AZ) ↔
    ∃ n : ℕ, 1 ≤ n ∧ k = 2 ^ n - 2 := by
  let H := HZ.map (Int.castRingHom (ZMod 2))
  have h0 : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, HZ_zero, map_zero]
  have h1 : coeff 1 H = 1 := by simp [H, coeff_map, HZ_one]
  have hf : H = X + X * H.subst (X ^ 2) := by
    rw [← square_subst]
    simpa only [mul_add, mul_one] using mod_two_H
  have hc := lacunary_coeff H h0 h1 hf (k + 1)
  have hm : ((coeff k AZ : ℤ) : ZMod 2) = coeff (k + 1) H := by simp [AZ, H, coeff_map]
  rw [← ZMod.intCast_eq_one_iff_odd, hm, hc]
  constructor
  · rintro ⟨n, hn, he⟩
    exact ⟨n, hn, by omega⟩
  · rintro ⟨n, hn, he⟩
    have hp : 2 ≤ 2 ^ n := by
      have h := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hn
      simpa using h
    exact ⟨n, hn, by omega⟩

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core

namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity
open _root_.PowerSeries
open D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd (diagonal_multiplier)

private theorem normalized_power (A : PowerSeries ℚ) (hA : constantCoeff A = 1)
    (c : ℚ) (n : ℕ) :
    (1 + C c * X * A) ^ n * (A ^ n)⁻¹ = (A⁻¹ + C c * X) ^ n := by
  have hi : A * A⁻¹ = 1 := PowerSeries.mul_inv_cancel A (by rw [hA]; norm_num)
  rw [← PowerSeries.inv_pow, ← mul_pow]
  congr 1
  calc
    (1 + C c * X * A) * A⁻¹ = A⁻¹ + C c * X * (A * A⁻¹) := by ring
    _ = _ := by rw [hi]; ring

private theorem solution_unique (A B : PowerSeries ℚ) (hA : IsGF A) (hB : IsGF B) : A = B := by
  have h0A : constantCoeff A⁻¹ = 1 := by rw [constantCoeff_inv, hA.1]; norm_num
  have h0B : constantCoeff B⁻¹ = 1 := by rw [constantCoeff_inv, hB.1]; norm_num
  have hinv : A⁻¹ = B⁻¹ := by
    ext d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      by_cases hd : d = 0
      · subst d; simpa only [coeff_zero_eq_constantCoeff] using h0A.trans h0B.symm
      let c : ℚ := ((d + 1 : ℕ) : ℚ) + 1
      have hpref : ∀ k < d, coeff k (A⁻¹ + C c * X) = coeff k (B⁻¹ + C c * X) := by
        intro k hk
        simp only [map_add, ih k hk]
      have ha0 : constantCoeff (A⁻¹ + C c * X) = 1 := by simp [h0A]
      have hb0 : constantCoeff (B⁻¹ + C c * X) = 1 := by simp [h0B]
      have hdiag := diagonal_multiplier ha0 hb0 hpref (d + 1)
      have he : coeff d ((A⁻¹ + C c * X) ^ (d + 1)) =
          coeff d ((B⁻¹ + C c * X) ^ (d + 1)) := by
        have ha := hA.2 (d + 1) (by omega)
        have hb := hB.2 (d + 1) (by omega)
        rw [normalized_power A hA.1] at ha
        rw [normalized_power B hB.1] at hb
        simpa only [Nat.add_sub_cancel, c] using ha.trans hb.symm
      have hn : (d + 1 : ℚ) ≠ 0 := by positivity
      have hz : (d + 1 : ℚ) * (coeff d A⁻¹ - coeff d B⁻¹) = 0 := by
        simp only [map_add, Nat.cast_add, Nat.cast_one] at hdiag
        linear_combination -hdiag + he
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  have hu : IsUnit B⁻¹ := isUnit_iff_constantCoeff.mpr (h0B ▸ isUnit_one)
  apply hu.mul_right_cancel
  have ha := PowerSeries.mul_inv_cancel A (by rw [hA.1]; norm_num)
  have hb := PowerSeries.mul_inv_cancel B (by rw [hB.1]; norm_num)
  rw [hinv] at ha
  exact ha.trans hb.symm

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity
namespace D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity
open _root_.PowerSeries
open D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Mobius
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (mobius mobius_zero mobius_denominator)

private noncomputable def canonicalA : PowerSeries ℚ :=
  D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.AZ.map (Int.castRingHom ℚ)
private noncomputable def canonicalR : PowerSeries ℚ :=
  D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.RZ.map (Int.castRingHom ℚ)

private theorem canonicalA_constant : constantCoeff canonicalA = 1 := by
  rw [canonicalA, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.AZ_constant, map_one]

private theorem canonicalR_equation :
    canonicalR * ((1 - X) ^ 2 * (1 + 2 * X) ^ 2) = X * (1 - 2 * X ^ 2 - 2 * X ^ 3) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.RZ_equation
  simpa only [_root_.map_mul, _root_.map_pow, _root_.map_sub, _root_.map_add,
    _root_.map_one, _root_.map_ofNat, map_X, canonicalR] using h

private theorem canonical_reversion : canonicalR.subst (X * canonicalA) = X := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.reversion
  change (MvPowerSeries.map (Int.castRingHom ℚ))
    (D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.RZ.subst D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.HZ) = _ at h
  rw [PowerSeries.map_subst (.of_constantCoeff_zero D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.HZ_zero), map_X] at h
  have hh := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.X_AZ
  rw [_root_.map_mul, map_X] at hh
  change (D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.RZ.map (Int.castRingHom ℚ)).subst
    (D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.HZ.map (Int.castRingHom ℚ)) = X at h
  rw [← hh] at h
  exact h

private theorem shifted_reversion (A r : PowerSeries ℚ) (hA : constantCoeff A = 1)
    (hr : r.subst (X * A) = X) (c : ℚ) :
    PowerSeries.subst (X * (A⁻¹ + C c * X)⁻¹ : PowerSeries ℚ)
      (r.subst (mobius c)) = (X : PowerSeries ℚ) := by
  let F := A⁻¹ + C c * X
  let v := X * F⁻¹
  have hF : constantCoeff F = 1 := by simp [F, constantCoeff_inv, hA]
  have hv : constantCoeff v = 0 := by simp [v]
  have hi := PowerSeries.mul_inv_cancel F (by rw [hF]; norm_num)
  have hAi := PowerSeries.mul_inv_cancel A (by rw [hA]; norm_num)
  have hs : (mobius c).subst v * (1 - C c * v) = v := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst v)
      (show mobius c * (1 - C c * X) = X from mobius_denominator c)
    have hC : (C c).subst v = C c := subst_C c
    simpa only [subst_mul (.of_constantCoeff_zero hv), subst_sub (.of_constantCoeff_zero hv),
      subst_one v, hC, subst_X (.of_constantCoeff_zero hv)] using h
  have hH : (X * A) * (1 - C c * v) = v := by
    dsimp only [v, F] at hi ⊢
    linear_combination -(X * A) * hi + (X * (A⁻¹ + C c * X)⁻¹) * hAi
  have hu : IsUnit (1 - C c * v) := by rw [isUnit_iff_constantCoeff]; simp [hv]
  have he : (mobius c).subst v = X * A := hu.mul_right_cancel (hs.trans hH.symm)
  rw [subst_comp_subst_apply (.of_constantCoeff_zero (mobius_zero c))
    (.of_constantCoeff_zero hv), he, hr]

private theorem canonicalA_isGF : IsGF canonicalA := by
  refine ⟨canonicalA_constant, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let F : PowerSeries ℚ := canonicalA⁻¹ + C ((m + 2 : ℚ) + 1) * X
  have hF : constantCoeff F = 1 := by simp [F, constantCoeff_inv, canonicalA_constant]
  have hFi : constantCoeff F⁻¹ = 1 := by rw [constantCoeff_inv, hF]; norm_num
  have hii : F⁻¹⁻¹ = F :=
    (inv_eq_iff_mul_eq_one (by rw [hFi]; norm_num)).mpr
      (PowerSeries.mul_inv_cancel F (by rw [hF]; norm_num))
  have hr : PowerSeries.subst (X * F⁻¹ : PowerSeries ℚ)
      (canonicalR.subst (mobius ((m + 2 : ℚ) + 1))) = (X : PowerSeries ℚ) :=
    shifted_reversion canonicalA canonicalR canonicalA_constant canonical_reversion _
  have hLag := D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Lagrange.inversion_coefficient F⁻¹
    (canonicalR.subst (mobius ((m + 2 : ℚ) + 1))) hFi hr (m + 1)
  rw [hii] at hLag
  rw [normalized_power canonicalA canonicalA_constant]
  have hc := D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Mobius.diagonal_coefficient canonicalR canonicalR_equation m
  have hcc : (m + 2 : ℚ) + 1 = m + 3 := by ring
  simp only [Nat.cast_add, Nat.cast_ofNat, show m + 2 - 1 = m + 1 by omega]
  change coeff (m + 1) (F ^ (m + 2)) = (m + 2 : ℚ) * ((m + 2 : ℚ) + 2) ^ m
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hcc,
    show (m + 1 + 1 : ℕ) = m + 2 by omega,
    show (m + 1 : ℚ) + 1 = m + 2 by ring,
    show (m + 2 : ℚ) + 2 = m + 4 by ring, hc] using hLag.symm

theorem result : claim := by
  refine ⟨⟨canonicalA, canonicalA_isGF⟩, ?_⟩
  intro A hA k
  have he : A = canonicalA := solution_unique A canonicalA hA canonicalA_isGF
  refine ⟨coeff k D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.AZ, ?_, D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.Core.AZ_parity k⟩
  rw [he]
  exact coeff_map _ _ _

end D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity
