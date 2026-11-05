/- GID: D5/S3/Arith/ModularForms/CubicThetaOddParity
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaOddParity
   mirror-E: none(waiver:integral-odd-euler-dissection)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: consumer=D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four
   digest: Integral odd four-dissection of the actual three-core Euler quotient.
-/

import D5.S3.Arith.ModularForms.CubicThetaCoreProduct
import Mathlib.Tactic.IntervalCases

/-! The affine parity correspondence is proved on the complete integer core lattice,
then consumed by the exact Euler quotient supplied by `CubicThetaCoreProduct`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaOddParity

open D5.S3.Arith.ModularForms.CubicThetaLattice
open D5.S3.Arith.ModularForms.CubicThetaCoreProduct

private def oddAffine (p : ℤ × ℤ) : ℤ × ℤ := (1 - 2 * p.1, -2 * p.2)

private theorem core_exponent_mod_four_one (p : ℤ × ℤ) :
    coreExponent p % 4 = 1 ↔ p.1 % 2 = 1 ∧ p.2 % 2 = 0 := by
  have hx0 := Int.emod_nonneg p.1 (by norm_num : (4 : ℤ) ≠ 0)
  have hx4 := Int.emod_lt_of_pos p.1 (by norm_num : (0 : ℤ) < 4)
  have hy0 := Int.emod_nonneg p.2 (by norm_num : (4 : ℤ) ≠ 0)
  have hy4 := Int.emod_lt_of_pos p.2 (by norm_num : (0 : ℤ) < 4)
  interval_cases hx : p.1 % 4 <;> interval_cases hy : p.2 % 4 <;>
    norm_num [coreExponent, eisensteinNorm, pow_two, Int.add_emod, Int.mul_emod,
      Int.sub_emod, hx, hy] <;> omega

private theorem core_exponent_mod_four_ne_three (p : ℤ × ℤ) :
    coreExponent p % 4 ≠ 3 := by
  have hx0 := Int.emod_nonneg p.1 (by norm_num : (4 : ℤ) ≠ 0)
  have hx4 := Int.emod_lt_of_pos p.1 (by norm_num : (0 : ℤ) < 4)
  have hy0 := Int.emod_nonneg p.2 (by norm_num : (4 : ℤ) ≠ 0)
  have hy4 := Int.emod_lt_of_pos p.2 (by norm_num : (0 : ℤ) < 4)
  interval_cases hx : p.1 % 4 <;> interval_cases hy : p.2 % 4 <;>
    norm_num [coreExponent, eisensteinNorm, pow_two, Int.add_emod, Int.mul_emod,
      Int.sub_emod, hx, hy] <;> omega

private theorem core_exponent_odd_affine (p : ℤ × ℤ) :
    coreExponent (oddAffine p) = 4 * coreExponent p + 1 := by
  dsimp [oddAffine, coreExponent, eisensteinNorm]
  ring

private theorem odd_affine_inverse (p : ℤ × ℤ)
    (hx : p.1 % 2 = 1) (hy : p.2 % 2 = 0) :
    oddAffine ((1 - p.1) / 2, -p.2 / 2) = p := by
  apply Prod.ext <;> dsimp [oddAffine] <;> omega

noncomputable def coreOddEquiv (n : ℕ) :
    CoreFiber n ≃ CoreFiber (4 * n + 1) where
  toFun p := ⟨oddAffine p.1, by
    rw [core_exponent_odd_affine, p.2]
    push_cast
    rfl⟩
  invFun p :=
    let q := ((1 - p.1.1) / 2, -p.1.2 / 2)
    ⟨q, by
      have hm : coreExponent p.1 % 4 = 1 := by
        rw [p.2]
        push_cast
        norm_num
      have hpar := (core_exponent_mod_four_one p.1).mp hm
      have hi := odd_affine_inverse p.1 hpar.1 hpar.2
      have he := core_exponent_odd_affine
        ((1 - p.1.1) / 2, -p.1.2 / 2)
      rw [hi, p.2] at he
      push_cast at he
      change coreExponent ((1 - p.1.1) / 2, -p.1.2 / 2) = _
      omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp [oddAffine] <;> omega
  right_inv p := by
    apply Subtype.ext
    have hm : coreExponent p.1 % 4 = 1 := by
      rw [p.2]
      push_cast
      norm_num
    have hpar := (core_exponent_mod_four_one p.1).mp hm
    exact odd_affine_inverse p.1 hpar.1 hpar.2

private theorem core_fiber_four_mul_add_one_card (n : ℕ) :
    Nat.card (CoreFiber (4 * n + 1)) = Nat.card (CoreFiber n) := by
  exact (Nat.card_congr (coreOddEquiv n)).symm

private theorem core_fiber_four_mul_add_three_empty (n : ℕ) :
    IsEmpty (CoreFiber (4 * n + 3)) := by
  letI : IsEmpty (CoreFiber (4 * n + 3)) := ⟨by
    intro p
    have hm := core_exponent_mod_four_ne_three p.1
    rw [p.2] at hm
    push_cast at hm
    norm_num at hm⟩
  exact inferInstance

private theorem core_product_coeff_mod_four (n : ℕ) :
    PowerSeries.coeff (4 * n + 1)
        ((PowerSeries.expand 3 (by decide)
          (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
          PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) =
      PowerSeries.coeff n
        ((PowerSeries.expand 3 (by decide)
          (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
          PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) ∧
    PowerSeries.coeff (4 * n + 3)
        ((PowerSeries.expand 3 (by decide)
          (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
          PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) = 0 := by
  constructor
  · rw [coeff_core_product, coeff_core_product]
    exact_mod_cast core_fiber_four_mul_add_one_card n
  · rw [coeff_core_product]
    have h := core_fiber_four_mul_add_three_empty n
    exact_mod_cast (Nat.card_of_isEmpty : Nat.card (CoreFiber (4 * n + 3)) = 0)

private noncomputable abbrev f1 : PowerSeries ℤ := PowerSeries.pentagonalSeries ℤ

private noncomputable abbrev f3 : PowerSeries ℤ :=
  PowerSeries.expand 3 (by decide) f1

noncomputable def integralT : PowerSeries ℤ :=
  f3 ^ 3 * PowerSeries.invOfUnit f1 1

private theorem f1_map :
    PowerSeries.map (Int.castRingHom ℚ) f1 = PowerSeries.pentagonalSeries ℚ := by
  exact map_pentagonal (Int.castRingHom ℚ)

private theorem f3_map :
    PowerSeries.map (Int.castRingHom ℚ) f3 =
      PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℚ) := by
  rw [f3, PowerSeries.map_expand, f1_map]

private theorem f1_constant_one : PowerSeries.constantCoeff f1 = 1 := by
  change PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℤ) = 1
  calc
    _ = PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℤ) :=
      (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
    _ = 1 := by
      have h := PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0
      rw [show _root_.pentagonal (0 : ℤ) = 0 by decide] at h
      simpa only [Int.coe_negOnePow, Int.natAbs_zero, pow_zero] using h

private theorem map_invOfUnit_f1 :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit f1 1) =
      PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
  have hz := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    (PowerSeries.mul_invOfUnit f1 1 f1_constant_one)
  simp only [map_mul, map_one, f1_map] at hz
  have hq := PowerSeries.mul_invOfUnit (PowerSeries.pentagonalSeries ℚ) 1
    CubicThetaCoreProduct.euler_constant_one
  have hq' : PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 *
      PowerSeries.pentagonalSeries ℚ = 1 := by
    rw [mul_comm, hq]
  calc
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit f1 1) =
        1 * PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit f1 1) := by rw [one_mul]
    _ = (PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 *
        PowerSeries.pentagonalSeries ℚ) *
        PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit f1 1) := by
      rw [hq', one_mul]
    _ = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 *
        (PowerSeries.pentagonalSeries ℚ *
          PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit f1 1)) := by ring
    _ = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 * 1 := by rw [hz]
    _ = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by rw [mul_one]

private theorem integralT_map :
    PowerSeries.map (Int.castRingHom ℚ) integralT =
      (PowerSeries.expand 3 (by decide)
        (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
        PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
  rw [integralT, map_mul, map_pow, f3_map, map_invOfUnit_f1]

theorem integralT_coeff_mod_four (n : ℕ) :
    PowerSeries.coeff (4 * n + 1) integralT = PowerSeries.coeff n integralT ∧
    PowerSeries.coeff (4 * n + 3) integralT = 0 := by
  have hq := core_product_coeff_mod_four n
  have hmap1 := congrArg (fun F : PowerSeries ℚ =>
      PowerSeries.coeff (4 * n + 1) F) integralT_map
  have hmapn := congrArg (fun F : PowerSeries ℚ =>
      PowerSeries.coeff n F) integralT_map
  have hmap3 := congrArg (fun F : PowerSeries ℚ =>
      PowerSeries.coeff (4 * n + 3) F) integralT_map
  constructor
  · have hc : ((PowerSeries.coeff (4 * n + 1) integralT : ℤ) : ℚ) =
        ((PowerSeries.coeff n integralT : ℤ) : ℚ) := by
      rw [PowerSeries.coeff_map] at hmap1 hmapn
      exact hmap1.trans (hq.1.trans hmapn.symm)
    exact Int.cast_injective hc
  · have hc : ((PowerSeries.coeff (4 * n + 3) integralT : ℤ) : ℚ) = 0 := by
      rw [PowerSeries.coeff_map] at hmap3
      exact hmap3.trans hq.2
    have hc' : ((PowerSeries.coeff (4 * n + 3) integralT : ℤ) : ℚ) =
        ((0 : ℤ) : ℚ) := by simpa using hc
    exact Int.cast_injective hc'

end D5.S3.Arith.ModularForms.CubicThetaOddParity
