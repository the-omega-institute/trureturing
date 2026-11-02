/- GID: D5/S3/Arith/ModularForms/CubicThetaCubeDissection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaCubeDissection
   mirror-E: none(waiver:formal-jacobi-cube-dissection)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Complete Jacobi cube columns by exact affine lattice reindexing. -/

import D5.S3.Arith.ModularForms.CubicThetaJacobiColumns

/-! The full three-residue Laurent dissection uses the complete integer lattice. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaCubeDissection

open CubicThetaJacobiColumns CubicThetaJacobiCube CubicThetaLattice CubicThetaShifted
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

def residueExponent (m : ℤ) (r : Fin 3) : ℕ :=
  (3 * (triangularExponent m : ℤ) + r.val * m).toNat

theorem residue_exponent_nonneg (m : ℤ) (r : Fin 3) :
    0 ≤ 3 * (triangularExponent m : ℤ) + r.val * m := by
  have h := twice_triangular m
  by_cases hm : m < 0
  · have hm' : m ≤ -1 := by omega
    fin_cases r <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat] <;>
      nlinarith [sq_nonneg (m + 1)]
  · by_cases hzero : m = 0
    · subst m; simp [triangularExponent]
    · have hm' : 1 ≤ m := by omega
      have htri : (0 : ℤ) ≤ triangularExponent m := Int.natCast_nonneg _
      fin_cases r <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat] <;>
        nlinarith

theorem residue_exponent_cast (m : ℤ) (r : Fin 3) :
    (residueExponent m r : ℤ) = 3 * (triangularExponent m : ℤ) + r.val * m :=
  Int.toNat_of_nonneg (residue_exponent_nonneg m r)

private def translate (m : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (m + p.1, m + p.2)
  invFun p := (p.1 - m, p.2 - m)
  left_inv p := by ext <;> dsimp <;> omega
  right_inv p := by ext <;> dsimp <;> omega

private def reflectTranslate (m : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (m + 1 - p.1, m + 1 - p.2)
  invFun p := (m + 1 - p.1, m + 1 - p.2)
  left_inv p := by ext <;> dsimp <;> omega
  right_inv p := by ext <;> dsimp <;> omega

private theorem triple_exponent_zero (m : ℤ) (p : ℤ × ℤ) :
    triangularExponent (m + p.1) + triangularExponent (m + p.2) +
      triangularExponent (m - p.1 - p.2) =
      residueExponent m 0 + (eisensteinNorm p).toNat := by
  have h1 := twice_triangular (m + p.1)
  have h2 := twice_triangular (m + p.2)
  have h3 := twice_triangular (m - p.1 - p.2)
  have hm := twice_triangular m
  have hr := residue_exponent_cast m 0
  have hn := Int.toNat_of_nonneg (norm_nonneg p)
  dsimp [eisensteinNorm] at hn
  norm_num only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at hr
  have heq : (triangularExponent (m + p.1) : ℤ) + triangularExponent (m + p.2) +
      triangularExponent (m - p.1 - p.2) =
      residueExponent m 0 + (eisensteinNorm p).toNat := by
    dsimp [eisensteinNorm]
    nlinarith
  exact_mod_cast heq

private theorem triple_exponent_one (m : ℤ) (p : ℤ × ℤ) :
    triangularExponent (m + p.1) + triangularExponent (m + p.2) +
      triangularExponent (m + 1 - p.1 - p.2) =
      residueExponent m 1 + (shiftedExponent p).toNat := by
  have h1 := twice_triangular (m + p.1)
  have h2 := twice_triangular (m + p.2)
  have h3 := twice_triangular (m + 1 - p.1 - p.2)
  have hm := twice_triangular m
  have hr := residue_exponent_cast m 1
  have hn := Int.toNat_of_nonneg (shifted_exponent_nonneg p)
  dsimp [shiftedExponent, eisensteinNorm] at hn
  norm_num only [Fin.val_one, Nat.cast_one, one_mul] at hr
  have heq : (triangularExponent (m + p.1) : ℤ) + triangularExponent (m + p.2) +
      triangularExponent (m + 1 - p.1 - p.2) =
      residueExponent m 1 + (shiftedExponent p).toNat := by
    dsimp [shiftedExponent, eisensteinNorm]
    nlinarith
  exact_mod_cast heq

private theorem triple_exponent_two (m : ℤ) (p : ℤ × ℤ) :
    triangularExponent (m + 1 - p.1) + triangularExponent (m + 1 - p.2) +
      triangularExponent (m + p.1 + p.2) =
      residueExponent m 2 + (shiftedExponent p).toNat := by
  have h1 := twice_triangular (m + 1 - p.1)
  have h2 := twice_triangular (m + 1 - p.2)
  have h3 := twice_triangular (m + p.1 + p.2)
  have hm := twice_triangular m
  have hr := residue_exponent_cast m 2
  have hn := Int.toNat_of_nonneg (shifted_exponent_nonneg p)
  dsimp [shiftedExponent, eisensteinNorm] at hn
  change (residueExponent m 2 : ℤ) = 3 * (triangularExponent m : ℤ) + 2 * m at hr
  have heq : (triangularExponent (m + 1 - p.1) : ℤ) + triangularExponent (m + 1 - p.2) +
      triangularExponent (m + p.1 + p.2) =
      residueExponent m 2 + (shiftedExponent p).toNat := by
    dsimp [shiftedExponent, eisensteinNorm]
    nlinarith
  exact_mod_cast heq

private theorem sign_residue (m : ℤ) (r : ℤ) :
    (-1 : ℚ) ^ (3 * m + r).natAbs = (-1 : ℚ) ^ m.natAbs * (-1 : ℚ) ^ r.natAbs := by
  have h : (3 * m + r).negOnePow = m.negOnePow * r.negOnePow := by
    rw [show 3 * m + r = 2 * m + (m + r) by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, Int.negOnePow_add]
  have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h
  simpa only [Units.val_mul, Int.cast_mul, Int.coe_negOnePow] using hh

set_option maxHeartbeats 1000000 in
-- Typeclass synthesis includes the complete power-series uniformity.
/-- All columns in residue zero are translated complete norm lattices. -/
theorem cube_column_three_mul (m : ℤ) :
    cubeColumn (3 * m) = PowerSeries.C ((-1 : ℚ) ^ m.natAbs) *
      PowerSeries.X ^ residueExponent m 0 * normTheta := by
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have h := (translate m).hasSum_iff.mpr (hasSum_cube_column (3 * m))
  have he (p : ℤ × ℤ) : 3 * m - (m + p.1) - (m + p.2) = m - p.1 - p.2 := by omega
  simp only [translate, Equiv.coe_fn_mk, Function.comp_def] at h
  simp_rw [he, triple_exponent_zero, pow_add] at h
  rw [show 3 * m = 3 * m + 0 by omega, sign_residue] at h
  simp only [Int.natAbs_zero, pow_zero, mul_one, map_mul] at h
  have ht := hasSum_lattice_theta.1.mul_left
    (PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ residueExponent m 0)
  simp only [mul_assoc] at ht
  simpa only [add_zero, mul_assoc] using h.unique ht

set_option maxHeartbeats 1000000 in
-- Typeclass synthesis includes the complete power-series uniformity.
/-- All columns in residue one are translated shifted lattices, with the exact sign. -/
theorem cube_column_three_mul_add_one (m : ℤ) :
    cubeColumn (3 * m + 1) = -(PowerSeries.C ((-1 : ℚ) ^ m.natAbs) *
      PowerSeries.X ^ residueExponent m 1 * (PowerSeries.C 3 * coreTheta)) := by
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have h := (translate m).hasSum_iff.mpr (hasSum_cube_column (3 * m + 1))
  have he (p : ℤ × ℤ) : 3 * m + 1 - (m + p.1) - (m + p.2) =
      m + 1 - p.1 - p.2 := by omega
  simp only [translate, Equiv.coe_fn_mk, Function.comp_def] at h
  simp_rw [he, triple_exponent_one, pow_add] at h
  rw [sign_residue] at h
  simp only [Int.natAbs_one, pow_one, mul_neg_one, map_neg] at h
  have ht := hasSum_shifted_theta.mul_left
    (-(PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ residueExponent m 1))
  rw [shifted_theta_eq_three_core] at ht
  simp only [mul_assoc, neg_mul] at h ht ⊢
  simpa only [add_zero, mul_assoc] using h.unique ht

set_option maxHeartbeats 1000000 in
-- Typeclass synthesis includes the complete power-series uniformity.
/-- Complementing the three integer indices gives every residue-two column. -/
theorem cube_column_three_mul_add_two (m : ℤ) :
    cubeColumn (3 * m + 2) = PowerSeries.C ((-1 : ℚ) ^ m.natAbs) *
      PowerSeries.X ^ residueExponent m 2 * (PowerSeries.C 3 * coreTheta) := by
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have h := (reflectTranslate m).hasSum_iff.mpr (hasSum_cube_column (3 * m + 2))
  have he (p : ℤ × ℤ) : 3 * m + 2 - (m + 1 - p.1) - (m + 1 - p.2) =
      m + p.1 + p.2 := by omega
  simp only [reflectTranslate, Equiv.coe_fn_mk, Function.comp_def] at h
  simp_rw [he, triple_exponent_two, pow_add] at h
  rw [sign_residue] at h
  norm_num only [show (2 : ℤ).natAbs = 2 from rfl, pow_two, neg_one_sq, mul_one] at h
  have ht := hasSum_shifted_theta.mul_left
    (PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ residueExponent m 2)
  rw [shifted_theta_eq_three_core] at ht
  simp only [mul_assoc] at ht
  simpa only [add_zero, mul_assoc] using h.unique ht

end D5.S3.Arith.ModularForms.CubicThetaCubeDissection
