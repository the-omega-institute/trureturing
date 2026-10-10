/- GID: D5/S3/VertexAlgebra/LatticeActualStateDerivative
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualStateDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual translation of every state differentiates its field at every integer mode. -/

import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

/-
Unconditional state differentiation for the actual lattice state-field map.
The proof extracts the actual residue iterate at -2 against the vacuum.
It uses ordinary LatticeData, with no inverse-Gram, grading, energy,
state-product compatibility, or derivative-state assumption.

Primary source and licensing are recorded in LatticeActualStateFieldCalculus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeActualStateDerivative
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeAllStateReconstruction FieldNormalProduct
open scoped VertexOperator
noncomputable section

private theorem minus_two_weight (j : ℕ) :
    (-1 : ℂ)^j * ((Ring.choose (-2) j : ℤ) : ℂ) = (j + 1 : ℂ) := by
  have choose : ((Ring.choose (-2) j : ℤ) : ℂ) =
      (-1 : ℂ)^j * (j + 1 : ℂ) := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, Ring.choose_neg,
      show (2 : ℤ) + j - 1 = ((j + 1 : ℕ) : ℤ) by omega,
      Ring.choose_natCast, Nat.choose_succ_self_right]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
      Int.cast_negOnePow_natCast, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
  have square : (-1 : ℂ)^j * (-1 : ℂ)^j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [choose, ← mul_assoc, square, one_mul]

/-- The derivative-state identity at every integer coefficient, even for a
degenerate even lattice and for arbitrary nonhomogeneous actual states. -/
theorem state_derivative_modes (D : LatticeData) (a : Carrier D) (q : ℤ) :
    ((Y D (translation D a))[[q]]) = -(q : ℂ) • ((Y D a)[[q - 1]]) := by
  classical
  apply LinearMap.ext
  intro v
  have h := (stateField_iterate D a (vacuum D) v (-2) q).2.2
  dsimp only at h
  rw [stateField_vacuum] at h
  simp_rw [minus_two_weight] at h
  rw [show (-1 : ℂ)^(-2 : ℤ) = 1 by norm_num, one_smul,
    ← LatticeActualVertexAlgebra.translation_as_mode D a] at h
  let left (j : ℕ) : Carrier D := (j + 1 : ℂ) •
    ((Y D a)[[-2 - j]]) (((identityField : VertexOperator ℂ (Carrier D))[[q + j]]) v)
  let right (j : ℕ) : Carrier D := (j + 1 : ℂ) •
    ((identityField : VertexOperator ℂ (Carrier D))[[-2 + q - j]])
      (((Y D a)[[j]]) v)
  change ((Y D (translation D a))[[q]]) v = (∑ᶠ j : ℕ, left j) - (∑ᶠ j : ℕ, right j) at h
  rcases lt_trichotomy q 0 with negative | zero | positive
  · have rightZero : ∀ j : ℕ, right j = 0 := by
      intro j
      simp [right, identity_modes, show (-2 : ℤ) + q - j ≠ -1 by omega]
    simp only [rightZero, finsum_zero, sub_zero] at h
    let n : ℕ := (-q - 1).toNat
    have index : q + (n : ℤ) = -1 := by dsimp [n]; omega
    have mode : (-2 : ℤ) - n = q - 1 := by dsimp [n]; omega
    have scalar : (n + 1 : ℂ) = -(q : ℂ) := by
      exact_mod_cast (show (n : ℤ) + 1 = -q by dsimp [n]; omega)
    have leftSum : (∑ᶠ j : ℕ, left j) = -(q : ℂ) • ((Y D a)[[q - 1]]) v := by
      rw [finsum_eq_single _ n]
      · simp only [left, identity_modes, if_pos index, LinearMap.id_apply, mode, scalar]
      · intro j different
        simp [left, identity_modes, show q + (j : ℤ) ≠ -1 by dsimp [n] at different; omega]
    rw [leftSum] at h
    simpa only [LinearMap.smul_apply] using h
  · subst q
    have leftZero : ∀ j : ℕ, left j = 0 := by
      intro j
      simp [left, identity_modes, show (0 : ℤ) + j ≠ -1 by omega]
    have rightZero : ∀ j : ℕ, right j = 0 := by
      intro j
      simp only [right, identity_modes,
        if_neg (show (-2 : ℤ) + 0 - (j : ℤ) ≠ -1 by omega),
        LinearMap.zero_apply, smul_zero]
    simpa only [leftZero, rightZero, finsum_zero, sub_self, Int.cast_zero,
      neg_zero, zero_smul, LinearMap.smul_apply, LinearMap.zero_apply] using h
  · have leftZero : ∀ j : ℕ, left j = 0 := by
      intro j
      simp [left, identity_modes, show q + (j : ℤ) ≠ -1 by omega]
    simp only [leftZero, finsum_zero, zero_sub] at h
    let n : ℕ := (q - 1).toNat
    have index : (-2 : ℤ) + q - n = -1 := by dsimp [n]; omega
    have mode : (n : ℤ) = q - 1 := by dsimp [n]; omega
    have scalar : (n + 1 : ℂ) = (q : ℂ) := by
      exact_mod_cast (show (n : ℤ) + 1 = q by dsimp [n]; omega)
    have rightSum : (∑ᶠ j : ℕ, right j) = (q : ℂ) • ((Y D a)[[q - 1]]) v := by
      rw [finsum_eq_single _ n]
      · simp only [right, identity_modes, if_pos index, LinearMap.id_apply]
        rw [mode, scalar]
      · intro j different
        simp [right, identity_modes,
          show (-2 : ℤ) + q - j ≠ -1 by dsimp [n] at different; omega]
    rw [rightSum] at h
    change _ = -(q : ℂ) • (((Y D a)[[q - 1]]) v)
    simpa only [neg_smul] using h

theorem dividedDerivative_one_modes (D : LatticeData)
    (A : VertexOperator ℂ (Carrier D)) (q : ℤ) :
    ((dividedDerivative 1 A)[[q]]) = -(q : ℂ) • (A[[q - 1]]) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-q - 1 + 1) 1 • HVertexOperator.coeff A (-q - 1 + 1) v = _
  rw [Ring.choose_one_right, VertexOperator.coeff_eq_ncoeff,
    show -(-q - 1 + 1) - 1 = q - 1 by omega, ← Int.cast_smul_eq_zsmul ℂ]
  simp only [sub_add_cancel, Int.cast_neg, LinearMap.smul_apply]

theorem state_derivative (D : LatticeData) (a : Carrier D) :
    Y D (translation D a) = dividedDerivative 1 (Y D a) := by
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    state_derivative_modes, dividedDerivative_one_modes]

end
end D5.S3.VertexAlgebra.LatticeActualStateDerivative
