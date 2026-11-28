/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qIntegratedNormalMode
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed normal-mode integral, including the zero-mode logarithm. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalScalar
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetNormalOrdering

/-!
The positive-level integral of a signed normal-order slot in
`t = (x/y)^3 - 1`. The exponent `-m-3d` in
`P48qJetNormalOrdering.jetTerm_cons` gives the branch `-m/3`.
For a nonzero mode, the external factor `y^(-m)` turns the numerator
`(y/x)^m - 1` into `x^(-m) - y^(-m)`. The logarithm for the zero
mode multiplies the action on the input momentum.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedNormalMode

open P48qJetNormalOrdering (jetWeight)
open P48qTwistedHeisenberg (diagonalCoverRatio)
open P48qThirdTwistedField (diagonalXOverY_mul_q)
open PowerSeries (C coeff binomialSeries)

open private diagonalXOverYUnit coe_diagonalXOverYUnit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private coverRatio_pow from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalScalar
open private choose_succ_mul_lower from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetContractions

/-- Integrate the signed jet weight at every positive source level. -/
def integratedNormalMode (m : ℤ) : PowerSeries ℂ :=
  PowerSeries.mk fun d =>
    if hd : 0 < d then jetWeight ⟨d, hd⟩ m / (d : ℂ) else 0

@[simp] theorem coeff_zero_integratedNormalMode (m : ℤ) :
    coeff 0 (integratedNormalMode m) = 0 := by
  simp [integratedNormalMode]

theorem coeff_integratedNormalMode_pos (m : ℤ) {d : ℕ} (hd : 0 < d) :
    coeff d (integratedNormalMode m) = jetWeight ⟨d, hd⟩ m / (d : ℂ) := by
  simp only [integratedNormalMode, PowerSeries.coeff_mk, dite_eq_left hd]

/-- The actual diagonal cover ratio `y/x` as a power series unit. -/
def diagonalCoverRatioUnit : (PowerSeries ℂ)ˣ :=
  diagonalXOverYUnit⁻¹

@[simp] theorem coe_diagonalCoverRatioUnit :
    (diagonalCoverRatioUnit : PowerSeries ℂ) = diagonalCoverRatio := by
  symm
  apply Units.eq_inv_of_mul_eq_one_left (u := diagonalXOverYUnit)
  rw [coe_diagonalXOverYUnit, diagonalXOverY_mul_q]

theorem coe_diagonalCoverRatioUnit_zpow (m : ℤ) :
    (↑(diagonalCoverRatioUnit ^ m) : PowerSeries ℂ) = binomialSeries ℂ (-(m : ℂ) / 3) := by
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, coe_diagonalCoverRatioUnit,
      coverRatio_pow, Int.cast_natCast, neg_div]
  | negSucc n =>
    rw [zpow_negSucc]
    symm
    apply Units.eq_inv_of_mul_eq_one_left
    rw [Units.val_pow_eq_pow_val, coe_diagonalCoverRatioUnit, coverRatio_pow,
      ← PowerSeries.binomialSeries_add, Int.cast_negSucc, neg_neg, neg_add_cancel,
      PowerSeries.binomialSeries_zero]

/-- The zero-mode primitive is the logarithm in the normalized diagonal variable. -/
theorem integratedNormalMode_zero : integratedNormalMode 0 = PowerSeries.log ℂ := by
  apply PowerSeries.ext
  intro d
  cases d with
  | zero => simp
  | succ n =>
    rw [coeff_integratedNormalMode_pos 0 (Nat.succ_pos n)]
    change Ring.choose (-(↑(0 : ℤ) : ℂ) / 3 - 1) n / (↑(n + 1 : ℕ) : ℂ) = _
    simp only [PowerSeries.coeff_log, Int.cast_zero, neg_zero, zero_div, zero_sub,
      ite_eq_right (Nat.succ_ne_zero n), map_div₀, map_pow, map_neg, map_one, map_natCast]
    rw [Ring.choose_neg,
      show (1 : ℂ) + n - 1 = n by ring, Ring.choose_natCast, Nat.choose_self, Nat.cast_one,
      Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast, mul_one,
      show n + 1 + 1 = n + 2 by rfl, pow_add (-1 : ℂ) n 2,
      show (-1 : ℂ) ^ 2 = 1 by norm_num, mul_one]

/-- The signed primitive times `-m/3` is the difference of the cover-ratio
power and one. This scaled identity also holds at zero. -/
theorem C_mul_integratedNormalMode (m : ℤ) :
    C (-(m : ℂ) / 3) * integratedNormalMode m =
      (↑(diagonalCoverRatioUnit ^ m) : PowerSeries ℂ) - 1 := by
  rw [coe_diagonalCoverRatioUnit_zpow]
  apply PowerSeries.ext
  intro d
  cases d with
  | zero =>
    rw [PowerSeries.coeff_C_mul, coeff_zero_integratedNormalMode]
    simp
  | succ n =>
    let a : ℂ := -(m : ℂ) / 3
    have hn : (↑(n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [PowerSeries.coeff_C_mul, coeff_integratedNormalMode_pos m (Nat.succ_pos n), map_sub,
      PowerSeries.binomialSeries_coeff, PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero n),
      sub_zero, smul_eq_mul, mul_one]
    change a * (Ring.choose (a - 1) n / (↑(n + 1 : ℕ) : ℂ)) = Ring.choose a (n + 1)
    rw [← mul_div_assoc, div_eq_iff hn, Nat.cast_succ, mul_comm (Ring.choose a (n + 1))]
    exact (choose_succ_mul_lower a n).symm

#print axioms integratedNormalMode
#print axioms coeff_zero_integratedNormalMode
#print axioms coeff_integratedNormalMode_pos
#print axioms diagonalCoverRatioUnit
#print axioms coe_diagonalCoverRatioUnit
#print axioms coe_diagonalCoverRatioUnit_zpow
#print axioms integratedNormalMode_zero
#print axioms C_mul_integratedNormalMode

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedNormalMode
