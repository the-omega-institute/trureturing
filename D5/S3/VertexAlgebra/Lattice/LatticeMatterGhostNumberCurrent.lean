/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCurrent
   mirror-E: none(waiver:original-algebraic-number-current)
   anchors: []
   utility: none
   digest: The original even ghost number current and unrestricted integer mode covariance. -/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate

/-! The number current is the matter vacuum tensored with the negative two-site
ghost occupation state. All sums are taken after application to an original
finite-excitation state. No rank or parity restriction is imposed on the states
in the covariance theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private integer_split normal_product b_modes c_modes from
  D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
open private signedNormalMinusOne from D5.S3.Quantum.Fermionic.BcGhostStateField
open private left_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeMatterGhostNumberCurrent

open LatticeGeneratingFieldLocality LatticeMatterGhostCoupling
open LatticeMatterGhostStateField LatticeMatterGhostDegree
open D5.S3.Quantum.Fermionic (BcGhostStateField BcGhostChargeTensor)

private theorem ghost_current_zero_mode :
    ((BcGhostStateField.Y (-ket {0, 1})) [[0]]) = ghostNumber := by
  have word : b (-2) (ket {1}) = ket {0, 1} := by
    norm_num [b, create_ket, phase, lowerCount, Finset.filter_insert,
      Finset.filter_singleton]
  have product := normal_product (ket {0}) (ket {1}) 1 1
    (by simp [parity_ket]) (by simp [parity_ket])
  rw [b_modes] at product
  norm_num only [show (-1 : ℤ) - 1 = -2 by omega,
    show (-1 : ℂ) ^ (1 * 1 : ℕ) = -1 by norm_num] at product
  rw [word] at product
  apply LinearMap.ext
  intro x
  rw [ghost_number_normal_sum, integer_split _ (normal_term_finite_support x) 2]
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply]
  rw [product, (signedNormalMinusOne (-1) _ _).2]
  simp only [b_modes, c_modes, neg_one_smul]
  have lower (i : ℕ) : normalTerm (2 - i - 1) x =
      c (0 - (i : ℤ) - 1 + 2) (b ((i : ℤ) - 1) x) := by
    rw [normalTerm, if_pos (by omega)]
    simp only [Module.End.mul_apply]
    congr 1 <;> congr 1 <;> omega
  have upper (i : ℕ) : normalTerm (2 + i) x =
      -(b (-(i : ℤ) - 1 - 1) (c (0 + (i : ℤ) + 2) x)) := by
    rw [normalTerm, if_neg (by omega)]
    simp only [LinearMap.neg_apply, Module.End.mul_apply]
    congr 1 <;> congr 1 <;> congr 1 <;> omega
  simp only [lower, upper, finsum_neg_distrib]
  abel

/-- The actual even number current on the original matter–ghost carrier. -/
def numberCurrent (D : LatticeData) : State D :=
  LatticeAllStateField.vacuum D ⊗ₜ[ℂ] (-ket {0, 1})

private theorem number_current_even (D : LatticeData) :
    parity D (numberCurrent D) = numberCurrent D := by
  simp [numberCurrent, parity, TensorProduct.map_tmul, parity_ket]

/-- Its literal zero mode is the original tensor number operator. -/
theorem number_current_zero_mode (D : LatticeData) :
    ((Y D (numberCurrent D)) [[0]]) = tensorNumber D := by
  rw [numberCurrent, left_vacuum_modes, ghost_current_zero_mode]
  rfl

/-- Ghost number acts covariantly on every integer mode and every original
state, including a nonhomogeneous second state. -/
theorem tensorNumber_stateField (D : LatticeData) (a x : State D) (n : ℤ) :
    tensorNumber D (((Y D a) [[n]]) x) -
        ((Y D a) [[n]]) (tensorNumber D x) =
      ((Y D (tensorNumber D a)) [[n]]) x := by
  have h := (LatticeMatterGhostStateFieldIterate.stateField_iterate
    D (numberCurrent D) a x 0 n).2.2.2
  dsimp only at h
  have evenPart : (2 : ℂ)⁻¹ •
      (numberCurrent D + parity D (numberCurrent D)) = numberCurrent D := by
    rw [number_current_even]
    module
  have oddPart : (2 : ℂ)⁻¹ •
      (numberCurrent D - parity D (numberCurrent D)) = 0 := by
    rw [number_current_even, sub_self, smul_zero]
  rw [evenPart, oddPart] at h
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero,
    finsum_zero, add_zero] at h
  have vanish (i : ℕ) (hi : i ≠ 0) : Ring.choose (0 : ℤ) i = 0 :=
    Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)
  rw [finsum_eq_single _ 0 (fun i hi => by simp [vanish i hi]),
    finsum_eq_single _ 0 (fun i hi => by simp [vanish i hi])] at h
  simpa only [Nat.cast_zero, sub_zero, add_zero, zero_add, pow_zero,
    Ring.choose_zero_right, Int.cast_one, mul_one, one_smul, zpow_zero,
    number_current_zero_mode] using h.symm

end D5.S3.VertexAlgebra.LatticeMatterGhostNumberCurrent
