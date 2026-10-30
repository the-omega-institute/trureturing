/- GID: D5/S3/VertexAlgebra/ChargedResidue/FiniteChambers
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/FiniteChambers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two finite native scalar sums have the collision residue coefficients. -/
import D5.S3.VertexAlgebra.ChargedResidue.TwoChamber

/-! The finite ordered scalar sums are normalized together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedCollision PowerSeries
open scoped BigOperators
noncomputable section

private theorem symmetric_binomial (q : ℤ) : chamberSeries q q =
    (rescale (-1 : ℂ) (binomialSeries (R := ℤ) ℂ q)).subst (X^2 : PowerSeries ℂ) := by
  have hh : HasSubst (X^2 : PowerSeries ℂ) := HasSubst.X_pow (by decide)
  have one : (1 : PowerSeries ℂ).subst (X^2 : PowerSeries ℂ) = 1 := by
    rw [← coe_substAlgHom hh, map_one]
  have step (q : ℤ) :
      chamberSeries (q+1) (q+1) = chamberSeries q q * (1-X^2) ∧
      (rescale (-1 : ℂ) (binomialSeries (R := ℤ) ℂ (q+1))).subst
          (X^2 : PowerSeries ℂ) =
        (rescale (-1 : ℂ) (binomialSeries (R := ℤ) ℂ q)).subst
          (X^2 : PowerSeries ℂ) * (1-X^2) := by
    have base : binomialSeries (R := ℤ) ℂ (1 : ℤ) = 1+X := by
      simpa using (binomialSeries_nat (R := ℤ) (A := ℂ) 1)
    constructor
    · simp only [chamberSeries, binomialSeries_add, map_mul, base, map_add, map_one,
        rescale_X, map_neg]
      ring
    · rw [binomialSeries_add, map_mul, subst_mul hh, base, map_add, map_one, rescale_X]
      have negx : (C (-1 : ℂ) * X : PowerSeries ℂ) = -X := by simp
      have negSubst : (-X : PowerSeries ℂ).subst (X^2 : PowerSeries ℂ) = -(X^2) := by
        rw [← coe_substAlgHom hh, map_neg, coe_substAlgHom, subst_X hh]
      rw [negx, subst_add hh, negSubst, one]
      ring
  have nonzero : (1-X^2 : PowerSeries ℂ) ≠ 0 := by
    intro zero
    have constant := congrArg constantCoeff zero
    norm_num at constant
  refine Int.induction_on q ?_ ?_ ?_
  · simp only [binomialSeries_zero, chamberSeries, map_one, mul_one, one]
  · intro i ih
    rw [(step i).1, (step i).2, ih]
  · intro i ih
    apply mul_right_cancel₀ nonzero
    rw [← (step (-(i : ℤ)-1)).1, ← (step (-(i : ℤ)-1)).2,
      show -(i : ℤ)-1+1 = -(i : ℤ) by omega, ih]

private theorem ordered_scalar_coefficient (D : LatticeData) (left right : Charge D)
    (q v : ℤ) (J : ℕ) (bound : v < J) :
    (∑ j ∈ Finset.range J, physicalResidueWeight q j *
      signedContraction D left right (v-2*j)) =
      scalarSignedCoeff (chamberSeries (q+bilinear D left right)
        (q-bilinear D left right)) v := by
  let T := rescale (-1 : ℂ) (binomialSeries (R := ℤ) ℂ q)
  let H := halfContraction D left right
  have expansion : chamberSeries (q+bilinear D left right) (q-bilinear D left right) =
      T.subst (X^2 : PowerSeries ℂ) * H := by
    rw [← symmetric_binomial]
    dsimp only [H]
    unfold chamberSeries halfContraction
    rw [sub_eq_add_neg, binomialSeries_add, binomialSeries_add, map_mul]
    ring
  have weight (j : ℕ) : coeff j T = physicalResidueWeight q j := by
    simp [T, coeff_rescale, binomialSeries_coeff, physicalResidueWeight,
      StateFieldResidueReconstruction.integerBinomial, zsmul_eq_mul]
  rw [expansion]
  by_cases negative : v < 0
  · rw [scalarSignedCoeff, ite_eq_left negative]
    apply Finset.sum_eq_zero
    intro j member
    simp only [signedContraction, ite_eq_left (by omega : v-2*(j : ℤ) < 0), mul_zero]
  · rw [scalarSignedCoeff, ite_eq_right negative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_bij_ne_zero (fun j _ _ => 2*j) ?_ ?_ ?_ ?_
    · intro j member nonzero
      have nonnegative : 0 ≤ v-2*(j : ℤ) := by
        by_contra outside
        exact nonzero (by simp [signedContraction, show v-2*(j : ℤ) < 0 by omega])
      apply Finset.mem_range.mpr
      omega
    · intro i hi ni j hj nj equal
      omega
    · intro i member nonzero
      have divisible : 2 ∣ i := by
        by_contra outside
        exact nonzero (by rw [coeff_subst_X_pow (by decide : 2 ≠ 0),
          ite_eq_right outside, zero_mul])
      obtain ⟨j, equality⟩ := divisible
      have upper := Finset.mem_range.mp member
      refine ⟨j, Finset.mem_range.mpr (by omega), ?_, equality.symm⟩
      have signed : v-2*(j : ℤ) = ((v.toNat-2*j : ℕ) : ℤ) := by omega
      have transformed := nonzero
      rw [equality, coeff_subst_X_pow (by decide : 2 ≠ 0)] at transformed
      have div : 2*j/2 = j := by omega
      simpa only [dvd_mul_right, ite_true, div, Algebra.algebraMap_self, RingHom.id_apply,
        weight, signedContraction, signed, ite_eq_right (by omega : ¬ ((v.toNat-2*j : ℕ) : ℤ) < 0),
        Int.toNat_natCast] using transformed
    · intro j member nonzero
      have nonnegative : 0 ≤ v-2*(j : ℤ) := by
        by_contra outside
        exact nonzero (by simp [signedContraction, show v-2*(j : ℤ) < 0 by omega])
      have signed : v-2*(j : ℤ) = ((v.toNat-2*j : ℕ) : ℤ) := by omega
      rw [coeff_subst_X_pow (by decide : 2 ≠ 0)]
      have div : 2*j/2 = j := by omega
      simp only [dvd_mul_right, ite_true, div, Algebra.algebraMap_self, RingHom.id_apply,
        weight, signedContraction, signed, ite_eq_right (by omega : ¬ ((v.toNat-2*j : ℕ) : ℤ) < 0),
        Int.toNat_natCast]
      rfl

/- proof_shape: native_chamber_scalar_full: content
   admission_basis: escape-witness
   escape_witness: Each native contraction sum is a separately finite sparse
   quadratic coefficient convolution. Their signed difference is evaluated by
   the full integer two-pole residue formula with its Jacobian.
   literature_status: classical finite twisted-lattice residue calculus. -/
theorem native_chamber_scalar_full (D : LatticeData) (left right : Charge D)
    (q v : ℤ) (forward reverse : ℕ) (hf : v < forward) (hr : 2*q-v < reverse) :
    nativeChamberScalar D left right q v forward reverse =
      (1/2 : ℂ) * (2 : ℂ)^(-2*bilinear D left right) *
        (if -q-1-bilinear D left right < 0 then 0 else
          collisionScalar (v-2*q-2) (bilinear D left right)
            (-q-1-bilinear D left right).toNat) +
      (-1 : ℂ)^v * (1/2 : ℂ) * (2 : ℂ)^(2*bilinear D left right) *
        (if -q-1+bilinear D left right < 0 then 0 else
          collisionScalar (v-2*q-2) (-bilinear D left right)
            (-q-1+bilinear D left right).toNat) := by
  rw [nativeChamberScalar, ordered_scalar_coefficient D left right q v forward hf,
    ordered_scalar_coefficient D left right q (2*q-v) reverse hr]
  have parity : paritySign (bilinear D left right) = (-1 : ℂ)^(bilinear D left right) := by
    rw [paritySign, neg_one_zpow_eq_ite]
  rw [parity, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have index : q+bilinear D left right+(q-bilinear D left right)-v = 2*q-v := by ring
  have result := signed_two_chamber_scalar q (bilinear D left right) v
  simpa only [chamberDifference, index] using result

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
