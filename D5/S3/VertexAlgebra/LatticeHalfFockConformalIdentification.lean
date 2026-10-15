/- GID: D5/S3/VertexAlgebra/LatticeHalfFockConformalIdentification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockConformalIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual corrected conformal-state identification with half-integer stress. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import D5.S3.VertexAlgebra.LatticeActualConformalState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField LatticeHalfFock LatticeActualConformalState
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem pair_enumeration (D : LatticeData) (first second : Index D) :
    [first, second].Perm (LatticeAllStateField.occurrences D
      (Finsupp.single first 1 + Finsupp.single second 1)) := by
  rw [← Multiset.coe_eq_coe]
  simp [LatticeAllStateField.occurrences, Finsupp.toMultiset_add]
  rfl

private theorem quadratic_correction (D : LatticeData) (i j : Fin D.rank) :
    Corr D 0 (X (i, 0) * X (j, 0)) =
      Finsupp.single 0 (X (i, 0) * X (j, 0)) +
        Finsupp.single 2 (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) := by
  have source := Corr_monomial_enumeration D 0
    (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1)
    [(i, 0), (j, 0)] (pair_enumeration D _ _)
  have monomial : monomial (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1) (1 : ℂ) =
      X (i, 0) * X (j, 0) := by
    simp [MvPolynomial.X, monomial_mul]
  rw [monomial] at source
  rw [source]
  have word : correctionWord D 0 [(i, 0), (j, 0)] =
      X (some (i, 0)) * X (some (j, 0)) +
        C ((1 / 8 : ℂ) * (D.G i j : ℂ)) * X none ^ 2 := by
    rw [correctionWord_matching]
    simp [labelledRemainders, correctionWord, insertion, singletonPolynomial,
      bilinear, pairPolynomial, sourceWeight, pairScalar, halfBinomial]
    <;> norm_num
  rw [word, map_add, map_mul, map_mul, map_pow,
    optionEquivLeft_X_some, optionEquivLeft_X_some, optionEquivLeft_C,
    optionEquivLeft_X_none, map_add]
  rw [← Polynomial.C_mul]
  change Finsupp.single 0 (X (i, 0) * X (j, 0)) +
    shiftCoefficients D (Polynomial.C (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) *
      Polynomial.X ^ 2) = _
  apply congrArg (fun tail : ℕ →₀ Oscillator D =>
    Finsupp.single 0 (X (i, 0) * X (j, 0)) + tail)
  apply Finsupp.ext
  intro shift
  change (Polynomial.C (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) *
    Polynomial.X ^ 2).coeff shift = _
  rw [Polynomial.coeff_C_mul_X_pow]
  simp only [Finsupp.single_apply, eq_comm]

private theorem normal_polynomial_pair (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) :
    normalPolynomial D hu 0 (X (i, 0) * X (j, 0)) =
      normalInsertion D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j) := by
  have monomial : monomial (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1) (1 : ℂ) =
      X (i, 0) * X (j, 0) := by simp [MvPolynomial.X, monomial_mul]
  rw [← monomial, normalPolynomial_monomial_enumeration D hu 0 _ _
    (pair_enumeration D _ _)]
  simp only [normalWord, charged_zero_identity, normalInsertion_identity_current]

private theorem quadratic_field (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) :
    Ytw D hu (Finsupp.single 0 (X (i, 0) * X (j, 0))) =
      normalInsertion D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j) +
        ((1 / 8 : ℂ) * (D.G i j : ℂ)) •
          shiftLinear D hu 2 FieldNormalProduct.identityField := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
    quadratic_correction, map_add, Finsupp.lsum_single, shiftLinear_zero,
    normal_polynomial_pair]
  have constant : C ((1 / 8 : ℂ) * (D.G i j : ℂ)) =
      ((1 / 8 : ℂ) * (D.G i j : ℂ)) • (1 : Oscillator D) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [constant, map_smul, normalPolynomial_one, charged_zero_identity, map_smul]

private theorem normal_pair_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (e : ℤ) (v : ActualTensor D hu) :
    (normalInsertion D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j)).coeff e v =
      if e % 2 = 0 then
        ∑ᶠ mode : ℤ, tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v
      else 0 := by
  classical
  rw [normalInsertion_integer_modes]
  by_cases even : e % 2 = 0
  · rw [if_pos even]
    have identification (mode : ℤ) : flatTerm D hu
        (tensorCurrentField D (ActualGround D hu) j) [(i, 0)] e v (mode, ()) =
        tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v := by
      have parity : (e + 2 * mode + 3) % 2 = 1 := by omega
      have index : (-(e + 2 * mode + 3)-3)/2 = (-e-4)/2-mode-1 := by omega
      simp only [flatTerm, flatCoefficient, jetCurrent, jetScalar,
        Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one,
        div_one, one_smul, Nat.cast_zero, mul_zero, add_zero,
        tensorCurrentField, HVertexOperator.coeff_of_coeff, currentCoeff,
        if_pos parity, index, tensorPair_eq]
      split_ifs <;> rfl
    have finite := tensorPair_finite D (ActualGround D hu) i j ((-e-4)/2) v
    have support : Function.support (fun mode : ℤ => flatTerm D hu
        (tensorCurrentField D (ActualGround D hu) j) [(i, 0)] e v (mode, ())) ⊆
        finite.toFinset := by
      intro mode member
      apply finite.mem_toFinset.mpr
      change tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v ≠ 0
      rw [← identification mode]
      exact member
    rw [finsum_eq_sum_of_support_subset _ support, finsum_eq_sum _ finite]
    exact Finset.sum_congr rfl (fun mode member => identification mode)
  · rw [if_neg even]
    have parity (mode : ℤ) : (e + 2 * mode + 3) % 2 ≠ 1 := by omega
    have zero (mode : ℤ) : flatTerm D hu (tensorCurrentField D (ActualGround D hu) j)
        [(i, 0)] e v (mode, ()) = 0 := by
      simp only [flatTerm, flatCoefficient, tensorCurrentField,
        HVertexOperator.coeff_of_coeff, Nat.cast_zero, mul_zero, add_zero,
        currentCoeff, if_neg (parity mode)]
      split_ifs <;> simp [tensorEnd]
    simp only [zero, finsum_zero]

private theorem shift_identity_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (v : ActualTensor D hu) :
    (shiftLinear D hu 2 FieldNormalProduct.identityField).coeff e v =
      if e = -4 then v else 0 := by
  simp only [shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
    HVertexOperator.coeff_of_coeff]
  norm_num only [Nat.cast_ofNat]
  simp only [FieldNormalProduct.identityField, VertexOperator.of_coeff,
    HVertexOperator.coeff_of_coeff,
    show (e + 4 = 0) ↔ e = -4 by omega]
  split_ifs <;> rfl

private theorem raw_trace_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ℤ) (v : ActualTensor D hu) :
    (Ytw D hu (omega D H)).coeff e v =
      (if e % 2 = 0 then tensorRawL D (ActualGround D hu) H ((-e-4)/2) v else 0) +
        (if e = -4 then ((∑ i, ∑ j, H i j * (D.G i j : ℂ)) / 16) • v else 0) := by
  classical
  unfold omega conformalPolynomial
  rw [← Finsupp.smul_single, map_smul]
  simp_rw [Finsupp.single_finsetSum, map_sum, ← Finsupp.smul_single, map_smul,
    quadratic_field]
  simp only [map_smul, map_sum, map_add, Pi.smul_apply, Pi.add_apply,
    Finset.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, normal_pair_coeff, shift_identity_coeff]
  by_cases even : e % 2 = 0
  · rw [if_pos even, tensor_rawL_finsum]
    simp only [if_pos even, smul_add, Finset.sum_add_distrib]
    by_cases shifted : e = -4
    · simp only [if_pos shifted]
      congr 1
      simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv,
        Finset.sum_mul, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i member
      apply Finset.sum_congr rfl
      intro j member
      congr 1
      ring
    · simp [if_neg shifted]
  · have shifted : e ≠ -4 := by intro equality; subst e; norm_num at even
    simp only [if_neg even, if_neg shifted, smul_zero, add_zero, Finset.sum_const_zero]

theorem Ytw_omega (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) :
    Ytw D hu (omega D H) = tensorStressField D (ActualGround D hu) H := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  rw [raw_trace_coeff, inverse_trace D H hHG]
  rw [tensorStressField, HVertexOperator.coeff_of_coeff]
  by_cases even : e % 2 = 0
  · have shifted : (-e-4)/2 = 0 ↔ e = -4 := by omega
    change _ = (tensorEndLinear D (ActualGround D hu) (stressCoeff D H e)) v
    simp only [stressCoeff, if_pos even, L, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, shifted]
    change tensorRawL D (ActualGround D hu) H ((-e-4)/2) v +
      (if e = -4 then ((D.rank : ℂ) / 16) • v else 0) =
      tensorRawL D (ActualGround D hu) H ((-e-4)/2) v +
        (if e = -4 then (D.rank : ℂ) / 16 else 0) • tensorEnd D (ActualGround D hu) 1 v
    congr 1
    split_ifs
    · change ((D.rank : ℂ) / 16) • v =
        ((D.rank : ℂ) / 16) • (TensorProduct.map LinearMap.id LinearMap.id) v
      rw [TensorProduct.map_id, LinearMap.id_apply]
    · simp only [zero_smul]
  · have shifted : e ≠ -4 := by intro equality; subst e; norm_num at even
    simp only [stressCoeff, if_neg even, if_neg shifted, add_zero]
    change 0 = tensorEndLinear D (ActualGround D hu) 0 v
    rw [map_zero, LinearMap.zero_apply]

end
end D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification.Ytw_omega
