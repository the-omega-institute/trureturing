import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHFormalCuspExpansion
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHFormalAlgebra
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHVectorModeJacobi
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBGradedModeBridge
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHTwoVariableRational

/-! The Laurent residue identity for the normalized BBHH channels gives the
literal coefficient Jacobi identity on the complementary twisted module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHActualVectorJacobi

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven leechUnit paritySign)
open Orbifold.NativeOddUpperRightSkew (rightField)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeFixedPairField (nu)
open LatticeHalfFockCorrectedField (correctedField)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedAIterateCoeff_eq_zero_off_energy)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff b_inner_coeff_off_grid)
open NativeFixedCrossedProductToIterate (aJointTerm)
open NativeBBHHVectorModeJacobi
open NativeBBHHFormalAlgebra
open NativeBBHHFormalCuspExpansion
open NativeBBHHTwoVariableRational (bJointTerm_off_total aJointTerm_off_total doubledDegree)
open NativeHHBBModeResidue (modePairs mem_modePairs)
open NativeHHBBFormalFusedIota (fusedNumeratorSeries)

open private grade_mod_two bModeLinear bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private aModeLinear aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private energySum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private fusedNumeratorSeries_eq_support from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalFusedIota
open private finsum_eq_sum_modePairs from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBGradedModeBridge
open private fixed_parity_preserved from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

local notation "ℒ" => leechData

private def bWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ)

private def dWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ)

private def aWeight (q : ℤ) (j : ℕ) : ℂ :=
  Ring.choose ((q : ℂ) + 1 / 2) j

/-- Absorb the positive half-binomial unit of the collision chart into the
test weight. This also applies when the target coefficient is below zero. -/
private theorem raw_iterate (A : ℕ → ℂ) (q k : ℤ) :
    (∑ ij ∈ modePairs k, ((Ring.choose q ij.2 : ℤ) : ℂ) *
      PowerSeries.coeff ij.1
        (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.mk A)) =
    ∑ ij ∈ modePairs k, aWeight q ij.2 * A ij.1 := by
  by_cases hk : 0 ≤ k
  · rw [modePairs, Finset.filter_true_of_mem fun _ _ => hk]
    have coeff_binomial_mul (z : ℂ) (F : PowerSeries ℂ) :
        PowerSeries.coeff k.toNat (PowerSeries.binomialSeries ℂ z * F) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k.toNat,
            Ring.choose z ij.2 * PowerSeries.coeff ij.1 F := by
      rw [mul_comm, PowerSeries.coeff_mul]
      simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
      exact Finset.sum_congr rfl fun ij _ => mul_comm _ _
    have cast_choose (j : ℕ) :
        ((Ring.choose q j : ℤ) : ℂ) = Ring.choose (q : ℂ) j :=
      Ring.map_choose (Int.castRingHom ℂ) q j
    calc
      _ = PowerSeries.coeff k.toNat (PowerSeries.binomialSeries ℂ (q : ℂ) *
            (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.mk A)) := by
        rw [coeff_binomial_mul]
        simp only [cast_choose]
      _ = PowerSeries.coeff k.toNat
            (PowerSeries.binomialSeries ℂ ((q : ℂ) + 1 / 2) * PowerSeries.mk A) := by
        rw [← mul_assoc, ← PowerSeries.binomialSeries_add]
      _ = _ := by
        rw [coeff_binomial_mul]
        simp only [PowerSeries.coeff_mk, aWeight]
  · simp [modePairs, hk]

/-- Match the analytic Taylor numerator and the formal Laurent numerator,
including the half-power on the selected collision sheet. -/
private theorem homogeneous_residue (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hR : R.val ∈ actualGrade ℒ leechUnit H)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    (hM : M % 2 = 1) (hK : K % 2 = 0) (hH : H % 2 = 1) (hJ : J % 2 = 0)
    (q p r : ℤ) (hbal : ((J : ℤ) - M - H - K - 4) / 2 + q + p + r = -2) :
    -(∑ ij ∈ modePairs (((5 + H + K) / 2 : ℕ) - (p : ℤ) - 1),
      bWeight r ij.2 * bProductCoeff true true M H K J R Q P S ij.1) +
    (∑ ij ∈ modePairs (((5 + M + K) / 2 : ℕ) - (q : ℤ) - 1),
      dWeight r ij.2 * bProductCoeff true true H M K J P Q R S ij.1) =
    ∑ ij ∈ modePairs (((6 + M + H) / 2 : ℕ) - (r : ℤ) - 1),
      aWeight q ij.2 * fixedAIterateCoeff true M H K J (fixedAExponent M H ij.1)
        P R Q.val S.val := by
  classical
  let a : ℕ := (5 + H + K) / 2
  let b : ℕ := (6 + M + H) / 2
  let c : ℕ := (5 + M + K) / 2
  let w : ℤ := ((J : ℤ) - M - H - K - 4) / 2
  let d := numeratorDegree M K H J
  let N := numerator M K H J P R Q S
  let A (m : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H m) P R Q.val S.val
  let β : ℂ := ((J : ℂ) - K + 1) / 2
  have hb : (M + H + 6) / 2 = b := by dsimp [b]; omega
  have hN : bbhhCommonNumerator M K H J P R Q S = N := by
    unfold bbhhCommonNumerator N numerator numeratorDegree energySum
    rfl
  have hdegree : (d : ℤ) = w + a + b + c := (cusp_exponents M K H J hM hK hH hJ).1
  have hhalf : (w : ℂ) + b - β = 1 / 2 := (cusp_exponents M K H J hM hK hH hJ).2.2.2
  obtain ⟨hdeg, hB, hD, hA, _, _⟩ :=
    bbhh_actual_formal_cusp_powerSeries_and_coeff M K H J P R Q S hP hQ hR hS
  rw [hN] at hB hD hA
  have hd : ((a : ℤ) + ((M + H + 6) / 2 : ℕ) + (1 + (J : ℤ) - H) / 2).toNat = d := rfl
  rw [hd, hb] at hD
  rw [hb] at hB
  have hDC : (d : ℂ) - c = (a : ℂ) + β + 1 / 2 := by
    have hdC := congrArg (fun t : ℤ => (t : ℂ)) hdegree
    push_cast at hdC
    linear_combination hdC + hhalf
  have hF : fusedNumeratorSeries N d c =
      PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.mk A := by
    rw [fusedNumeratorSeries_eq_support N d c (numerator_natDegree_le M K H J P R Q S)]
    change PowerSeries.mk A = _ at hA
    rw [hA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm, ← PowerSeries.binomialSeries_add]
    congr 2
    change (d : ℂ) - c - j = 1 / 2 + ((a : ℂ) + β - j)
    rw [hDC]
    ring
  have hj := coefficient_jacobi_of_cusp_series M K H J P R Q S hM hK hH hJ q p r
  dsimp only at hj
  have hD' : (exchangedNumerator N d b).toPowerSeries *
      (PowerSeries.invOneSubPow ℂ b).val =
      PowerSeries.mk (fun m => -bProductCoeff true true H M K J P Q R S m) := by
    exact hD.symm
  specialize hj hB.symm hD' hF
  have hidx : w + a + q + r + 1 = (a : ℤ) - p - 1 := by dsimp [w] at *; omega
  change (∑ ij ∈ modePairs (w + a + q + r + 1), bWeight r ij.2 *
      (-bProductCoeff true true M H K J R Q P S ij.1)) -
    (∑ ij ∈ modePairs ((c : ℤ) - q - 1), dWeight r ij.2 *
      (-bProductCoeff true true H M K J P Q R S ij.1)) =
    ∑ ij ∈ modePairs ((b : ℤ) - r - 1), ((Ring.choose q ij.2 : ℤ) : ℂ) *
      PowerSeries.coeff ij.1 (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) *
        PowerSeries.mk A) at hj
  rw [hidx, raw_iterate A q] at hj
  simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add] at hj
  simpa only [a, b, c, A] using hj

/-- Read the homogeneous coefficient sums on the literal raw selector grids. -/
private theorem homogeneous_mode_sums (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hR : R.val ∈ actualGrade ℒ leechUnit H)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hM : M % 2 = 1) (hK : K % 2 = 0) (hH : H % 2 = 1) (hJ : J % 2 = 0)
    (q p r : ℤ) (hbal : ((J : ℤ) - M - H - K - 4) / 2 + q + p + r = -2)
    (weightB weightD weightA : ℕ → ℂ) :
    let B := BBHHModeSum.product p (q+r) weightB
    let D := BBHHModeSum.product q (p+r) weightD
    let A := BBHHModeSum.iterate r (q+p+1) weightA
    let a : ℕ := (5 + H + K) / 2
    let b : ℕ := (6 + M + H) / 2
    let c : ℕ := (5 + M + K) / 2
    ((∑ᶠ j, B.weight j * bJointTerm true true R Q P S 1 1 (B.modes j)) =
      ∑ ij ∈ modePairs ((a : ℤ) - p - 1),
        weightB ij.2 * bProductCoeff true true M H K J R Q P S ij.1) ∧
    ((∑ᶠ j, D.weight j * bJointTerm true true P Q R S 1 1 (D.modes j)) =
      ∑ ij ∈ modePairs ((c : ℤ) - q - 1),
        weightD ij.2 * bProductCoeff true true H M K J P Q R S ij.1) ∧
    ((∑ᶠ j, A.weight j * aJointTerm true false P R Q S 1 1 (A.modes j)) =
      ∑ ij ∈ modePairs ((b : ℤ) - r - 1),
        weightA ij.2 * fixedAIterateCoeff true M H K J (fixedAExponent M H ij.1)
          P R Q.val S.val) := by
  intro B D A a b c
  have ha : 2 * (a : ℤ) = 5 + (H : ℤ) + K := by dsimp [a]; omega
  have hc : 2 * (c : ℤ) = 5 + (M : ℤ) + K := by dsimp [c]; omega
  have hb : 2 * (b : ℤ) = 6 + (M : ℤ) + H := by dsimp [b]; omega
  have htotal : -2 * (q + p + r) = (J : ℤ) - M - H - K := by omega
  have hHK : Odd ((H : ℤ) + K) := Int.odd_iff.mpr (by omega)
  have hMK : Odd ((M : ℤ) + K) := Int.odd_iff.mpr (by omega)
  have hMH : Even ((M : ℤ) + H) := Int.even_iff.mpr (by omega)
  refine ⟨finsum_eq_sum_modePairs
    (fun m j => weightB j * bProductCoeff true true M H K J R Q P S m) _ ?_ ?_,
    finsum_eq_sum_modePairs
    (fun m j => weightD j * bProductCoeff true true H M K J P Q R S m) _ ?_ ?_,
    finsum_eq_sum_modePairs
    (fun m j => weightA j * fixedAIterateCoeff true M H K J (fixedAExponent M H m)
      P R Q.val S.val) _ ?_ ?_⟩
  · intro m j hmj
    have hpair : B.modes j =
        (2 * (m : ℤ) - (6 + (H : ℤ) + K), (J : ℤ) - M - 2 * (m : ℤ)) := by
      apply Prod.ext <;> dsimp [B, BBHHModeSum.product, BBHHModeSum.downshift] <;> omega
    rw [hpair]
    simp only [B, BBHHModeSum.product, BBHHModeSum.downshift, bJointTerm, bProductCoeff,
      one_zpow, mul_one]
  · intro j hj
    have hz := b_inner_coeff_off_grid true H K R Q hR hQ hHK (B.modes j).1
      (fun m hm => by dsimp [B, BBHHModeSum.product, BBHHModeSum.downshift] at hm; omega)
    simp [bJointTerm, hz]
  · intro m j hmj
    have hpair : D.modes j =
        (2 * (m : ℤ) - (6 + (M : ℤ) + K), (J : ℤ) - H - 2 * (m : ℤ)) := by
      apply Prod.ext <;> dsimp [D, BBHHModeSum.product, BBHHModeSum.downshift] <;> omega
    rw [hpair]
    simp only [D, BBHHModeSum.product, BBHHModeSum.downshift, bJointTerm, bProductCoeff,
      one_zpow, mul_one]
  · intro j hj
    have hz := b_inner_coeff_off_grid true M K P Q hP hQ hMK (D.modes j).1
      (fun m hm => by dsimp [D, BBHHModeSum.product, BBHHModeSum.downshift] at hm; omega)
    simp [bJointTerm, hz]
  · intro m j hmj
    have hpair : A.modes j = (fixedAExponent M H m,
        (J : ℤ) - K - (fixedAExponent M H m + ((M : ℤ) + H + 6))) := by
      apply Prod.ext <;> dsimp [A, BBHHModeSum.iterate, BBHHModeSum.downshift, fixedAExponent] <;> omega
    rw [hpair]
    simp only [A, BBHHModeSum.iterate, BBHHModeSum.downshift, aJointTerm, fixedAIterateCoeff,
      one_zpow, mul_one]
  · intro j hj
    have hz := fixedAIterateCoeff_eq_zero_off_energy true M H K J (A.modes j).1
      P R Q.val S.val hP hR hMH (by
        rintro ⟨m, hm⟩
        dsimp [A, BBHHModeSum.iterate, BBHHModeSum.downshift, fixedAExponent] at hm
        omega)
    have he : (A.modes j).2 =
        (J : ℤ) - K - ((A.modes j).1 + ((M : ℤ) + H + 6)) := by
      dsimp [A, BBHHModeSum.iterate, BBHHModeSum.downshift]
      omega
    simp only [aJointTerm, he, one_zpow, mul_one]
    rw [← fixedAIterateCoeff, hz, mul_zero]

private theorem homogeneous_scalar (q p r : ℤ)
    (M H K J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hR : R.val ∈ actualGrade ℒ leechUnit H)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    bbhhScalarModeIdentity
      (BBHHModeSum.product p (q+r) (bWeight r))
      (BBHHModeSum.product q (p+r) (fun j => -dWeight r j))
      (BBHHModeSum.iterate r (q+p+1) (aWeight q)) P R Q S := by
  by_cases hzero : P = 0 ∨ R = 0 ∨ Q = 0 ∨ S = 0
  · rcases hzero with h | h | h | h <;>
      simp [bbhhScalarModeIdentity, ← bModeLinear_apply, ← aModeLinear_apply, h]
  push Not at hzero
  obtain ⟨hP₀, hR₀, hQ₀, hS₀⟩ := hzero
  have hM : M % 2 = 1 := grade_mod_two (s := true) hP hP₀
  have hH : H % 2 = 1 := grade_mod_two (s := true) hR hR₀
  have hK : K % 2 = 0 := grade_mod_two (s := false) hQ hQ₀
  have hJ : J % 2 = 0 := grade_mod_two (s := false) hS hS₀
  by_cases hbal : ((J : ℤ) - M - H - K - 4) / 2 + q + p + r = -2
  · obtain ⟨hB, hD, hA⟩ := homogeneous_mode_sums M K H J P R Q S hP hR hQ
      hM hK hH hJ q p r hbal (bWeight r) (fun j => -dWeight r j) (aWeight q)
    unfold bbhhScalarModeIdentity
    rw [hB, hD, hA]
    simp only [neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
    exact homogeneous_residue M K H J P R Q S hP hR hQ hS hM hK hH hJ q p r hbal
  · have htotal : -2 * (q + p + r) - 6 ≠ doubledDegree M K H J := by
      unfold doubledDegree
      omega
    have hB (j : ℕ) := bJointTerm_off_total hP hQ hR hS
      (Int.odd_iff.mpr (by omega)) 1 1
      ((BBHHModeSum.product p (q+r) (bWeight r)).modes j)
      (by dsimp [BBHHModeSum.product, BBHHModeSum.downshift]; omega)
    have hD (j : ℕ) := bJointTerm_off_total hR hQ hP hS
      (Int.odd_iff.mpr (by omega)) 1 1
      ((BBHHModeSum.product q (p+r) (fun j => -dWeight r j)).modes j)
      (by dsimp [BBHHModeSum.product, BBHHModeSum.downshift, doubledDegree] at *; omega)
    have hA (j : ℕ) := aJointTerm_off_total hP hQ hR hS
      (Int.even_iff.mpr (by omega)) 1 1
      ((BBHHModeSum.iterate r (q+p+1) (aWeight q)).modes j)
      (by dsimp [BBHHModeSum.iterate, BBHHModeSum.downshift]; omega)
    simp only [bbhhScalarModeIdentity, hB, hD, hA, mul_zero, finsum_zero, neg_zero, sub_zero]

/-- Coefficient Jacobi on the actual complementary twisted module. The
integers are the residue weights of X, Z, and X-Z. Both product terms use the
native right-skew and mixed fields, and the iterate uses the corrected fixed
field. The half-binomial comes from the positive collision sheet. -/
theorem bbhh_actual_vector_coefficient_jacobi
    (P R : TwistedOdd) (Q : TwistedEven) (q p r : ℤ) :
    -(∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ)) •
      (rightField ℒ leechUnit true P).coeff (-2 * (q+r) - 3 + 2 * (j : ℤ))
        ((mu true R).coeff (-2 * p - 3 - 2 * (j : ℤ)) Q)) +
    (∑ᶠ j : ℕ, ((-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ)) •
      (rightField ℒ leechUnit true R).coeff (-2 * (p+r) - 3 + 2 * (j : ℤ))
        ((mu true P).coeff (-2 * q - 3 - 2 * (j : ℤ)) Q)) =
    ∑ᶠ j : ℕ, Ring.choose ((q : ℂ) + 1 / 2) j •
      (⟨(correctedField ℒ leechUnit
        ((nu true P).coeff (-2 * r - 2 - 2 * (j : ℤ)) R).val).coeff
          (-2 * (q+p+1) - 2 + 2 * (j : ℤ)) Q.val,
        fixed_parity_preserved ℒ leechUnit (paritySign false) _ _ Q.val Q.property⟩ : TwistedEven) := by
  have h := bbhh_vector_mode_identity_of_homogeneous
    (BBHHModeSum.product p (q+r) (bWeight r))
    (BBHHModeSum.product q (p+r) (fun j => -dWeight r j))
    (BBHHModeSum.iterate r (q+p+1) (aWeight q)) (homogeneous_scalar q p r) P R Q
  let D := BBHHModeSum.product q (p+r) (dWeight r)
  let Dneg := BBHHModeSum.product q (p+r) (fun j => -dWeight r j)
  have hneg : (∑ᶠ j, Dneg.weight j • bbhhBVectorTerm R P Q (Dneg.modes j)) =
      -(∑ᶠ j, D.weight j • bbhhBVectorTerm R P Q (D.modes j)) := by
    calc
      _ = ∑ᶠ j, -(D.weight j • bbhhBVectorTerm R P Q (D.modes j)) := by
        apply congrArg (fun f : ℕ → TwistedEven => ∑ᶠ j, f j)
        funext j
        apply Subtype.ext
        change (-dWeight r j) • (bbhhBVectorTerm R P Q (D.modes j)).val =
          -(dWeight r j • (bbhhBVectorTerm R P Q (D.modes j)).val)
        exact neg_smul (dWeight r j) (bbhhBVectorTerm R P Q (D.modes j)).val
      _ = _ := finsum_neg_distrib (fun j : ℕ =>
        D.weight j • bbhhBVectorTerm R P Q (D.modes j))
  rw [hneg] at h
  let B := BBHHModeSum.product p (q+r) (bWeight r)
  have hsign : -(∑ᶠ j, B.weight j • bbhhBVectorTerm P R Q (B.modes j)) -
      -(∑ᶠ j, D.weight j • bbhhBVectorTerm R P Q (D.modes j)) =
      -(∑ᶠ j, B.weight j • bbhhBVectorTerm P R Q (B.modes j)) +
      (∑ᶠ j, D.weight j • bbhhBVectorTerm R P Q (D.modes j)) := by
    apply Subtype.ext
    exact sub_neg_eq_add _ _
  exact hsign.symm.trans h

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHActualVectorJacobi
