/- GID: D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NormFourLowestGrades
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual norm-four twisted zero modes and complete first half-oscillator grade. -/

/-
Classical twisted lattice construction: Frenkel--Lepowsky--Meurman;
Dong--Nagatomo, math/9808088, section 3.2;
Bakalov--Kac, math/0402315, section 4.
The existing suppliers retain their respective copyright and attribution.
-/

import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import Batteries.Tactic.OpenPrivate

/-! Actual norm-four zero modes on the twisted ground and complete first half-oscillator grade. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open private quadratic_field normal_pair_coeff shift_identity_coeff
  current_ground_zero_charge
  from D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
open private charge_pairing from D5.S3.VertexAlgebra.LatticeSugawaraConformal

namespace D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

open _root_.D5.S3.VertexAlgebra.Lattice
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraConformal LatticeActualAnnihilation
open LatticeHalfFock LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedMonodromy
open LatticeHalfFockGroundProducts LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace MvPolynomial
open HalfFockSpectralFiberSource
open scoped BigOperators TensorProduct

noncomputable section

/-- Physical zero mode: the native exponent is twice the physical exponent. -/
def zeroMode (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (s : ℂ) :
    Module.End ℂ (ActualTensor D hu) :=
  (correctedField D hu (NormFourVirasoroVector.vector D a s)).coeff (-4)

private theorem half_creation_zero (D : LatticeData) (a : Charge D) :
    halfCreationCoeff D a 0 = 1 := by
  simpa [halfCreationCoeff] using LatticeHalfFockChargedCoefficients.exponential_constant D a

private theorem half_creation_one (D : LatticeData) (a : Charge D) :
    halfCreationCoeff D a 1 = (2 : ℂ) • chargePolynomial D a := by
  have h := congrArg (PowerSeries.coeff 0)
    (LatticeHalfFockChargedCoefficients.exponential_derivative D a)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
  simpa [Finset.Nat.antidiagonal_zero,
    LatticeHalfFockChargedCoefficients.exponential_constant,
    series_derivative_coeff, halfCreationCoeff, chargePolynomial] using h

/- The degree-one translated polynomial has its entire support in {0,1}.
   This is a support proof, not a postulated coefficient readout. -/
private theorem translated_X_support (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) :
    (halfTranslatedPolynomial D a (X (i, 0))).support ⊆ {0, 1} := by
  classical
  intro n hn
  by_contra outside
  have hn0 : n ≠ 0 := by intro h; exact outside (by simp [h])
  have hn1 : n ≠ 1 := by intro h; exact outside (by simp [h])
  have hz : (halfTranslatedPolynomial D a (X (i, 0))).coeff n = 0 := by
    simp [halfTranslatedPolynomial, halfTranslationVariable, omega,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X,
      hn0, Ne.symm hn1]
  exact (Polynomial.mem_support_iff.mp hn) hz

private theorem charged_X_tail (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (e : ℤ) :
    Function.support (oscillatorTerm D a e (X (i, 0))) ⊆ ({0, 1} : Finset ℕ) := by
  intro n hn
  exact translated_X_support D a i (term_support D a e _ hn)

private theorem charged_X_coefficient (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (i : Fin D.rank) :
    oscillatorCoefficient D a (-4) (X (i, 0)) =
      X (i, 0) - (2 * (bilinear D a (unitCharge D i) : ℂ)) • chargePolynomial D a := by
  classical
  change (∑ᶠ n : ℕ, oscillatorTerm D a (-4) (X (i, 0)) n) = _
  rw [finsum_eq_sum_of_support_subset _ (charged_X_tail D a i (-4))]
  simp [oscillatorTerm, halfTranslatedPolynomial, halfTranslationVariable,
    chargeNorm, ha, omega, Polynomial.coeff_C_mul,
    half_creation_zero, half_creation_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

private theorem current_ground_nonneg (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (hm : 0 ≤ m) : current D i m 1 = 0 := by
  simp [current, not_lt.mpr hm, ← annihilation_apply,
    Derivation.map_one_eq_zero]

private theorem current_X_nonneg (D : LatticeData) (i k : Fin D.rank)
    (m : ℤ) (hm : 0 ≤ m) :
    current D i m (X (k, 0)) =
      if m = 0 then ((D.G i k : ℂ) / 2) • (1 : Oscillator D) else 0 := by
  by_cases hz : m = 0
  · subst m
    simp [current, annihilate_X, frequency, smul_smul, div_eq_mul_inv, mul_comm]
  · have hn : m.toNat ≠ 0 := by omega
    simp [current, not_lt.mpr hm, annihilate_X, hn, hz]

private theorem normal_pair_ground (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) : normalPair D i j m (-m-1) 1 = 0 := by
  by_cases hm : m < 0
  · simp [normalPair, hm, Module.End.mul_apply,
      current_ground_nonneg D j (-m-1) (by omega)]
  · simp [normalPair, hm, Module.End.mul_apply,
      current_ground_nonneg D i m (by omega)]

/-- Complete surviving-index contraction: only modes -1 and 0 can survive. -/
private theorem normal_pair_X (D : LatticeData) (i j k : Fin D.rank) (m : ℤ) :
    normalPair D i j m (-m-1) (X (k, 0)) =
      if m = -1 then ((D.G j k : ℂ) / 2) • X (i, 0)
      else if m = 0 then ((D.G i k : ℂ) / 2) • X (j, 0) else 0 := by
  by_cases hneg : m < 0
  · rw [normalPair, ite_eq_left hneg, Module.End.mul_apply,
      current_X_nonneg D j k (-m-1) (by omega)]
    by_cases hm : m = -1
    · subst m
      simp [current, map_smul, LinearMap.mulLeft_apply]
    · simp [hm, show -m-1 ≠ 0 by omega, show m ≠ 0 by omega]
  · rw [normalPair, ite_eq_right hneg, Module.End.mul_apply,
      current_X_nonneg D i k m (by omega)]
    by_cases hm : m = 0
    · subst m
      simp [current, map_smul, LinearMap.mulLeft_apply]
    · simp [hm, show m ≠ -1 by omega]

private theorem tensor_pair_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (m : ℤ) (u : ActualGround D hu) :
    tensorPair D (ActualGround D hu) i j m (-m-1) (1 ⊗ₜ[ℂ] u) = 0 := by
  simp [tensorPair, tensorEnd, TensorProduct.map_tmul, normal_pair_ground]

private theorem tensor_pair_X (D : LatticeData) (hu : IsUnit D.G.det)
    (i j k : Fin D.rank) (m : ℤ) (u : ActualGround D hu) :
    tensorPair D (ActualGround D hu) i j m (-m-1) (X (k, 0) ⊗ₜ[ℂ] u) =
      if m = -1 then ((D.G j k : ℂ) / 2) • (X (i, 0) ⊗ₜ[ℂ] u)
      else if m = 0 then ((D.G i k : ℂ) / 2) • (X (j, 0) ⊗ₜ[ℂ] u) else 0 := by
  simp only [tensorPair, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    normal_pair_X]
  split_ifs <;> simp [← TensorProduct.smul_tmul']

private theorem tensor_pair_X_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (i j k : Fin D.rank) (u : ActualGround D hu) :
    Function.support (fun m : ℤ => tensorPair D (ActualGround D hu) i j m (-m-1)
      (X (k, 0) ⊗ₜ[ℂ] u)) ⊆ ({-1, 0} : Finset ℤ) := by
  intro m hm
  by_contra outside
  have hm1 : m ≠ -1 := by intro h; exact outside (by simp [h])
  have hm0 : m ≠ 0 := by intro h; exact outside (by simp [h])
  exact hm (by simp [tensor_pair_X, hm1, hm0])

private theorem normal_ground_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (u : ActualGround D hu) :
    (singletonLinear D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j)).coeff
      (-4) (1 ⊗ₜ[ℂ] u) = 0 := by
  rw [normal_pair_coeff]
  rw [ite_eq_left (by norm_num : (-4 : ℤ) % 2 = 0),
    show (-(-4 : ℤ)-4)/2 = 0 by norm_num]
  simp only [zero_sub]
  simp only [tensor_pair_ground, finsum_zero]

private theorem normal_X_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (i j k : Fin D.rank) (u : ActualGround D hu) :
    (singletonLinear D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j)).coeff
      (-4) (X (k, 0) ⊗ₜ[ℂ] u) =
      ((D.G j k : ℂ) / 2) • (X (i, 0) ⊗ₜ[ℂ] u) +
      ((D.G i k : ℂ) / 2) • (X (j, 0) ⊗ₜ[ℂ] u) := by
  classical
  rw [normal_pair_coeff]
  rw [ite_eq_left (by norm_num : (-4 : ℤ) % 2 = 0),
    show (-(-4 : ℤ)-4)/2 = 0 by norm_num]
  simp only [zero_sub]
  rw [finsum_eq_sum_of_support_subset _ (tensor_pair_X_tail D hu i j k u)]
  simp [tensor_pair_X]

private theorem quadratic_ground_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (u : ActualGround D hu) :
    (correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff
      (-4) (1 ⊗ₜ[ℂ] u) =
      ((D.G i j : ℂ) / 8) • (1 ⊗ₜ[ℂ] u) := by
  rw [quadratic_field]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, normal_ground_zero, shift_identity_coeff]
  simp [div_eq_mul_inv, mul_comm]

private theorem quadratic_X_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (i j k : Fin D.rank) (u : ActualGround D hu) :
    (correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff
      (-4) (X (k, 0) ⊗ₜ[ℂ] u) =
      ((D.G j k : ℂ) / 2) • (X (i, 0) ⊗ₜ[ℂ] u) +
      ((D.G i k : ℂ) / 2) • (X (j, 0) ⊗ₜ[ℂ] u) +
      ((D.G i j : ℂ) / 8) • (X (k, 0) ⊗ₜ[ℂ] u) := by
  rw [quadratic_field]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, normal_X_zero, shift_identity_coeff]
  simp [div_eq_mul_inv, mul_comm]

private theorem charge_square_expansion (D : LatticeData) (a : Charge D) :
    (chargePolynomial D a)^2 = ∑ i : Fin D.rank, ∑ j : Fin D.rank,
      ((a i : ℂ) * (a j : ℂ)) • (X (i, 0) * X (j, 0) : Oscillator D) := by
  simp only [pow_two, chargePolynomial, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (X (j, 0) : Oscillator D) (X (i, 0))]

private theorem gram_contraction (D : LatticeData) (a : Charge D) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (a i : ℂ) * (a j : ℂ) * (D.G i j : ℂ)) = (bilinear D a a : ℂ) := by
  simp only [bilinear, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem gram_contraction_div (D : LatticeData) (a : Charge D) (c : ℂ) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (a i : ℂ) * (a j : ℂ) * ((D.G i j : ℂ) / c)) = (bilinear D a a : ℂ) / c := by
  calc
    _ = (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        (a i : ℂ) * (a j : ℂ) * (D.G i j : ℂ)) / c := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [gram_contraction]

private theorem coordinate_pairing (D : LatticeData) (a : Charge D) (k : Fin D.rank) :
    (∑ i : Fin D.rank, (a i : ℂ) * (D.G i k : ℂ)) =
      (bilinear D a (unitCharge D k) : ℂ) := by
  simp [bilinear, unitCharge]

private theorem quadratic_state_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (v : ActualTensor D hu) :
    (correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff (-4) v =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, ((a i : ℂ) * (a j : ℂ)) •
        (correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff (-4) v := by
  unfold NormFourVirasoroVector.quadraticState
  rw [charge_square_expansion]
  simp only [Finsupp.single_finsetSum, ← Finsupp.smul_single, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]

private theorem quadratic_along_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (u : ActualGround D hu) :
    (correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff
      (-4) (1 ⊗ₜ[ℂ] u) = (1 / 2 : ℂ) • (1 ⊗ₜ[ℂ] u) := by
  rw [quadratic_state_expansion]
  simp only [quadratic_ground_zero, smul_smul, ← Finset.sum_smul]
  have scalar : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (a i : ℂ) * (a j : ℂ) * ((D.G i j : ℂ) / 8)) = (1 / 2 : ℂ) := by
    rw [gram_contraction_div, ha]
    norm_num
  rw [scalar]

set_option maxHeartbeats 4000000 in
-- The finite double Gram contraction is normalized over all lattice coordinates.
private theorem quadratic_along_X (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (k : Fin D.rank)
    (u : ActualGround D hu) :
    (correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff
      (-4) (X (k, 0) ⊗ₜ[ℂ] u) =
      ((1 / 2 : ℂ) • X (k, 0) +
        (bilinear D a (unitCharge D k) : ℂ) • chargePolynomial D a) ⊗ₜ[ℂ] u := by
  classical
  rw [quadratic_state_expansion]
  simp only [quadratic_X_zero, smul_add, smul_smul, Finset.sum_add_distrib]
  have first : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      ((a i : ℂ) * (a j : ℂ) * ((D.G j k : ℂ) / 2)) • (X (i, 0) ⊗ₜ[ℂ] u)) =
      ((bilinear D a (unitCharge D k) : ℂ) / 2) •
        (chargePolynomial D a ⊗ₜ[ℂ] u) := by
    simp only [← Finset.sum_smul]
    have inner (i : Fin D.rank) :
        (∑ j : Fin D.rank, (a i : ℂ) * (a j : ℂ) * ((D.G j k : ℂ) / 2)) =
          (a i : ℂ) * ((bilinear D a (unitCharge D k) : ℂ) / 2) := by
      calc
        _ = ((a i : ℂ) / 2) * ∑ j : Fin D.rank, (a j : ℂ) * (D.G j k : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [coordinate_pairing]; ring
    simp_rw [inner]
    simp only [chargePolynomial, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  have second : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      ((a i : ℂ) * (a j : ℂ) * ((D.G i k : ℂ) / 2)) • (X (j, 0) ⊗ₜ[ℂ] u)) =
      ((bilinear D a (unitCharge D k) : ℂ) / 2) •
        (chargePolynomial D a ⊗ₜ[ℂ] u) := by
    calc
      _ = ∑ j : Fin D.rank, ∑ i : Fin D.rank,
          ((a j : ℂ) * (a i : ℂ) * ((D.G i k : ℂ) / 2)) •
            (X (j, 0) ⊗ₜ[ℂ] u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        ring
      _ = _ := first
  have third : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      ((a i : ℂ) * (a j : ℂ) * ((D.G i j : ℂ) / 8)) • ((X (k, 0) : Oscillator D) ⊗ₜ[ℂ] u)) =
      (1 / 2 : ℂ) • ((X (k, 0) : Oscillator D) ⊗ₜ[ℂ] u) := by
    simp only [← Finset.sum_smul]
    have scalar : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        (a i : ℂ) * (a j : ℂ) * ((D.G i j : ℂ) / 8)) = (1 / 2 : ℂ) := by
      rw [gram_contraction_div, ha]
      norm_num
    rw [scalar]
  rw [first, second, third]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  module

private theorem charged_ground_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (u : ActualGround D hu) :
    chargedCoefficient D hu a (-4) (1 ⊗ₜ[ℂ] u) =
      (1 / 16 : ℂ) • (1 ⊗ₜ[ℂ] groundAction D hu a u) := by
  rw [charged_vacuum_coefficient]
  norm_num [chargeScalar, chargeNorm, ha, half_creation_zero]

private theorem charged_X_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (i : Fin D.rank)
    (u : ActualGround D hu) :
    chargedCoefficient D hu a (-4) (X (i, 0) ⊗ₜ[ℂ] u) =
      (1 / 16 : ℂ) •
        ((X (i, 0) - (2 * (bilinear D a (unitCharge D i) : ℂ)) •
          chargePolynomial D a) ⊗ₜ[ℂ] groundAction D hu a u) := by
  simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
    charged_X_coefficient D a ha]
  norm_num [chargeScalar, chargeNorm, ha]

private theorem charged_state_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (v : ActualTensor D hu) :
    (correctedField D hu (NormFourVirasoroVector.chargedState D a)).coeff (-4) v =
      (2 : ℂ) • chargedCoefficient D hu a (-4) v := by
  change (correctedField D hu
    (Finsupp.single a (1 : Oscillator D) + Finsupp.single (-a) 1)).coeff (-4) v = _
  simp only [map_add, Pi.add_apply, LinearMap.add_apply,
    corrected_singleton_coeff_charged, chargedField, HVertexOperator.coeff_of_coeff]
  have h := charged_coefficient_coordinate_monodromy D hu a (-4)
  norm_num at h
  rw [h]
  module

private theorem zeroMode_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) (v : ActualTensor D hu) :
    zeroMode D hu a s v =
      (1 / 16 : ℂ) •
        (correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff (-4) v +
      (s / 2) • chargedCoefficient D hu a (-4) v := by
  simp only [zeroMode, NormFourVirasoroVector.vector, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    charged_state_zero, smul_smul]
  congr 1
  congr 1
  ring

/-- The actual corrected norm-four field on every chosen actual ground vector.
    No sign-square premise is needed for either action computation. -/
theorem zeroMode_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (u : ActualGround D hu) :
    zeroMode D hu a s (1 ⊗ₜ[ℂ] u) =
      (1 / 32 : ℂ) • (1 ⊗ₜ[ℂ] u) +
      (s / 32) • (1 ⊗ₜ[ℂ] groundAction D hu a u) := by
  rw [zeroMode_expansion, quadratic_along_ground D hu a ha,
    charged_ground_zero D hu a ha]
  simp only [smul_smul]
  module

/-- The actual corrected norm-four field on every lowest half-mode tensor. -/
theorem zeroMode_X (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (i : Fin D.rank) (u : ActualGround D hu) :
    zeroMode D hu a s (X (i, 0) ⊗ₜ[ℂ] u) =
      ((1 / 32 : ℂ) • X (i, 0) +
        ((bilinear D a (unitCharge D i) : ℂ) / 16) • chargePolynomial D a) ⊗ₜ[ℂ] u +
      (s / 32) • ((X (i, 0) -
        (2 * (bilinear D a (unitCharge D i) : ℂ)) • chargePolynomial D a) ⊗ₜ[ℂ]
          groundAction D hu a u) := by
  rw [zeroMode_expansion, quadratic_along_X D hu a ha,
    charged_X_zero D hu a ha]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', smul_add, smul_smul]
  module

/- Complete actual-grade identification. The only weight-one monomials are
   the native variables X_(i,0); the rank-zero case needs no exception. -/
private theorem oddWeight_one_iff (D : LatticeData) (d : OddMonomial D) :
    oddWeight D d = 1 ↔ ∃ i : Fin D.rank, d = Finsupp.single (i, 0) 1 := by
  classical
  constructor
  · intro hd
    have hexists : ∃ x : Index D, d x ≠ 0 := by
      by_contra h
      push Not at h
      have hz : d = 0 := Finsupp.ext h
      simp [hz, oddWeight] at hd
    obtain ⟨x, hx⟩ := hexists
    have hxmem : x ∈ d.support := Finsupp.mem_support_iff.mpr hx
    have hb := oddFiber_support_bounds D 1 ⟨d, hd⟩ x hxmem
    have hxmode : x.2 = 0 := by dsimp [omega] at hb; omega
    have he := oddFiber_exponent_bound D 1 ⟨d, hd⟩ x
    change d x ≤ 1 at he
    have hxexp : d x = 1 := by omega
    have total : (∑ y ∈ d.support, d y * omega D y) = 1 := by
      simpa only [oddWeight, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hd
    have distinguished : d x * omega D x = 1 := by simp [hxexp, omega, hxmode]
    have erased : (∑ y ∈ d.support.erase x, d y * omega D y) = 0 := by
      have h := Finset.sum_erase_add d.support (fun y => d y * omega D y) hxmem
      rw [total, distinguished] at h
      omega
    have other (y : Index D) (hy : y ≠ x) : d y = 0 := by
      by_cases hys : y ∈ d.support
      · have hye : y ∈ d.support.erase x := Finset.mem_erase.mpr ⟨hy, hys⟩
        have hle : d y * omega D y ≤ ∑ z ∈ d.support.erase x, d z * omega D z :=
          Finset.single_le_sum (f := fun z : Index D => d z * omega D z)
            (fun z hz => Nat.zero_le _) hye
        rw [erased] at hle
        have hm : d y * omega D y = 0 := Nat.eq_zero_of_le_zero hle
        exact (Nat.mul_eq_zero.mp hm).resolve_right (by simp [omega])
      · exact Finsupp.notMem_support_iff.mp hys
    have hxprod : x = (x.1, 0) := Prod.ext rfl hxmode
    have hsingle : d = Finsupp.single x 1 := by
      apply Finsupp.ext
      intro y
      by_cases hy : y = x
      · subst y
        simp only [Finsupp.single_eq_same, hxexp]
      · rw [other y hy, Finsupp.single_eq_of_ne hy]
    exact ⟨x.1, hsingle.trans (congrArg (fun z : Index D => Finsupp.single z (1 : ℕ)) hxprod)⟩
  · rintro ⟨i, rfl⟩
    simp [oddWeight, Finsupp.weight_apply, Finsupp.sum, omega]

private theorem X_tmul_mem_actualGrade_one (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (u : ActualGround D hu) :
    X (i, 0) ⊗ₜ[ℂ] u ∈ actualGrade D hu 1 := by
  have oscillator : L D (actualInverse D) 0 (X (i, 0)) =
      ((D.rank : ℂ) / 16 + 1 / 2) • (X (i, 0) : Oscillator D) := by
    have h := L_zero_monomial_coeff D (actualInverse D)
      (actualInverse_left D hu) (actualInverse_right D hu)
      (Finsupp.single (i, 0) 1) (1 : ℂ)
    simpa [MvPolynomial.X] using h
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  simp [actualTensorL0, tensorL, tensorEnd, TensorProduct.map_tmul,
    oscillator, ← TensorProduct.smul_tmul']

/-- Equality with the COMPLETE actual eigengrade, not a selected subspace.
    The reverse inclusion uses the original tensor L0; the forward inclusion
    uses the full production ambient basis and the weight-one classification. -/
theorem actualGrade_one_eq_span (D : LatticeData) (hu : IsUnit D.G.det) :
    actualGrade D hu 1 = Submodule.span ℂ
      (Set.range (fun x : Fin D.rank × ActualGround D hu =>
        (X (x.1, 0) : Oscillator D) ⊗ₜ[ℂ] x.2)) := by
  apply le_antisymm
  · rw [actual_grade_span]
    apply Submodule.span_le.mpr
    rintro v ⟨⟨⟨d, hd⟩, b⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (oddWeight_one_iff D d).mp hd
    apply Submodule.subset_span
    refine ⟨(i, Pi.single b (1 : ℂ)), ?_⟩
    simp [actualGradeVector, actual_basis_apply, MvPolynomial.X]
  · apply Submodule.span_le.mpr
    rintro v ⟨⟨i, u⟩, rfl⟩
    exact X_tmul_mem_actualGrade_one D hu i u

private theorem P_tmul_mem_actualGrade_one (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (u : ActualGround D hu) :
    chargePolynomial D a ⊗ₜ[ℂ] u ∈ actualGrade D hu 1 := by
  classical
  simp only [chargePolynomial, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']
  apply Submodule.sum_mem
  intro i hi
  exact (actualGrade D hu 1).smul_mem _ (X_tmul_mem_actualGrade_one D hu i u)

private theorem opposite_phase (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D a (-a) = 1 := by
  have hneg : lowerCocycleExponent D a (-a) = -lowerCocycleExponent D a a := by
    unfold lowerCocycleExponent
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    abel
  rw [epsilon, hneg,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, ha]
  norm_num [paritySign]

private theorem ground_square (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) :
    groundAction D hu a * groundAction D hu a = 1 := by
  have h := ground_action_product D hu a (-a)
  rw [ground_neg, opposite_phase D a ha, add_neg_cancel,
    current_ground_zero_charge, one_smul] at h
  exact h

private theorem ground_square_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (u : ActualGround D hu) :
    groundAction D hu a (groundAction D hu a u) = u := by
  have h := LinearMap.congr_fun (ground_square D hu a ha) u
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h

private theorem charge_pairing_complex (D : LatticeData) (a : Charge D) :
    (∑ i : Fin D.rank, (a i : ℂ) * (bilinear D a (unitCharge D i) : ℂ)) =
      (bilinear D a a : ℂ) := by
  exact_mod_cast charge_pairing D a a

private theorem zeroMode_X_expanded (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (i : Fin D.rank) (u : ActualGround D hu) :
    zeroMode D hu a s (X (i, 0) ⊗ₜ[ℂ] u) =
      (1 / 32 : ℂ) • (X (i, 0) ⊗ₜ[ℂ] u) +
      ((bilinear D a (unitCharge D i) : ℂ) / 16) • (chargePolynomial D a ⊗ₜ[ℂ] u) +
      (s / 32) • (X (i, 0) ⊗ₜ[ℂ] groundAction D hu a u) -
      ((s * (bilinear D a (unitCharge D i) : ℂ)) / 16) •
        (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u) := by
  rw [zeroMode_X D hu a ha]
  simp only [TensorProduct.add_tmul, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul',
    smul_sub, smul_smul]
  module

set_option maxHeartbeats 4000000 in
-- The four coordinate sums are normalized before applying the norm-four identity.
/-- The norm-four contraction on the actual charge direction, used for the
    iterated zero-mode computation. This is where P^2 = 4P enters. -/
private theorem zeroMode_P (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (u : ActualGround D hu) :
    zeroMode D hu a s (chargePolynomial D a ⊗ₜ[ℂ] u) =
      (9 / 32 : ℂ) • (chargePolynomial D a ⊗ₜ[ℂ] u) -
      (7 * s / 32) • (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u) := by
  classical
  have hp (v : ActualGround D hu) :
      (∑ i : Fin D.rank, (a i : ℂ) • (X (i, 0) ⊗ₜ[ℂ] v)) =
        chargePolynomial D a ⊗ₜ[ℂ] v := by
    simp only [chargePolynomial, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']
  have hb : (∑ i : Fin D.rank,
      (a i : ℂ) * (bilinear D a (unitCharge D i) : ℂ)) = (4 : ℂ) := by
    rw [charge_pairing_complex, ha]
    norm_num
  conv_lhs => rw [← hp u, map_sum]
  simp only [map_smul, zeroMode_X_expanded D hu a ha, smul_add, smul_sub,
    smul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have sum1 : (∑ i : Fin D.rank,
      ((a i : ℂ) * (1 / 32 : ℂ)) • (X (i, 0) ⊗ₜ[ℂ] u)) =
      (1 / 32 : ℂ) • (chargePolynomial D a ⊗ₜ[ℂ] u) := by
    rw [← hp u, Finset.smul_sum]
    simp only [smul_smul, mul_comm]
  have sum2 : (∑ i : Fin D.rank,
      ((a i : ℂ) * ((bilinear D a (unitCharge D i) : ℂ) / 16)) •
        (chargePolynomial D a ⊗ₜ[ℂ] u)) =
      (1 / 4 : ℂ) • (chargePolynomial D a ⊗ₜ[ℂ] u) := by
    rw [← Finset.sum_smul]
    have h : (∑ i : Fin D.rank,
        (a i : ℂ) * ((bilinear D a (unitCharge D i) : ℂ) / 16)) = (1 / 4 : ℂ) := by
      calc
        _ = (∑ i : Fin D.rank,
            (a i : ℂ) * (bilinear D a (unitCharge D i) : ℂ)) / 16 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [hb]; norm_num
    rw [h]
  have sum3 : (∑ i : Fin D.rank,
      ((a i : ℂ) * (s / 32)) • (X (i, 0) ⊗ₜ[ℂ] groundAction D hu a u)) =
      (s / 32) • (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u) := by
    rw [← hp (groundAction D hu a u), Finset.smul_sum]
    simp only [smul_smul, mul_comm]
  have sum4 : (∑ i : Fin D.rank,
      ((a i : ℂ) * (s * (bilinear D a (unitCharge D i) : ℂ) / 16)) •
        (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u)) =
      (s / 4) • (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u) := by
    rw [← Finset.sum_smul]
    have h : (∑ i : Fin D.rank,
        (a i : ℂ) * (s * (bilinear D a (unitCharge D i) : ℂ) / 16)) = s / 4 := by
      calc
        _ = s / 16 * ∑ i : Fin D.rank,
            (a i : ℂ) * (bilinear D a (unitCharge D i) : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [hb]; ring
    rw [h]
  rw [sum1, sum2, sum3, sum4]
  module

/- A ring identity on the FOUR ACTUAL tensors X_i⊗u, P_a⊗u,
   X_i⊗Uu, P_a⊗Uu. This does not introduce a four-dimensional model:
   these tensors may be dependent or zero. The polynomial identity below
   is proved by repeated application of the actual coefficient formulas.
   Its RHS keeps the exact s ^ 2-1 factor, so `module` needs no spectral
   assumptions or hidden use of an eigenbasis. -/
set_option maxHeartbeats 4000000 in
-- Repeated action expands the cubic on the four actual tensor expressions.
private theorem polynomial_X_identity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (i : Fin D.rank) (u : ActualGround D hu) :
    (zeroMode D hu a s *
      (zeroMode D hu a s - (1 / 16 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))) *
      (zeroMode D hu a s - (1 / 2 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))))
        (X (i, 0) ⊗ₜ[ℂ] u) =
      ((s ^ 2 - 1) / 32768) •
        ((-15 : ℂ) • (X (i, 0) ⊗ₜ[ℂ] u) +
          (114 * (bilinear D a (unitCharge D i) : ℂ)) •
            (chargePolynomial D a ⊗ₜ[ℂ] u) +
          s • (X (i, 0) ⊗ₜ[ℂ] groundAction D hu a u) -
          (86 * s * (bilinear D a (unitCharge D i) : ℂ)) •
            (chargePolynomial D a ⊗ₜ[ℂ] groundAction D hu a u)) := by
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_sub, map_smul,
    zeroMode_X_expanded D hu a ha, zeroMode_P D hu a ha,
    ground_square_apply D hu a ha]
  module

private theorem polynomial_X (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (i : Fin D.rank) (u : ActualGround D hu) :
    (zeroMode D hu a s *
      (zeroMode D hu a s - (1 / 16 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))) *
      (zeroMode D hu a s - (1 / 2 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))))
        (X (i, 0) ⊗ₜ[ℂ] u) = 0 := by
  rw [polynomial_X_identity D hu a ha, hs, sub_self, zero_div, zero_smul]

/-- The actual norm-four polynomial vanishes on EVERY vector of the COMPLETE
    actual odd grade one. The complete-grade equality above is essential to
    this proof; the kernel argument includes all finite linear combinations. -/
private theorem zeroMode_polynomial_actualGrade_one (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (v : ActualTensor D hu) (hv : v ∈ actualGrade D hu 1) :
    (zeroMode D hu a s *
      (zeroMode D hu a s - (1 / 16 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))) *
      (zeroMode D hu a s - (1 / 2 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu)))) v = 0 := by
  let F : Module.End ℂ (ActualTensor D hu) := zeroMode D hu a s *
    (zeroMode D hu a s - (1 / 16 : ℂ) • 1) *
    (zeroMode D hu a s - (1 / 2 : ℂ) • 1)
  have span_le : actualGrade D hu 1 ≤ LinearMap.ker F := by
    rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨⟨i, u⟩, rfl⟩
    exact polynomial_X D hu a ha s hs i u
  exact span_le hv

/-- Preservation is proved in the genuine original L0 eigengrade. -/
private theorem zeroMode_preserves_actualGrade_one (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (v : ActualTensor D hu) (hv : v ∈ actualGrade D hu 1) :
    zeroMode D hu a s v ∈ actualGrade D hu 1 := by
  have inclusion : actualGrade D hu 1 ≤
      (actualGrade D hu 1).comap (zeroMode D hu a s) := by
    conv_lhs => rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨⟨i, u⟩, rfl⟩
    change zeroMode D hu a s (X (i, 0) ⊗ₜ[ℂ] u) ∈ actualGrade D hu 1
    rw [zeroMode_X_expanded D hu a ha]
    exact (actualGrade D hu 1).sub_mem
      ((actualGrade D hu 1).add_mem
        ((actualGrade D hu 1).add_mem
          ((actualGrade D hu 1).smul_mem _ (X_tmul_mem_actualGrade_one D hu i u))
          ((actualGrade D hu 1).smul_mem _ (P_tmul_mem_actualGrade_one D hu a u)))
        ((actualGrade D hu 1).smul_mem _
          (X_tmul_mem_actualGrade_one D hu i (groundAction D hu a u))))
      ((actualGrade D hu 1).smul_mem _
        (P_tmul_mem_actualGrade_one D hu a (groundAction D hu a u)))
  exact inclusion hv

def actualGradeOneZeroMode (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    Module.End ℂ (actualGrade D hu 1) :=
  (zeroMode D hu a s).restrict (zeroMode_preserves_actualGrade_one D hu a ha s)

/-- Endomorphism form of L(L-1/16)(L-1/2)=0 on the actual grade. -/
theorem actualGradeOneZeroMode_polynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    actualGradeOneZeroMode D hu a ha s *
      (actualGradeOneZeroMode D hu a ha s -
        (1 / 16 : ℂ) • (1 : Module.End ℂ (actualGrade D hu 1))) *
      (actualGradeOneZeroMode D hu a ha s -
        (1 / 2 : ℂ) • (1 : Module.End ℂ (actualGrade D hu 1))) = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change
    (zeroMode D hu a s *
      (zeroMode D hu a s - (1 / 16 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))) *
      (zeroMode D hu a s - (1 / 2 : ℂ) • (1 : Module.End ℂ (ActualTensor D hu))))
        (v : ActualTensor D hu) = 0
  exact zeroMode_polynomial_actualGrade_one D hu a ha s hs v v.2

end
end D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
