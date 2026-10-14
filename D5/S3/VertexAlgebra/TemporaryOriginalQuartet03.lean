import D5.S3.VertexAlgebra.TemporaryOriginalQuartet02

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def coordinate (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (index : Index D) : Oscillator D :=
  ∑ original, frame index.1 original • MvPolynomial.X (original, index.2)

def coordinateSub (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Oscillator D →ₐ[ℂ] Oscillator D := MvPolynomial.aeval (coordinate D frame)

def originalDerivative (D : LatticeData) (direction : Fin D.rank → ℂ) (frequency : ℕ) :
    Module.End ℂ (Oscillator D) :=
  ∑ original, direction original • weightedPartial D original frequency

def coordinateDerivative (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (direction : Fin D.rank → ℂ) (frequency : ℕ) : Module.End ℂ (Oscillator D) :=
  ∑ row, gramPair D direction (frame row) • (MvPolynomial.pderiv (row, frequency)).toLinearMap

def directionalPolynomialCurrent (D : LatticeData) (direction : Fin D.rank → ℂ)
    (charge : Charge D) (mode : ℤ) : Module.End ℂ (Oscillator D) :=
  ∑ original, direction original • neutralPolynomialMode D original charge mode

def chargeCoefficient (D : LatticeData) (direction : Fin D.rank → ℂ) (charge : Charge D) : ℂ :=
  ∑ original, direction original * (bilinear D (unitCharge D original) charge : ℂ)

theorem coordinateSub_X (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (index : Index D) : coordinateSub D frame (MvPolynomial.X index) = coordinate D frame index := by
  exact MvPolynomial.aeval_X (coordinate D frame) index

theorem coordinateSub_coordinate (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (index : Index D) :
    coordinateSub D frame (coordinate D inverse index) = coordinate D (inverse * frame) index := by
  classical
  simp only [coordinate, map_sum, map_smul, coordinateSub_X, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem coordinate_identity (D : LatticeData) (index : Index D) :
    coordinate D 1 index = MvPolynomial.X index := by
  classical
  simp [coordinate, Matrix.one_apply]

theorem coordinateSub_inverse (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (inverseIdentity : inverse * frame = 1) (polynomial : Oscillator D) :
    coordinateSub D frame (coordinateSub D inverse polynomial) = polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [coordinateSub]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionHypothesis =>
      simp only [map_mul, coordinateSub_X, inductionHypothesis,
        coordinateSub_coordinate, inverseIdentity, coordinate_identity]

theorem coordinateSub_bijective (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1) :
    Function.Bijective (coordinateSub D frame) := by
  constructor
  · intro first second imagesEqual
    calc
      first = coordinateSub D inverse (coordinateSub D frame first) :=
        (coordinateSub_inverse D inverse frame rightInverse first).symm
      _ = coordinateSub D inverse (coordinateSub D frame second) := by rw [imagesEqual]
      _ = second := coordinateSub_inverse D inverse frame rightInverse second
  · intro polynomial
    exact ⟨coordinateSub D inverse polynomial,
      coordinateSub_inverse D frame inverse leftInverse polynomial⟩

theorem originalDerivative_X (D : LatticeData) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (index : Index D) :
    originalDerivative D direction frequency (MvPolynomial.X index) =
      if frequency = index.2 then
        (∑ original, direction original * (D.G original index.1 : ℂ)) • (1 : Oscillator D)
      else 0 := by
  classical
  rcases index with ⟨axis, indexFrequency⟩
  by_cases sameFrequency : frequency = indexFrequency
  · simp [originalDerivative, weightedPartial, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, sameFrequency, smul_smul, Finset.sum_smul]
  · have reverseDifferent : indexFrequency ≠ frequency := Ne.symm sameFrequency
    simp [originalDerivative, weightedPartial, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, sameFrequency, reverseDifferent]

theorem originalDerivative_coordinate (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (index : Index D) :
    originalDerivative D direction frequency (coordinate D frame index) =
      if frequency = index.2 then gramPair D direction (frame index.1) • (1 : Oscillator D)
      else 0 := by
  classical
  simp only [coordinate, map_sum, map_smul, originalDerivative_X]
  by_cases sameFrequency : frequency = index.2
  · simp only [if_pos sameFrequency, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp only [gramPair, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first firstMember
    apply Finset.sum_congr rfl
    intro second secondMember
    ring
  · simp [sameFrequency]

theorem coordinateDerivative_X (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (index : Index D) :
    coordinateDerivative D frame direction frequency (MvPolynomial.X index) =
      if frequency = index.2 then gramPair D direction (frame index.1) • (1 : Oscillator D)
      else 0 := by
  classical
  rcases index with ⟨axis, indexFrequency⟩
  by_cases sameFrequency : frequency = indexFrequency
  · simp [coordinateDerivative, MvPolynomial.pderiv_X, Pi.single_apply,
      Prod.mk.injEq, sameFrequency]
  · have reverseDifferent : indexFrequency ≠ frequency := Ne.symm sameFrequency
    simp [coordinateDerivative, MvPolynomial.pderiv_X, Pi.single_apply,
      Prod.mk.injEq, sameFrequency, reverseDifferent]

theorem originalDerivative_product (D : LatticeData) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (first second : Oscillator D) :
    originalDerivative D direction frequency (first * second) =
      originalDerivative D direction frequency first * second +
        first * originalDerivative D direction frequency second := by
  classical
  simp [originalDerivative, weightedPartial, MvPolynomial.pderiv_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
  rw [add_comm]
  refine congrArg₂ (fun left right : Oscillator D => left + right) ?_ rfl
  apply Finset.sum_congr rfl
  intro original originalMember
  apply congrArg (fun polynomial : Oscillator D => direction original • polynomial)
  apply Finset.sum_congr rfl
  intro axis axisMember
  exact congrArg (fun polynomial : Oscillator D => (D.G original axis : ℂ) • polynomial)
    (mul_comm _ _)

theorem coordinateDerivative_product (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (first second : Oscillator D) :
    coordinateDerivative D frame direction frequency (first * second) =
      coordinateDerivative D frame direction frequency first * second +
        first * coordinateDerivative D frame direction frequency second := by
  classical
  simp [coordinateDerivative, MvPolynomial.pderiv_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, mul_comm, add_comm]

theorem original_derivative_coordinate_chain_rule (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (frequency : ℕ) (polynomial : Oscillator D) :
    originalDerivative D direction frequency (coordinateSub D frame polynomial) =
      coordinateSub D frame (coordinateDerivative D frame direction frequency polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
      simp [coordinateSub, originalDerivative, weightedPartial, coordinateDerivative,
        MvPolynomial.pderiv_C]
  | add first second firstProof secondProof =>
      simp [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionHypothesis =>
      rw [map_mul, coordinateSub_X, originalDerivative_product,
        inductionHypothesis, originalDerivative_coordinate,
        coordinateDerivative_product, map_add, map_mul, map_mul,
        coordinateSub_X, coordinateDerivative_X]
      by_cases sameFrequency : frequency = index.2 <;>
        simp [sameFrequency, map_smul]

theorem directionalPolynomialCurrent_negative (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (row : Fin D.rank) (charge : Charge D)
    (frequency : ℕ) (polynomial : Oscillator D) :
    directionalPolynomialCurrent D (frame row) charge (-(frequency : ℤ) - 1)
      (coordinateSub D frame polynomial) =
      coordinateSub D frame (MvPolynomial.X (row, frequency) * polynomial) := by
  classical
  simp only [directionalPolynomialCurrent, LinearMap.sum_apply, LinearMap.smul_apply,
    neutralPolynomialMode_negative, LinearMap.mulLeft_apply, map_mul, coordinateSub_X,
    coordinate, Finset.sum_mul, smul_mul_assoc]

theorem directionalPolynomialCurrent_positive (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (charge : Charge D) (frequency : ℕ) (polynomial : Oscillator D) :
    directionalPolynomialCurrent D direction charge ((frequency : ℤ) + 1)
      (coordinateSub D frame polynomial) =
      (frequency + 1 : ℂ) • coordinateSub D frame
        (coordinateDerivative D frame direction frequency polynomial) := by
  classical
  have scalarFactor : directionalPolynomialCurrent D direction charge ((frequency : ℤ) + 1) =
      (frequency + 1 : ℂ) • originalDerivative D direction frequency := by
    simp only [directionalPolynomialCurrent, neutralPolynomialMode_positive,
      originalDerivative, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro original originalMember
    rw [mul_comm (direction original) (frequency + 1 : ℂ)]
  rw [scalarFactor, LinearMap.smul_apply, original_derivative_coordinate_chain_rule]

theorem directionalPolynomialCurrent_zero (D : LatticeData) (direction : Fin D.rank → ℂ)
    (charge : Charge D) (polynomial : Oscillator D) :
    directionalPolynomialCurrent D direction charge 0 polynomial =
      chargeCoefficient D direction charge • polynomial := by
  classical
  simp [directionalPolynomialCurrent, neutralPolynomialMode, chargeCoefficient,
    smul_smul, Finset.sum_smul]

theorem chargeCoefficient_gramPair (D : LatticeData) (direction : Fin D.rank → ℂ)
    (charge : Charge D) :
    chargeCoefficient D direction charge = gramPair D direction (fun index => (charge index : ℂ)) := by
  classical
  simp [chargeCoefficient, gramPair, bilinear, unitCharge, Int.cast_sum,
    Int.cast_mul, Finset.mul_sum, mul_assoc]

theorem directionalCurrent_single (D : LatticeData) (direction : Fin D.rank → ℂ)
    (charge : Charge D) (mode : ℤ) (polynomial : Oscillator D) :
    directionalCurrent D direction mode (Finsupp.single charge polynomial) =
      Finsupp.single charge (directionalPolynomialCurrent D direction charge mode polynomial) := by
  classical
  simp [directionalCurrent, directionalPolynomialCurrent,
    Finsupp.single_finsetSum, Finsupp.smul_single]

theorem original_coordinate_current_bridge (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * frame = 1) (rightInverse : frame * inverse = 1)
    (charge : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ)
    (row : Fin D.rank) (direction : Fin D.rank → ℂ) (frequency : ℕ) :
    Function.Bijective (coordinateSub D frame) ∧
    O D (frame row) (-(frequency : ℤ) - 1)
      (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) =
      Finsupp.single charge (coordinateSub D frame (MvPolynomial.X (row, frequency) * polynomial))
        ⊗ₜ[ℂ] ghost ∧
    O D direction ((frequency : ℤ) + 1)
      (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) =
      (frequency + 1 : ℂ) •
        (Finsupp.single charge (coordinateSub D frame
          (coordinateDerivative D frame direction frequency polynomial)) ⊗ₜ[ℂ] ghost) ∧
    O D direction 0
      (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) =
      gramPair D direction (fun index => (charge index : ℂ)) •
        (Finsupp.single charge (coordinateSub D frame polynomial) ⊗ₜ[ℂ] ghost) := by
  refine ⟨coordinateSub_bijective D frame inverse leftInverse rightInverse, ?_, ?_, ?_⟩
  · simp [O, directionalCurrent_single, directionalPolynomialCurrent_negative]
  · simp [O, directionalCurrent_single, directionalPolynomialCurrent_positive,
      ← Finsupp.smul_single, ← TensorProduct.smul_tmul']
  · simp [O, directionalCurrent_single, directionalPolynomialCurrent_zero,
      chargeCoefficient_gramPair, ← Finsupp.smul_single, ← TensorProduct.smul_tmul']

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
