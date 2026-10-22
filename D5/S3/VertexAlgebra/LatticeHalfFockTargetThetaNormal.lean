/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original labelled normal tuples intertwine target oscillator reflection. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockTargetThetaCoefficients
open LatticeInvolution MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

theorem sigma_current (D : LatticeData) (colour : Fin D.rank) (mode : ℤ)
    (polynomial : Oscillator D) :
    sigma D (LatticeHalfFock.current D colour mode polynomial) =
      -LatticeHalfFock.current D colour mode (sigma D polynomial) := by
  classical
  unfold LatticeHalfFock.current
  split_ifs
  · simp [LinearMap.mulLeft_apply, map_mul]
  · simp only [LinearMap.smul_apply, sigma_smul, LatticeActualAnnihilation.annihilate,
      LatticeSugawaraCurrents.weightedPartial, LinearMap.sum_apply, map_sum]
    change LatticeHalfFock.frequency mode •
        (∑ other : Fin D.rank, (D.G colour other : ℂ) •
          sigma D (pderiv (other, mode.toNat) polynomial)) =
      -(LatticeHalfFock.frequency mode •
        ∑ other : Fin D.rank, (D.G colour other : ℂ) •
          pderiv (other, mode.toNat) (sigma D polynomial))
    simp_rw [sigma_pderiv]
    simp [Finset.sum_neg_distrib, smul_neg]

theorem sigmaTensor_current (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (mode : ℤ) (vector : ActualTensor D hu) :
    sigmaTensor D hu (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      -LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode (sigmaTensor D hu vector) := by
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply, sigmaTensor_tmul, sigma_current,
      TensorProduct.neg_tmul]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, neg_add]

theorem sigmaTensor_jetCurrent (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    sigmaTensor D hu (jetCurrent D hu index mode vector) =
      -jetCurrent D hu index mode (sigmaTensor D hu vector) := by
  simp only [jetCurrent, LinearMap.smul_apply, map_smul, sigmaTensor_current, smul_neg]

theorem sigmaTensor_flatCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (modes : ModeTuple D word)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    sigmaTensor D hu
        (flatCoefficient D hu (chargedField D hu charge) word modes exponent vector) =
      ((-1 : ℂ) ^ word.length) •
        flatCoefficient D hu (chargedField D hu (-charge)) word modes exponent
          (sigmaTensor D hu vector) := by
  induction word generalizing exponent vector with
  | nil =>
    simpa only [flatCoefficient, List.length_nil, pow_zero, one_smul, chargedField,
      HVertexOperator.coeff_of_coeff] using
      sigmaTensor_chargedCoefficient D hu charge exponent vector
  | cons index tail inductionProof =>
    simp only [flatCoefficient, List.length_cons]
    split_ifs
    · simp only [Module.End.mul_apply]
      rw [sigmaTensor_jetCurrent, inductionProof, map_smul]
      simp [pow_succ, mul_neg, neg_smul]
    · simp only [Module.End.mul_apply]
      rw [inductionProof, sigmaTensor_jetCurrent, map_neg]
      simp [pow_succ, mul_neg, neg_smul]

theorem sigmaTensor_normalWord (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    sigmaTensor D hu ((normalWord D hu charge word).coeff exponent vector) =
      ((-1 : ℂ) ^ word.length) •
        (normalWord D hu (-charge) word).coeff exponent (sigmaTensor D hu vector) := by
  rw [normalWord_flattened, normalWord_flattened]
  change (sigmaTensor D hu).toAddMonoidHom
      (∑ᶠ modes : ModeTuple D word,
        flatTerm D hu (chargedField D hu charge) word exponent vector modes) =
    ((-1 : ℂ) ^ word.length) •
      ∑ᶠ modes : ModeTuple D word,
        flatTerm D hu (chargedField D hu (-charge)) word exponent
          (sigmaTensor D hu vector) modes
  rw [(sigmaTensor D hu).toAddMonoidHom.map_finsum
      (flatTerm_finite D hu (chargedField D hu charge) word exponent vector),
    smul_finsum' _ (flatTerm_finite D hu (chargedField D hu (-charge)) word exponent
      (sigmaTensor D hu vector))]
  apply finsum_congr
  intro modes
  exact sigmaTensor_flatCoefficient D hu charge word modes exponent vector

theorem sigmaTensor_normalPolynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    sigmaTensor D hu ((normalPolynomial D hu charge polynomial).coeff exponent vector) =
      (normalPolynomial D hu (-charge) (sigma D polynomial)).coeff exponent
        (sigmaTensor D hu vector) := by
  induction polynomial using MvPolynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, firstProof, secondProof]
  | monomial sourceExponent scalar =>
    have scalarLaw : monomial sourceExponent scalar =
        scalar • (monomial sourceExponent 1 : Oscillator D) := by simp [smul_monomial]
    rw [scalarLaw]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, sigma_smul]
    congr 1
    rw [sigma_monomial]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [normalPolynomial_monomial_enumeration D hu charge sourceExponent _ (List.Perm.refl _),
      normalPolynomial_monomial_enumeration D hu (-charge) sourceExponent _ (List.Perm.refl _)]
    exact sigmaTensor_normalWord D hu charge (LatticeAllStateField.occurrences D sourceExponent)
      exponent vector

#print axioms sigmaTensor_flatCoefficient
#print axioms sigmaTensor_normalPolynomial

end
end D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal
