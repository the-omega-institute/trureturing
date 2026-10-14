/- GID: D5/S3/VertexAlgebra/OriginalChargedGroundField
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalChargedGroundField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite native lattice grounds have a cocycle-normalized original b0 product. -/

import D5.S3.VertexAlgebra.OriginalChargedGround
import D5.S3.VertexAlgebra.OriginalTensorCB0

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalChargedGroundField

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeBcGhostBrstCharge BcGhostFockSupport BcGhostSuperGenerators
open VertexOperatorTensorProduct OriginalChargedGround OriginalCartanOperator
open OriginalCartanCohomology OriginalTensorCB0
open scoped TensorProduct VertexOperator BigOperators

private theorem creationCoeff_one (D : LatticeData) (charge : Charge D) :
    creationCoeff D charge 1 = chargePolynomial D charge := by
  have constant : creationCoeff D charge 0 = 1 := by
    simp [creationCoeff, exponential_constant]
  have vacuumCoeff : rawCoeff D charge 0 (Finsupp.single (0 : Charge D) 1) =
      Finsupp.single charge 1 := by
    rw [LatticeActualOrderedProducts.raw_ground]
    simp [bilinear, epsilon, lowerCocycleExponent, paritySign, constant]
  have equality := LinearMap.congr_fun (rawCoeff_translation D charge 0)
    (Finsupp.single (0 : Charge D) 1)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at equality
  rw [vacuumCoeff, (actual_translation_generators D).2.1, map_zero, sub_zero,
    (actual_translation_generators D).1, LatticeActualOrderedProducts.raw_ground] at equality
  have coordinate := congrArg (fun state : Carrier D => state charge) equality
  simpa [bilinear, epsilon, lowerCocycleExponent, paritySign,
    Derivation.map_one_eq_zero, Finsupp.smul_apply] using coordinate.symm

theorem opposite_ground_coefficient (D : LatticeData) (charge : Charge D)
    (normTwo : bilinear D charge charge = 2) :
    ((actualField D charge)[[0]]) (Finsupp.single (-charge) (1 : Oscillator D)) =
      epsilon D charge (-charge) • Finsupp.single 0 (chargePolynomial D charge) := by
  have pairing : bilinear D charge (-charge) = -2 := by
    rw [LatticeFiniteNegativeGeneration.bilinear_neg_right, normTwo]
  rw [actualField, VertexOperator.ncoeff_of_coeff, LatticeActualOrderedProducts.raw_ground,
    pairing]
  norm_num [creationCoeff_one]

#print axioms opposite_ground_coefficient

theorem opposite_ground_B0_product (D : LatticeData) (charge : Charge D)
    (normTwo : bilinear D charge charge = 2) :
    B D 0 (((LatticeBcGhostTensorStateField.stateField D (ground D charge))[[-1]])
      (ground D (-charge))) =
      epsilon D charge (-charge) •
        (Finsupp.single 0 (chargePolynomial D charge) ⊗ₜ[ℂ] Finsupp.single {1} 1) := by
  have contraction := tensor_c_B0 D (actualField D charge) (-1)
    (Finsupp.single (-charge) (1 : Oscillator D)) (Finsupp.single {1} 1)
  change B D 0 (((field (actualField D charge) (currentField .c))[[-1]])
      (ground D (-charge))) +
    ((field (actualField D charge) (currentField .c))[[-1]])
      (B D 0 (ground D (-charge))) = _ at contraction
  rw [ground_B0, map_zero, add_zero] at contraction
  rw [ground_field]
  exact contraction.trans (by
    change ((actualField D charge)[[0]])
      (Finsupp.single (-charge) (1 : Oscillator D)) ⊗ₜ[ℂ] Finsupp.single {1} 1 = _
    rw [opposite_ground_coefficient D charge normTwo]
    rfl)

#print axioms opposite_ground_B0_product

private theorem opposite_cocycle (D : LatticeData) (charge : Charge D)
    (normTwo : bilinear D charge charge = 2) : epsilon D charge (-charge) = -1 := by
  have exponent : lowerCocycleExponent D charge (-charge) =
      -lowerCocycleExponent D charge charge := by
    rw [LatticeTwistedGroundRealization.SignQuotient.lower_matrix_formula,
      LatticeTwistedGroundRealization.SignQuotient.lower_matrix_formula]
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [epsilon, exponent,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, normTwo]
  norm_num [paritySign]

private theorem chargePolynomial_cartan (D : LatticeData) (charge : Charge D) :
    Finsupp.single 0 (chargePolynomial D charge) ⊗ₜ[ℂ] Finsupp.single {1} 1 =
      -cartanState D (complexCharge D charge) := by
  classical
  rw [cartanState_apply, neg_neg]
  change (Finsupp.single (0 : Charge D)
      (∑ axis : Fin D.rank, (charge axis : ℂ) • MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
      Finsupp.single {1} 1) =
    ∑ axis : Fin D.rank, (charge axis : ℂ) •
      (Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
        Finsupp.single {1} 1)
  rw [Finsupp.single_finsetSum, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro axis _
  rw [← Finsupp.smul_single]
  rfl

theorem opposite_ground_signed_B0 (D : LatticeData) (charge : Charge D)
    (normTwo : bilinear D charge charge = 2) :
    -B D 0 (((LatticeBcGhostTensorStateField.stateField D (ground D charge))[[-1]])
      (ground D (-charge))) = -cartanState D (complexCharge D charge) := by
  rw [opposite_ground_B0_product D charge normTwo, opposite_cocycle D charge normTwo,
    neg_one_smul, neg_neg, chargePolynomial_cartan]

#print axioms opposite_ground_signed_B0

end D5.S3.VertexAlgebra.OriginalChargedGroundField
