import D5.S3.VertexAlgebra.OriginalCartanOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalCartanCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open LatticeBcGhostBrstCharge BcGhostFockSupport
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open OriginalBrstReassembly
open OriginalCartanOperator
open TensorConformal.OriginalTopologicalApplications
open TensorConformal.OriginalIntegralBVGerstBracketTransient
open LatticeBcGhostCohomologyModes
open scoped TensorProduct VertexOperator BigOperators

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

def complexCharge (charge : Charge D) : Fin D.rank → ℂ := fun axis => (charge axis : ℂ)

def gramPair (left right : Fin D.rank → ℂ) : ℂ :=
  ∑ axis, ∑ other, left axis * (D.G axis other : ℂ) * right other

theorem gramPair_charge (coefficients : Fin D.rank → ℂ) (charge : Charge D) :
    gramPair D coefficients (complexCharge D charge) =
      ∑ axis, coefficients axis * (bilinear D (unitCharge D axis) charge : ℂ) := by
  simp [gramPair, complexCharge, bilinear, unitCharge, Finset.mul_sum, mul_assoc]

theorem momentum_fullBasis (coefficients : Fin D.rank → ℂ) (label : FullLabel D) :
    momentum D coefficients (fullBasis D label) =
      gramPair D coefficients (complexCharge D label.1.1) • fullBasis D label := by
  rw [gramPair_charge, momentum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, fullBasis_apply,
    LatticePositiveEnergy.carrierBasis_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, neutralMode_single]
  simp only [neutralPolynomialMode, lt_self_iff_false, if_false, if_pos rfl,
    LinearMap.smul_apply, LinearMap.id_apply, ← Finsupp.smul_single,
    TensorProduct.smul_tmul, smul_smul]
  simp [← Finsupp.smul_single, TensorProduct.smul_tmul, smul_smul, ← Finset.sum_smul]

theorem momentum_charge (coefficients : Fin D.rank → ℂ) (charge : Charge D)
    (state : State D) (member : state ∈ part D (chargeTag D) charge) :
    momentum D coefficients state = gramPair D coefficients (complexCharge D charge) • state := by
  have operators :
      (momentum D coefficients).comp (projection D (chargeTag D) charge) =
        gramPair D coefficients (complexCharge D charge) • projection D (chargeTag D) charge := by
    apply (fullBasis D).ext
    intro label
    by_cases same : chargeTag D label = charge
    · rw [LinearMap.comp_apply,
        projection_fixed D (chargeTag D) charge (same ▸ basis_mem_part D (chargeTag D) label),
        LinearMap.smul_apply,
        projection_fixed D (chargeTag D) charge (same ▸ basis_mem_part D (chargeTag D) label),
        momentum_fullBasis]
      exact congrArg (fun scalar : ℂ => scalar • fullBasis D label)
        (congrArg (fun source => gramPair D coefficients (complexCharge D source)) same)
    · simp only [LinearMap.comp_apply, LinearMap.smul_apply,
        projection_other D (chargeTag D) charge (chargeTag D label) same
          (basis_mem_part D (chargeTag D) label), map_zero, smul_zero]
  have equality := LinearMap.congr_fun operators state
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply,
    projection_fixed D (chargeTag D) charge member] using equality

theorem currentState_sector (axis : Fin D.rank) :
    currentState D axis =
      (OriginalZeroChargeEnergyBasis.sectorBasis D (.inr (axis, false)) : State D) := by
  rw [OriginalZeroChargeEnergyBasis.sectorBasis_coe,
    OriginalZeroChargeEnergyBasis.fullBasis_apply]
  rfl

include leftInverse rightInverse in
theorem cartanState_zero (coefficients : Fin D.rank → ℂ) :
    cartanState D coefficients ∈ zeroSpace D H := by
  have each (axis : Fin D.rank) : currentState D axis ∈ zeroSpace D H := by
    rw [currentState_sector]
    exact ((OriginalZeroChargeEnergyBasis.mem_sector_iff D H leftInverse rightInverse _).mp
      (OriginalZeroChargeEnergyBasis.sectorBasis D (.inr (axis, false))).property).2
  rw [cartanState_apply]
  exact (zeroSpace D H).neg_mem ((zeroSpace D H).sum_mem fun axis _ =>
    (zeroSpace D H).smul_mem _ (each axis))

theorem cartanState_J (coefficients : Fin D.rank → ℂ) :
    LatticeBcGhostBrstGhostNumber.J D (cartanState D coefficients) =
      cartanState D coefficients := by
  have each (axis : Fin D.rank) : LatticeBcGhostBrstGhostNumber.J D (currentState D axis) =
      currentState D axis := by
    rw [currentState_sector]
    simpa [OriginalZeroChargeEnergyBasis.indexDegree] using
      OriginalZeroChargeEnergyBasis.J_sectorBasis D (.inr (axis, false))
  simp only [cartanState_apply, map_neg, map_sum, map_smul, each]

def cartanZeroCycle (coefficients : Fin D.rank → ℂ) : cycles D H (zeroSpace D H) :=
  ⟨cartanState D coefficients, cartanState_zero D H leftInverse rightInverse coefficients,
    cartanState_Q D H leftInverse rightInverse coefficients⟩

def cartanClass : (Fin D.rank → ℂ) →ₗ[ℂ] OriginalCohomology D H :=
  (OriginalBoundaries D H).mkQ.comp
    ((cartanState D).codRestrict (OriginalCycles D H)
      (cartanState_Q D H leftInverse rightInverse))

theorem cartanClass_zeroCycle (coefficients : Fin D.rank → ℂ) :
    cartanClass D H leftInverse rightInverse coefficients =
      originalClass D H (cartanZeroCycle D H leftInverse rightInverse coefficients) := rfl

theorem cartanClass_parity (coefficients : Fin D.rank → ℂ) :
    parity D H 1 (cartanClass D H leftInverse rightInverse coefficients) =
      cartanClass D H leftInverse rightInverse coefficients := by
  rw [cartanClass_zeroCycle]
  change parity D H 1 ((OriginalBoundaries D H).mkQ _) = _
  rw [parity_mk]
  congr 1
  apply Subtype.ext
  have each (axis : Fin D.rank) :
      LatticeBcGhostTensorStateField.parityPart 1 (currentState D axis) = currentState D axis := by
    simp only [currentState, LatticeBcGhostTensorStateField.parityPart_tmul]
    rw [BcGhostSuperGenerators.parityPart_identity]
    exact BcGhostSuperGenerators.single_mem 1 {1} 1 (by norm_num [BcGhostSuperGenerators.subsetParity])
  change LatticeBcGhostTensorStateField.parityPart 1 (cartanState D coefficients) =
    cartanState D coefficients
  simp only [cartanState_apply, map_neg, map_sum, map_smul, each]

theorem cartanClass_J (coefficients : Fin D.rank → ℂ) :
    literalCohomologyJ D H (cartanClass D H leftInverse rightInverse coefficients) =
      cartanClass D H leftInverse rightInverse coefficients := by
  change (OriginalBoundaries D H).mkQ _ = (OriginalBoundaries D H).mkQ _
  congr 1
  apply Subtype.ext
  exact cartanState_J D coefficients

theorem cartan_defect_state (coefficients : Fin D.rank → ℂ)
    (right : cycles D H (zeroSpace D H)) :
    ((-zeroCycleDefect D H leftInverse rightInverse 1
      (cartanZeroCycle D H leftInverse rightInverse coefficients) right :
      cycles D H (zeroSpace D H)) : State D) = momentum D coefficients right.val := by
  change -(B D 0 (LatticeBcGhostTensorJacobi.mu D (cartanState D coefficients) (-1) right.val) -
      LatticeBcGhostTensorJacobi.mu D (B D 0 (cartanState D coefficients)) (-1) right.val -
      SuperFieldProducts.koszul 1 1 • LatticeBcGhostTensorJacobi.mu D
        (cartanState D coefficients) (-1) (B D 0 right.val)) = _
  rw [cartanState_B0]
  simp only [LatticeBcGhostTensorJacobi.mu, map_zero, Pi.zero_apply, LinearMap.zero_apply,
    sub_zero, SuperFieldProducts.koszul, mul_one, pow_one, neg_one_smul, sub_neg_eq_add]
  rw [cartanState_B0_minusOne, neg_neg]

theorem mixedBracket_cartan_zeroClass (coefficients : Fin D.rank → ℂ)
    (charge : Charge D) (right : cycles D H (zeroSpace D H))
    (charged : right.val ∈ part D (chargeTag D) charge) :
    mixedBracket D H leftInverse rightInverse critical
      (cartanClass D H leftInverse rightInverse coefficients) (originalClass D H right) =
      gramPair D coefficients (complexCharge D charge) • originalClass D H right := by
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical 1 0 _ _
    (cartanClass_parity D H leftInverse rightInverse coefficients), pow_one, neg_one_smul,
    cartanClass_zeroCycle, quotientDefectValue,
    quotientDefect_class D H leftInverse rightInverse critical]
  change -(OriginalBoundaries D H).mkQ _ = _ • (OriginalBoundaries D H).mkQ _
  rw [← map_neg, ← map_smul]
  congr 1
  apply Subtype.ext
  exact (cartan_defect_state D H leftInverse rightInverse coefficients right).trans
    (momentum_charge D coefficients charge right.val charged)

def chargeZeroCycle (charge : Charge D) :
    cycles D H (zeroSpace D H) →ₗ[ℂ] cycles D H (zeroSpace D H) :=
  cyclesMap D H (zeroSpace D H) (zeroSpace D H)
    (projection D (chargeTag D) charge)
    (zero_projected D H leftInverse rightInverse (chargeTag D) charge)
    (chargeProjection_Q D H charge)

def chargeClassProjection (charge : Charge D) : Module.End ℂ (OriginalCohomology D H) :=
  (originalZeroEquiv D H leftInverse rightInverse critical).symm.toLinearMap.comp
    ((homologyMap D H leftInverse rightInverse critical (zeroSpace D H) (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse) (zero_stable D H leftInverse rightInverse)
      (projection D (chargeTag D) charge)
      (zero_projected D H leftInverse rightInverse (chargeTag D) charge)
      (chargeProjection_Q D H charge)).comp
        (originalZeroEquiv D H leftInverse rightInverse critical).toLinearMap)

theorem chargeClassProjection_zeroClass (charge : Charge D)
    (right : cycles D H (zeroSpace D H)) :
    chargeClassProjection D H leftInverse rightInverse critical charge (originalClass D H right) =
      originalClass D H (chargeZeroCycle D H leftInverse rightInverse charge right) := by
  unfold originalClass
  rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical right]
  simp only [chargeClassProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, homologyMap_mk]
  exact originalZeroEquiv_symm_mk D H leftInverse rightInverse critical _

include leftInverse rightInverse critical in
theorem original_zero_representative (state : OriginalCohomology D H) :
    ∃ representative : cycles D H (zeroSpace D H), originalClass D H representative = state := by
  obtain ⟨representative, equality⟩ :=
    (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse)).mkQ_surjective
        (originalZeroEquiv D H leftInverse rightInverse critical state)
  refine ⟨representative, ?_⟩
  unfold originalClass
  rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical representative,
    equality, LinearEquiv.symm_apply_apply]

theorem charged_zero_representative (charge : Charge D) (state : OriginalCohomology D H)
    (fixed : chargeClassProjection D H leftInverse rightInverse critical charge state = state) :
    ∃ representative : cycles D H (zeroSpace D H),
      representative.val ∈ part D (chargeTag D) charge ∧
        originalClass D H representative = state := by
  obtain ⟨representative, equality⟩ :=
    original_zero_representative D H leftInverse rightInverse critical state
  refine ⟨chargeZeroCycle D H leftInverse rightInverse charge representative,
    projection_mem D (chargeTag D) charge representative.val, ?_⟩
  rw [← chargeClassProjection_zeroClass D H leftInverse rightInverse critical,
    equality, fixed]

theorem mixedBracket_cartan_charge (coefficients : Fin D.rank → ℂ)
    (charge : Charge D) (state : OriginalCohomology D H)
    (fixed : chargeClassProjection D H leftInverse rightInverse critical charge state = state) :
    mixedBracket D H leftInverse rightInverse critical
      (cartanClass D H leftInverse rightInverse coefficients) state =
      gramPair D coefficients (complexCharge D charge) • state := by
  obtain ⟨representative, charged, equality⟩ :=
    charged_zero_representative D H leftInverse rightInverse critical charge state fixed
  rw [← equality]
  exact mixedBracket_cartan_zeroClass D H leftInverse rightInverse critical coefficients
    charge representative charged

#print axioms mixedBracket_cartan_zeroClass
#print axioms mixedBracket_cartan_charge

end D5.S3.VertexAlgebra.OriginalCartanCohomology
