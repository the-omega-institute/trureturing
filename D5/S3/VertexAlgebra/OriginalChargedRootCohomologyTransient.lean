import D5.S3.VertexAlgebra.OriginalChargedGroundField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalChargedRootCohomologyTransient

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraVirasoro LatticeFiniteNegativeGeneration LatticeBcGhostBrstCharge
open BcGhostFockSupport OriginalBrstReassembly OriginalChargedGround
open OriginalChargedGroundField OriginalCartanOperator OriginalCartanCohomology
open OriginalCartanFaithfulness
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open TensorConformal.OriginalTopologicalApplications
open TensorConformal.OriginalIntegralB0CompatibilityTransient
open TensorConformal.OriginalIntegralBVGerstBracketTransient LatticeBcGhostCohomologyModes
open scoped TensorProduct VertexOperator BigOperators

theorem ground_J (D : LatticeData) (charge : Charge D) :
    nativeJ D (ground D charge) = ground D charge := by
  have eigenvector := J_basis D ((charge, 0), {1})
  have degree : BcGhostNumber.degree ({1} : Finset ℕ) = 1 := by decide
  simpa only [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply,
    MvPolynomial.monomial_zero', map_one, degree, Int.cast_one, one_smul,
    ground, nativeJ] using eigenvector

#print axioms ground_J

theorem ground_basis (D : LatticeData) (charge : Charge D) :
    fullBasis D ((charge, 0), {1}) = ground D charge := by
  rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
  simp only [MvPolynomial.monomial_zero', map_one]
  all_goals rfl

theorem ground_charge (D : LatticeData) (charge : Charge D) :
    ground D charge ∈ part D (chargeTag D) charge := by
  rw [← ground_basis D charge]
  exact basis_mem_part D (chargeTag D) ((charge, 0), {1})

#print axioms ground_charge

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)

include leftInverse rightInverse in
theorem ground_zero (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    ground D charge ∈ zeroSpace D H := by
  have ward := LinearMap.congr_fun (ward_identity D H 0) (ground D charge)
  change Q D H (B D 0 (ground D charge)) + B D 0 (Q D H (ground D charge)) =
    (M D H 0 + G D 0) (ground D charge) at ward
  change (M D H 0 + G D 0) (ground D charge) = 0
  simpa only [ground_B0, ground_Q D H leftInverse rightInverse charge normTwo,
    map_zero, zero_add] using ward.symm

#print axioms ground_zero

def rootGhostCycle (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    ghostCycles D H (zeroSpace D H) 1 :=
  ⟨ground D charge,
    ⟨ground_zero D H leftInverse rightInverse charge normTwo,
      ground_Q D H leftInverse rightInverse charge normTwo⟩,
    (ghostPart_iff_number D 1 (ground D charge)).mpr
      (by simpa only [Int.cast_one, one_smul] using ground_J D charge)⟩

def rootZeroCycle (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    cycles D H (zeroSpace D H) :=
  ghostCycleInclude D H (zeroSpace D H) 1
    (rootGhostCycle D H leftInverse rightInverse charge normTwo)

def rootClass (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    OriginalCohomology D H :=
  originalClass D H (rootZeroCycle D H leftInverse rightInverse charge normTwo)

theorem rootClass_J (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    literalCohomologyJ D H (rootClass D H leftInverse rightInverse charge normTwo) =
      rootClass D H leftInverse rightInverse charge normTwo := by
  change (OriginalBoundaries D H).mkQ _ = (OriginalBoundaries D H).mkQ _
  apply congrArg (OriginalBoundaries D H).mkQ
  apply Subtype.ext
  exact ground_J D charge

#print axioms rootClass_J

theorem rootClass_parity (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    parity D H 1 (rootClass D H leftInverse rightInverse charge normTwo) =
      rootClass D H leftInverse rightInverse charge normTwo := by
  change (OriginalBoundaries D H).mkQ _ = (OriginalBoundaries D H).mkQ _
  apply congrArg (OriginalBoundaries D H).mkQ
  apply Subtype.ext
  change LatticeBcGhostTensorStateField.parityPart 1 (ground D charge) = ground D charge
  exact ghostPart_original_parity D 1 (ground D charge)
    (rootGhostCycle D H leftInverse rightInverse charge normTwo).property.2

theorem normTwo_neg (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    bilinear D (-charge) (-charge) = 2 := by
  rw [bilinear_neg_left, bilinear_neg_right, neg_neg, normTwo]

theorem opposite_root_bracket (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    mixedBracket D H leftInverse rightInverse critical
      (rootClass D H leftInverse rightInverse charge normTwo)
      (rootClass D H leftInverse rightInverse (-charge) (normTwo_neg D charge normTwo)) =
      -cartanClass D H leftInverse rightInverse (complexCharge D charge) := by
  rw [mixedBracket_homogeneous D H leftInverse rightInverse critical 1 0 _ _
    (rootClass_parity D H leftInverse rightInverse charge normTwo),
    pow_one, neg_one_smul, quotientDefectValue]
  simp only [rootClass]
  rw [quotientDefect_class, cartanClass_zeroCycle]
  change -(OriginalBoundaries D H).mkQ _ = -(OriginalBoundaries D H).mkQ _
  apply congrArg (fun value : OriginalCohomology D H => -value)
  apply congrArg (OriginalBoundaries D H).mkQ
  apply Subtype.ext
  change (B D 0 (((LatticeBcGhostTensorStateField.stateField D (ground D charge))[[-1]])
      (ground D (-charge))) -
    ((LatticeBcGhostTensorStateField.stateField D (B D 0 (ground D charge)))[[-1]])
      (ground D (-charge)) -
    SuperFieldProducts.koszul 1 1 •
      ((LatticeBcGhostTensorStateField.stateField D (ground D charge))[[-1]])
        (B D 0 (ground D (-charge)))) = cartanState D (complexCharge D charge)
  simp only [ground_B0, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero, sub_zero]
  exact neg_injective (opposite_ground_signed_B0 D charge normTwo)

#print axioms opposite_root_bracket

private theorem gramPair_complex_charges (charge source : Charge D) :
    gramPair D (complexCharge D charge) (complexCharge D source) =
      (bilinear D charge source : ℂ) := by
  classical
  simp [gramPair, complexCharge, bilinear, Int.cast_sum, Int.cast_mul,
    mul_comm, mul_left_comm, mul_assoc]

theorem cartan_root_nonzero (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    cartanClass D H leftInverse rightInverse (complexCharge D charge) ≠ 0 := by
  intro zeroClass
  have zeroCharge := cartanClass_faithful D H leftInverse rightInverse
    (complexCharge D charge) zeroClass
  have pairing := gramPair_complex_charges D charge charge
  rw [zeroCharge] at pairing
  norm_num [gramPair, normTwo] at pairing

theorem rootClass_ne_zero (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    rootClass D H leftInverse rightInverse charge normTwo ≠ 0 := by
  intro zeroClass
  have opposite := opposite_root_bracket D H leftInverse rightInverse critical charge normTwo
  simp only [zeroClass, map_zero, LinearMap.zero_apply] at opposite
  exact cartan_root_nonzero D H leftInverse rightInverse charge normTwo
    (neg_eq_zero.mp opposite.symm)

theorem cartan_root_action (critical : D.rank = 26) (coefficients : Fin D.rank → ℂ)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    mixedBracket D H leftInverse rightInverse critical
      (cartanClass D H leftInverse rightInverse coefficients)
      (rootClass D H leftInverse rightInverse charge normTwo) =
      gramPair D coefficients (complexCharge D charge) •
        rootClass D H leftInverse rightInverse charge normTwo := by
  exact mixedBracket_cartan_zeroClass D H leftInverse rightInverse critical coefficients charge
    (rootZeroCycle D H leftInverse rightInverse charge normTwo) (ground_charge D charge)

theorem normalized_sl2_relations (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    let positive := rootClass D H leftInverse rightInverse charge normTwo
    let negative := -rootClass D H leftInverse rightInverse (-charge) (normTwo_neg D charge normTwo)
    let cartan := cartanClass D H leftInverse rightInverse (complexCharge D charge)
    positive ≠ 0 ∧ negative ≠ 0 ∧ cartan ≠ 0 ∧
      mixedBracket D H leftInverse rightInverse critical positive negative = cartan ∧
      mixedBracket D H leftInverse rightInverse critical cartan positive = (2 : ℂ) • positive ∧
      mixedBracket D H leftInverse rightInverse critical cartan negative = (-2 : ℂ) • negative := by
  dsimp only
  refine ⟨rootClass_ne_zero D H leftInverse rightInverse critical charge normTwo,
    neg_ne_zero.mpr (rootClass_ne_zero D H leftInverse rightInverse critical (-charge)
      (normTwo_neg D charge normTwo)),
    cartan_root_nonzero D H leftInverse rightInverse charge normTwo, ?_, ?_, ?_⟩
  · rw [map_neg, opposite_root_bracket, neg_neg]
  · have action := cartan_root_action D H leftInverse rightInverse critical
      (complexCharge D charge) charge normTwo
    simpa [gramPair_complex_charges, normTwo] using action
  · have action := cartan_root_action D H leftInverse rightInverse critical
      (complexCharge D charge) (-charge) (normTwo_neg D charge normTwo)
    have normalized : mixedBracket D H leftInverse rightInverse critical
        (cartanClass D H leftInverse rightInverse (complexCharge D charge))
        (rootClass D H leftInverse rightInverse (-charge) (normTwo_neg D charge normTwo)) =
        (-2 : ℂ) • rootClass D H leftInverse rightInverse (-charge)
          (normTwo_neg D charge normTwo) := by
      simpa [gramPair_complex_charges, bilinear_neg_right, normTwo] using action
    calc
      _ = -(mixedBracket D H leftInverse rightInverse critical
          (cartanClass D H leftInverse rightInverse (complexCharge D charge))
          (rootClass D H leftInverse rightInverse (-charge) (normTwo_neg D charge normTwo))) :=
        map_neg _ _
      _ = -((-2 : ℂ) • rootClass D H leftInverse rightInverse (-charge)
          (normTwo_neg D charge normTwo)) :=
        congrArg (fun value : OriginalCohomology D H => -value) normalized
      _ = _ := (smul_neg (-2 : ℂ)
        (rootClass D H leftInverse rightInverse (-charge) (normTwo_neg D charge normTwo))).symm

#print axioms rootClass_ne_zero
#print axioms normalized_sl2_relations

def rootGhostClass (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    ghostCohomology D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse) 1 :=
  (ghostBoundaries D H leftInverse rightInverse critical (zeroSpace D H)
    (zero_stable D H leftInverse rightInverse) 1).mkQ
      (rootGhostCycle D H leftInverse rightInverse charge normTwo)

theorem rootGhostClass_original (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    (originalZeroEquiv D H leftInverse rightInverse critical).symm
      (ghostClassInclude D H leftInverse rightInverse critical (zeroSpace D H)
        (zero_stable D H leftInverse rightInverse) 1
        (rootGhostClass D H leftInverse rightInverse critical charge normTwo)) =
      rootClass D H leftInverse rightInverse charge normTwo := by
  change (originalZeroEquiv D H leftInverse rightInverse critical).symm
      ((boundaries D H leftInverse rightInverse critical (zeroSpace D H)
        (zero_stable D H leftInverse rightInverse)).mkQ
          (rootZeroCycle D H leftInverse rightInverse charge normTwo)) = _
  exact originalZeroEquiv_symm_mk D H leftInverse rightInverse critical
    (rootZeroCycle D H leftInverse rightInverse charge normTwo)

theorem rootGhostClass_ne_zero (critical : D.rank = 26)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    rootGhostClass D H leftInverse rightInverse critical charge normTwo ≠ 0 := by
  intro zeroClass
  have equation := rootGhostClass_original D H leftInverse rightInverse critical charge normTwo
  simp only [zeroClass, map_zero] at equation
  exact rootClass_ne_zero D H leftInverse rightInverse critical charge normTwo equation.symm

#print axioms rootGhostClass_ne_zero

end D5.S3.VertexAlgebra.OriginalChargedRootCohomologyTransient
