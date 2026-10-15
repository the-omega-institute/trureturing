/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeSymmetricForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeSymmetricForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original chosen Leech ground is symmetrically complex-bilinear self-dual. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeOrbit
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open GolayLeech.ExplicitLeechLattice
open LeechQuadratic NativeHyperbolicActions NativeOrbit OperatorAlgebra
open scoped BigOperators

noncomputable section

attribute [local irreducible] intertwiner nativeBasis hyperbolicBasis actionScalar

def coordinateDot : LinearMap.BilinForm ℂ (Ground 12) :=
  Matrix.toBilin' (1 : Matrix (Half 12) (Half 12) ℂ)

theorem coordinate_dot_apply (first second : Ground 12) :
    coordinateDot first second = ∑ half : Half 12, first half * second half := by
  classical
  simp [coordinateDot, Matrix.toBilin'_apply, Matrix.one_apply]

theorem coordinate_dot_symm : coordinateDot.IsSymm := by
  constructor
  intro first second
  simp only [coordinate_dot_apply, mul_comm]

theorem coordinate_dot_nondegenerate : coordinateDot.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  simp

theorem weyl_dot_invariant (coordinates : Coordinates 12) (first second : Ground 12) :
    coordinateDot (weylOperator coordinates first) (weylOperator coordinates second) =
      coordinateDot first second := by
  classical
  simp only [coordinate_dot_apply, weylOperator, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ half : Half 12, complexSign (dot (rightHalf coordinates) half) *
      first (half + leftHalf coordinates) *
      (complexSign (dot (rightHalf coordinates) half) * second (half + leftHalf coordinates))) =
        ∑ half : Half 12, first (half + leftHalf coordinates) * second (half + leftHalf coordinates) := by
          apply Finset.sum_congr rfl
          intro half _
          have square := sign_square (dot (rightHalf coordinates) half)
          linear_combination first (half + leftHalf coordinates) *
            second (half + leftHalf coordinates) * square
    _ = _ := Fintype.sum_equiv (Equiv.addRight (leftHalf coordinates))
      (fun half => first (half + leftHalf coordinates) * second (half + leftHalf coordinates))
      (fun half => first half * second half) (fun _ => rfl)

def nativePairing : LinearMap.BilinForm ℂ NativeGround :=
  coordinateDot.compl₁₂ intertwiner.symm.toLinearMap intertwiner.symm.toLinearMap

theorem native_pairing_apply (first second : NativeGround) :
    nativePairing first second = coordinateDot (intertwiner.symm first) (intertwiner.symm second) := rfl

theorem native_pairing_symm : nativePairing.IsSymm := by
  constructor
  intro first second
  exact coordinate_dot_symm.eq _ _

theorem native_pairing_nondegenerate : nativePairing.Nondegenerate := by
  constructor
  · intro state vanishing
    apply intertwiner.symm.injective
    have annihilates : ∀ other : Ground 12, coordinateDot (intertwiner.symm state) other = 0 := by
      intro other
      simpa only [native_pairing_apply, LinearEquiv.symm_apply_apply] using
        vanishing (intertwiner other)
    simpa using coordinate_dot_nondegenerate.1 _ annihilates
  · intro state vanishing
    apply intertwiner.symm.injective
    have annihilates : ∀ other : Ground 12, coordinateDot other (intertwiner.symm state) = 0 := by
      intro other
      simpa only [native_pairing_apply, LinearEquiv.symm_apply_apply] using
        vanishing (intertwiner other)
    simpa using coordinate_dot_nondegenerate.2 _ annihilates

theorem basis_pairing (first second : Half 12) :
    nativePairing (nativeBasis first) (nativeBasis second) = if first = second then 1 else 0 := by
  classical
  rw [native_pairing_apply]
  unfold intertwiner
  change coordinateDot (nativeBasis.equivFun (nativeBasis first))
    (nativeBasis.equivFun (nativeBasis second)) = _
  simp [coordinate_dot_apply, Module.Basis.equivFun_self, Finsupp.single_apply,
    mul_ite, ite_mul]

theorem native_pairing_nonzero : nativePairing ≠ 0 := by
  intro zero
  have contradiction := basis_pairing 0 0
  rw [zero] at contradiction
  norm_num at contradiction

theorem native_pairing_invariant (element : Extension data ⧸ K data)
    (first second : NativeGround) :
    nativePairing (nativeRho element first) (nativeRho element second) = nativePairing first second := by
  let reduced := quotientEquiv data element
  have transport (state : NativeGround) : intertwiner.symm (nativeRho element state) =
      actionScalar data hyperbolicBasis reduced •
        weylOperator (hyperbolicBasis.equivFun reduced.charge) (intertwiner.symm state) := by
    have equation := quotient_intertwiner element (intertwiner.symm state)
    rw [LinearEquiv.apply_symm_apply] at equation
    apply intertwiner.injective
    rw [LinearEquiv.apply_symm_apply]
    exact equation
  simp only [native_pairing_apply, transport, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [← mul_assoc, scalar_square, one_mul, weyl_dot_invariant]

def comparison (form : LinearMap.BilinForm ℂ NativeGround) : Module.End ℂ NativeGround where
  toFun state := ∑ half : Half 12, form state (nativeBasis half) • nativeBasis half
  map_add' first second := by
    simp [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar state := by
    simp [map_smul, LinearMap.smul_apply, smul_smul, Finset.smul_sum]

theorem comparison_pairing (form : LinearMap.BilinForm ℂ NativeGround)
    (first second : NativeGround) :
    nativePairing (comparison form first) second = form first second := by
  have maps : nativePairing (comparison form first) = form first := by
    apply nativeBasis.ext
    intro half
    simp [comparison, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      basis_pairing, smul_eq_mul, mul_ite]
  exact congrArg (fun functional : NativeGround →ₗ[ℂ] ℂ => functional second) maps

theorem invariant_form_unique (form : LinearMap.BilinForm ℂ NativeGround)
    (invariant : ∀ element : Extension data ⧸ K data, ∀ first second,
      form (nativeRho element first) (nativeRho element second) = form first second) :
    ∃ scalar : ℂ, form = scalar • nativePairing := by
  have commutes (element : Extension data ⧸ K data) :
      comparison form * nativeRho element = nativeRho element * comparison form := by
    apply LinearMap.ext
    intro state
    apply sub_eq_zero.mp
    apply native_pairing_nondegenerate.1
    intro other
    rw [map_sub, LinearMap.sub_apply]
    apply sub_eq_zero.mpr
    let inverseOther := nativeRho element⁻¹ other
    have undo : nativeRho element inverseOther = other := by
      change (nativeRho element * nativeRho element⁻¹) other = other
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    change nativePairing (comparison form (nativeRho element state)) other =
      nativePairing (nativeRho element (comparison form state)) other
    rw [comparison_pairing, ← undo, invariant, native_pairing_invariant, comparison_pairing]
  obtain ⟨scalar, equality⟩ :=
    ((nativeOperatorAlgebra data determinantUnit).scalar_commutant (comparison form)).mp
      (fun charge => commutes (chargeLift data charge))
  refine ⟨scalar, ?_⟩
  apply LinearMap.ext
  intro first
  apply LinearMap.ext
  intro second
  rw [← comparison_pairing, equality]
  change nativePairing (scalar • first) second = scalar * nativePairing first second
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem original_integral_sign (charge : Charge data) :
    complexSign (quadratic data (reduceCharge data charge)) =
      paritySign (bilinear data charge charge / 2) := by
  rw [quadratic_integral, complexSign_integral]

theorem original_integral_square (charge : Charge data) :
    groundAction data determinantUnit charge ^ 2 =
      complexSign (quadratic data (reduceCharge data charge)) • (1 : Module.End ℂ NativeGround) := by
  rw [original_integral_sign]
  exact (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation data determinantUnit))).2.2.2.2.2.1 charge

theorem original_epsilon_inverse (charge : Charge data) :
    epsilon data charge (-charge) =
      complexSign (quadratic data (reduceCharge data charge)) := by
  unfold epsilon
  rw [← complexSign_integral]
  change complexSign (integralCocycle data charge (-charge)) = _
  rw [← cocycle_reduction, map_neg]
  have negation : -(reduceCharge data charge) = reduceCharge data charge := by
    ext index
    exact CharTwo.neg_eq _
  rw [negation, quadratic_diagonal]

theorem original_integral_adjoint (charge : Charge data) (first second : NativeGround) :
    nativePairing (groundAction data determinantUnit charge first) second =
      epsilon data charge (-charge) *
        nativePairing first (groundAction data determinantUnit (-charge) second) := by
  have cancellation : groundAction data determinantUnit charge
      (epsilon data charge (-charge) • groundAction data determinantUnit (-charge) second) =
        second := by
    rw [map_smul]
    change epsilon data charge (-charge) •
      ((groundAction data determinantUnit charge *
        groundAction data determinantUnit (-charge)) second) = second
    rw [LatticeHalfFockGroundProducts.ground_action_product, add_neg_cancel]
    have zeroAction : groundAction data determinantUnit 0 = (1 : Module.End ℂ NativeGround) := by
      change groundRepresentation data determinantUnit 1 = 1
      exact map_one _
    rw [zeroAction]
    change epsilon data charge (-charge) • (epsilon data charge (-charge) • second) = second
    rw [smul_smul, original_epsilon_inverse, sign_square, one_smul]
  have equation := native_pairing_invariant (groundLift data charge) first
    (epsilon data charge (-charge) • groundAction data determinantUnit (-charge) second)
  change nativePairing (groundAction data determinantUnit charge first)
    (groundAction data determinantUnit charge
      (epsilon data charge (-charge) • groundAction data determinantUnit (-charge) second)) = _
    at equation
  simpa only [cancellation, map_smul, smul_eq_mul] using equation

theorem chosen_native_symmetric_self_duality :
    nativePairing ≠ 0 ∧ nativePairing.IsSymm ∧ nativePairing.Nondegenerate ∧
    (∀ element : Extension data ⧸ K data, ∀ first second,
      nativePairing (nativeRho element first) (nativeRho element second) =
        nativePairing first second) ∧
    (∀ form : LinearMap.BilinForm ℂ NativeGround,
      (∀ element : Extension data ⧸ K data, ∀ first second,
        form (nativeRho element first) (nativeRho element second) = form first second) →
      ∃ scalar : ℂ, form = scalar • nativePairing) ∧
    (∀ charge : Charge data, groundAction data determinantUnit charge ^ 2 =
      complexSign (quadratic data (reduceCharge data charge)) • (1 : Module.End ℂ NativeGround)) ∧
    (Finset.univ.noncommProd (BinaryProjectorProduct.projectorFactor nativeActions)
      (fun first _ second _ _ =>
        BinaryProjectorProduct.factors_commute nativeActions first second) = Pplus) ∧
    (∀ charge : Charge data, ∀ first second,
      nativePairing (groundAction data determinantUnit charge first) second =
        epsilon data charge (-charge) *
          nativePairing first (groundAction data determinantUnit (-charge) second)) :=
  ⟨native_pairing_nonzero, native_pairing_symm, native_pairing_nondegenerate,
    native_pairing_invariant, invariant_form_unique, original_integral_square,
    Pplus_product, original_integral_adjoint⟩

#print axioms chosen_native_symmetric_self_duality

end

end D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
