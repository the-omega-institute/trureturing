/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeOrbit
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The chosen native Leech ground has a nonzero hyperbolic projector and orbit intertwiner. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions
import D5.S3.VertexAlgebra.TwistedGround.BinaryOrbit
import D5.S3.VertexAlgebra.TwistedGround.BinaryProjectorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.TwistedGround.NativeOrbit

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open GolayLeech.ExplicitLeechLattice
open LeechQuadratic NativeHyperbolicActions OperatorAlgebra
open scoped BigOperators

noncomputable section

attribute [local irreducible] hyperbolicBasis actionScalar

def nativeActions : BinaryOrbit.Actions 12 NativeGround where
  left := leftAction
  right := rightAction
  left_zero := left_action_zero
  right_zero := right_action_zero
  left_add := left_action_add
  right_add := right_action_add
  cross := cross_action

theorem native_dimension_power : Module.finrank ℂ NativeGround = 2 ^ 12 := by
  rw [native_dimension]
  norm_num

theorem right_trace (half : Half 12) (nonzero : half ≠ 0) :
    LinearMap.trace ℂ NativeGround (rightAction half) = 0 := by
  have coordinates_nonzero : rightCoordinates half ≠ 0 := by
    intro zero
    apply nonzero
    funext index
    exact congrFun zero (Sum.inr index)
  have charge_nonzero :
      quotientCharge data ((quotientEquiv data).symm
        (coordinateElement (rightCoordinates half))) ≠ 0 := by
    simp only [quotientCharge, MulEquiv.apply_symm_apply]
    change hyperbolicBasis.equivFun.symm (rightCoordinates half) ≠ 0
    intro zero
    apply coordinates_nonzero
    have mapped := congrArg hyperbolicBasis.equivFun zero
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using mapped
  have trace_zero := nonzero_charge_trace data determinantUnit nativeRho native_central _
    charge_nonzero
  change LinearMap.trace ℂ NativeGround
    (actionScalar data hyperbolicBasis (coordinateElement (rightCoordinates half)) •
      nativeRho ((quotientEquiv data).symm (coordinateElement (rightCoordinates half)))) = 0
  rw [map_smul, trace_zero, smul_zero]

def Pplus : Module.End ℂ NativeGround := BinaryOrbit.plusProjector nativeActions

theorem Pplus_product :
    Finset.univ.noncommProd (BinaryProjectorProduct.projectorFactor nativeActions)
      (fun first _ second _ _ =>
        BinaryProjectorProduct.factors_commute nativeActions first second) = Pplus :=
  BinaryProjectorProduct.product_equals_plus nativeActions

theorem Pplus_trace : LinearMap.trace ℂ NativeGround Pplus = 1 :=
  BinaryOrbit.plus_trace nativeActions native_dimension_power right_trace

theorem Pplus_nonzero : Pplus ≠ 0 :=
  BinaryOrbit.plus_nonzero nativeActions native_dimension_power right_trace

theorem original_image_exists : ∃ state : NativeGround, Pplus state ≠ 0 :=
  BinaryOrbit.image_vector_exists nativeActions native_dimension_power right_trace

def seed : NativeGround := Classical.choose original_image_exists

attribute [local irreducible] Pplus

theorem seed_image_nonzero : Pplus seed ≠ 0 := Classical.choose_spec original_image_exists

def nativeBasis : Module.Basis (Half 12) ℂ NativeGround :=
  BinaryOrbit.orbitBasis nativeActions seed native_dimension_power
    (by simpa only [Pplus] using seed_image_nonzero)

theorem native_basis_apply (half : Half 12) :
    nativeBasis half = leftAction half (Pplus seed) := by
  simpa only [nativeBasis, BinaryOrbit.orbit, nativeActions, Pplus] using
    BinaryOrbit.orbit_basis_apply nativeActions seed native_dimension_power
      (by simpa only [Pplus] using seed_image_nonzero) half

private theorem native_orbit_function : BinaryOrbit.orbit nativeActions seed =
    fun half => leftAction half (Pplus seed) := by
  funext half
  simp only [BinaryOrbit.orbit, nativeActions, Pplus]

theorem actual_orbit_spans :
    Submodule.span ℂ (Set.range (fun half => leftAction half (Pplus seed))) = ⊤ := by
  rw [← native_orbit_function]
  exact BinaryOrbit.orbit_spans nativeActions seed native_dimension_power
    (by simpa only [Pplus] using seed_image_nonzero)

theorem actual_orbit_independent :
    LinearIndependent ℂ (fun half => leftAction half (Pplus seed)) := by
  rw [← native_orbit_function]
  exact BinaryOrbit.orbit_independent nativeActions seed
    (by simpa only [Pplus] using seed_image_nonzero)

def intertwiner : Ground 12 ≃ₗ[ℂ] NativeGround := nativeBasis.equivFun.symm

theorem left_on_basis (first second : Half 12) :
    leftAction first (nativeBasis second) = nativeBasis (first + second) := by
  simp only [native_basis_apply]
  change (leftAction first * leftAction second) (Pplus seed) = _
  rw [← left_action_add]

theorem right_on_basis (character half : Half 12) :
    rightAction character (nativeBasis half) = complexSign (dot character half) • nativeBasis half := by
  simpa only [native_basis_apply, BinaryOrbit.orbit, nativeActions, Pplus] using
    BinaryOrbit.orbit_character nativeActions seed half character

theorem left_intertwiner (half : Half 12) (function : Ground 12) :
    leftAction half (intertwiner function) = intertwiner (shift half function) := by
  classical
  change leftAction half (nativeBasis.equivFun.symm function) =
    nativeBasis.equivFun.symm (shift half function)
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, left_on_basis, shift]
  apply Fintype.sum_equiv (Equiv.addLeft half)
  intro other
  have cancellation : half + other + half = other := by
    rw [add_assoc, add_comm other half, ← add_assoc, BinaryOrbit.half_add_self, zero_add]
  simp only [Equiv.coe_addLeft, cancellation]

theorem right_intertwiner (half : Half 12) (function : Ground 12) :
    rightAction half (intertwiner function) = intertwiner (diagonal half function) := by
  classical
  change rightAction half (nativeBasis.equivFun.symm function) =
    nativeBasis.equivFun.symm (diagonal half function)
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, right_on_basis,
    diagonal, smul_smul]
  apply Finset.sum_congr rfl
  intro other _
  rw [mul_comm]

theorem coordinate_intertwiner (coordinates : Coordinates 12) (function : Ground 12) :
    coordinateAction coordinates (intertwiner function) =
      intertwiner (weylOperator coordinates function) := by
  have decomposition : rightCoordinates (rightHalf coordinates) +
      leftCoordinates (leftHalf coordinates) = coordinates := by
    ext (index | index) <;> simp [rightCoordinates, leftCoordinates, rightHalf, leftHalf]
  have product := coordinate_action_mul (rightCoordinates (rightHalf coordinates))
    (leftCoordinates (leftHalf coordinates))
  have cocycle : standardCocycle (rightCoordinates (rightHalf coordinates))
      (leftCoordinates (leftHalf coordinates)) = 0 := by
    simp [standardCocycle, dot, leftHalf, rightHalf, rightCoordinates, leftCoordinates]
  rw [cocycle, sign_zero, one_smul, decomposition] at product
  rw [← product]
  change rightAction (rightHalf coordinates)
    (leftAction (leftHalf coordinates) (intertwiner function)) = _
  rw [left_intertwiner, right_intertwiner]
  rfl

theorem normalized_coordinate (element : ReducedExtension data) :
    normalized element = coordinateAction (hyperbolicBasis.equivFun element.charge) := by
  unfold coordinateAction coordinateElement
  rw [LinearEquiv.symm_apply_apply]
  exact normalized_sign element.sign element.charge

def modelRho : Representation ℂ (Extension data ⧸ K data) (Ground 12) :=
  quotientRepresentation data hyperbolicBasis frame_symplectic

theorem quotient_intertwiner (element : Extension data ⧸ K data) (function : Ground 12) :
    nativeRho element (intertwiner function) = intertwiner (modelRho element function) := by
  let reduced := quotientEquiv data element
  have twice : nativeRho element = actionScalar data hyperbolicBasis reduced • normalized reduced := by
    unfold normalized reducedNative
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, smul_smul, reduced,
      MulEquiv.symm_apply_apply, scalar_square, one_smul]
  rw [twice, LinearMap.smul_apply, normalized_coordinate, coordinate_intertwiner, ← map_smul]
  rfl

end

end D5.S3.VertexAlgebra.TwistedGround.NativeOrbit
