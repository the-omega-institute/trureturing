/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A literal Leech hyperbolic frame normalizes the original chosen ground action. -/

import D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open GolayLeech.ExplicitLeechLattice GolayLeech.ExplicitLeechBasis
open LeechQuadratic OperatorAlgebra
open scoped BigOperators

noncomputable section

attribute [local irreducible] hyperbolicBasis
attribute [local irreducible] actionScalar

local instance : (K data).Normal := K_normal data

instance nativeQuotientGroup : Group (Extension data ⧸ K data) := inferInstance

local instance : LinearOrder (Fin 12 ⊕ Fin 12) :=
  LatticeTwistedGroundRealization.coordinateOrder 12

def determinantUnit : IsUnit data.G.det := by
  change IsUnit gramMatrix.det
  rw [gram_determinant]
  exact isUnit_one

abbrev NativeGround := ActualGround data determinantUnit

def nativeRho : Representation ℂ (Extension data ⧸ K data) NativeGround :=
  groundRepresentation data determinantUnit

theorem native_rank : groundRank data determinantUnit = 12 := by
  have properties := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation data determinantUnit))
  have rank := properties.1
  change 24 = groundRank data determinantUnit + groundRank data determinantUnit at rank
  omega

theorem native_dimension : Module.finrank ℂ NativeGround = 4096 := by
  change Module.finrank ℂ (Ground (groundRank data determinantUnit)) = 4096
  rw [native_rank]
  simp [Ground, Half, F₂, Module.finrank_fintype_fun_eq_card]

theorem native_central : nativeRho (QuotientGroup.mk (⟨1, 0⟩ : Extension data)) =
    -(1 : Module.End ℂ NativeGround) := by
  exact (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation data determinantUnit))).2.2.1

theorem frame_symplectic :
    D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing data)
      hyperbolicBasis := by
  constructor
  · intro first second
    simp [hyperbolic_basis_apply, literal_certificate.2, partner]
  · intro first second
    simp [hyperbolic_basis_apply, literal_certificate.2, partner]
  · intro index
    simp [hyperbolic_basis_apply, literal_certificate.2, partner]
  · intro first second distinct
    simp [hyperbolic_basis_apply, literal_certificate.2, partner, distinct]

theorem correction_diagonal (index : Fin 12 ⊕ Fin 12) :
    squareCorrection data hyperbolicBasis index index = 0 := by
  simp only [squareCorrection, Matrix.add_apply, coordinateCocycle,
    LinearMap.BilinForm.toMatrix_apply]
  change modTwoCocycle data (hyperbolicBasis index) (hyperbolicBasis index) +
    standardMatrix 12 index index = 0
  rw [← quadratic_diagonal, original_plus_type.1]
  cases index <;> simp [standardMatrix]

theorem scalar_is_sign (element : ReducedExtension data) :
    actionScalar data hyperbolicBasis element = complexSign
      (element.sign + normalExponent (squareCorrection data hyperbolicBasis)
        (hyperbolicBasis.equivFun element.charge)) := by
  unfold actionScalar liftPhase diagonalPhase
  simp [correction_diagonal, fourthRoot, complexSign_add]

theorem scalar_square (element : ReducedExtension data) :
    actionScalar data hyperbolicBasis element * actionScalar data hyperbolicBasis element = 1 := by
  simp only [scalar_is_sign, sign_square]

theorem scalar_multiplication (first second : ReducedExtension data) :
    actionScalar data hyperbolicBasis (first * second) =
      actionScalar data hyperbolicBasis first * actionScalar data hyperbolicBasis second *
        complexSign (standardCocycle (hyperbolicBasis.equivFun first.charge)
          (hyperbolicBasis.equivFun second.charge)) := by
  have evaluates (element : ReducedExtension data) (function : Ground 12) (half : Half 12) :
      reducedRepresentation data hyperbolicBasis frame_symplectic element function half =
        actionScalar data hyperbolicBasis element *
          (complexSign (dot (rightHalf (hyperbolicBasis.equivFun element.charge)) half) *
            function (half + leftHalf (hyperbolicBasis.equivFun element.charge))) := rfl
  have equation := congrArg (fun operator : Module.End ℂ (Ground 12) =>
    operator (fun _ => 1) 0)
    (map_mul (reducedRepresentation data hyperbolicBasis frame_symplectic) first second)
  simp only [Module.End.mul_apply, evaluates, Pi.zero_apply, zero_add,
    mul_one, dot, mul_zero, Finset.sum_const_zero, sign_zero, one_mul] at equation
  simpa only [standardCocycle, dot, mul_assoc] using equation

def reducedNative : Representation ℂ (ReducedExtension data) NativeGround :=
  nativeRho.comp (quotientEquiv data).symm.toMonoidHom

def normalized (element : ReducedExtension data) : Module.End ℂ NativeGround :=
  actionScalar data hyperbolicBasis element • reducedNative element

def coordinateElement (coordinates : Coordinates 12) : ReducedExtension data :=
  ⟨0, hyperbolicBasis.equivFun.symm coordinates⟩

def coordinateAction (coordinates : Coordinates 12) : Module.End ℂ NativeGround :=
  normalized (coordinateElement coordinates)

theorem normalized_mul (first second : ReducedExtension data) :
    normalized first * normalized second =
      complexSign (standardCocycle (hyperbolicBasis.equivFun first.charge)
        (hyperbolicBasis.equivFun second.charge)) • normalized (first * second) := by
  unfold normalized
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    ← (map_mul reducedNative first second), smul_smul,
    scalar_multiplication]
  apply congrArg (fun scalar : ℂ => scalar • reducedNative (first * second))
  have square := sign_square (standardCocycle (hyperbolicBasis.equivFun first.charge)
    (hyperbolicBasis.equivFun second.charge))
  linear_combination -(actionScalar data hyperbolicBasis first *
    actionScalar data hyperbolicBasis second) * square

theorem reduced_central (sign : F₂) :
    reducedNative (⟨sign, 0⟩ : ReducedExtension data) =
      complexSign sign • (1 : Module.End ℂ NativeGround) := by
  have lifted : (quotientEquiv data).symm (⟨sign, 0⟩ : ReducedExtension data) =
      QuotientGroup.mk (⟨sign, 0⟩ : Extension data) := by
    apply (quotientEquiv data).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change nativeRho ((quotientEquiv data).symm _) = _
  rw [lifted]
  have cases : sign = 0 ∨ sign = 1 :=
    (by decide : ∀ value : F₂, value = 0 ∨ value = 1) sign
  rcases cases with zero | one
  · subst sign
    change nativeRho 1 = _
    simp [sign_zero]
  · subst sign
    rw [native_central, sign_one]
    exact (neg_one_smul ℂ (1 : Module.End ℂ NativeGround)).symm

theorem normalized_sign (sign : F₂) (charge : ModTwoCharge data) :
    normalized (⟨sign, charge⟩ : ReducedExtension data) = normalized ⟨0, charge⟩ := by
  have decomposition : (⟨sign, charge⟩ : ReducedExtension data) =
      (⟨sign, 0⟩ : ReducedExtension data) * ⟨0, charge⟩ := by
    apply SignExtension.ext
    · change sign = sign + 0 + modTwoCocycle data 0 charge
      simp
    · change charge = 0 + charge
      simp
  have action : reducedNative (⟨sign, charge⟩ : ReducedExtension data) =
      complexSign sign • reducedNative (⟨0, charge⟩ : ReducedExtension data) := by
    rw [decomposition, map_mul, reduced_central, smul_mul_assoc, one_mul]
  unfold normalized
  rw [action, smul_smul]
  apply congrArg (fun scalar : ℂ => scalar • reducedNative (⟨0, charge⟩ : ReducedExtension data))
  rw [scalar_is_sign, scalar_is_sign]
  change complexSign (sign + normalExponent (squareCorrection data hyperbolicBasis)
      (hyperbolicBasis.equivFun charge)) * complexSign sign =
    complexSign (0 + normalExponent (squareCorrection data hyperbolicBasis)
      (hyperbolicBasis.equivFun charge))
  rw [complexSign_add, zero_add]
  have square := sign_square sign
  linear_combination complexSign (normalExponent (squareCorrection data hyperbolicBasis)
    (hyperbolicBasis.equivFun charge)) * square

theorem coordinate_action_mul (first second : Coordinates 12) :
    coordinateAction first * coordinateAction second =
      complexSign (standardCocycle first second) • coordinateAction (first + second) := by
  unfold coordinateAction
  rw [normalized_mul]
  simp only [coordinateElement, LinearEquiv.apply_symm_apply]
  have charges : hyperbolicBasis.equivFun.symm first + hyperbolicBasis.equivFun.symm second =
      hyperbolicBasis.equivFun.symm (first + second) := (map_add _ _ _).symm
  change _ • normalized ⟨_, _ + _⟩ = _
  rw [normalized_sign, charges]

theorem coordinate_action_zero : coordinateAction 0 = 1 := by
  unfold coordinateAction normalized coordinateElement
  simp [scalar_is_sign, normalExponent, sign_zero]
  change reducedNative 1 = 1
  exact map_one reducedNative

def leftCoordinates (half : Half 12) : Coordinates 12 := Sum.elim half 0

def rightCoordinates (half : Half 12) : Coordinates 12 := Sum.elim 0 half

def leftAction (half : Half 12) : Module.End ℂ NativeGround :=
  coordinateAction (leftCoordinates half)

def rightAction (half : Half 12) : Module.End ℂ NativeGround :=
  coordinateAction (rightCoordinates half)

theorem left_action_add (first second : Half 12) :
    leftAction (first + second) = leftAction first * leftAction second := by
  have added : leftCoordinates (first + second) = leftCoordinates first + leftCoordinates second := by
    ext (index | index) <;> simp [leftCoordinates]
  have law := coordinate_action_mul (leftCoordinates first) (leftCoordinates second)
  have cocycle : standardCocycle (leftCoordinates first) (leftCoordinates second) = 0 := by
    simp [standardCocycle, dot, leftHalf, rightHalf, leftCoordinates]
  rw [cocycle, sign_zero, one_smul, ← added] at law
  exact law.symm

theorem right_action_add (first second : Half 12) :
    rightAction (first + second) = rightAction first * rightAction second := by
  have added : rightCoordinates (first + second) = rightCoordinates first + rightCoordinates second := by
    ext (index | index) <;> simp [rightCoordinates]
  have law := coordinate_action_mul (rightCoordinates first) (rightCoordinates second)
  have cocycle : standardCocycle (rightCoordinates first) (rightCoordinates second) = 0 := by
    simp [standardCocycle, dot, leftHalf, rightHalf, rightCoordinates]
  rw [cocycle, sign_zero, one_smul, ← added] at law
  exact law.symm

theorem left_action_zero : leftAction 0 = 1 := by
  have coordinates : leftCoordinates 0 = 0 := by ext (index | index) <;> rfl
  rw [leftAction, coordinates, coordinate_action_zero]

theorem right_action_zero : rightAction 0 = 1 := by
  have coordinates : rightCoordinates 0 = 0 := by ext (index | index) <;> rfl
  rw [rightAction, coordinates, coordinate_action_zero]

theorem left_action_square (half : Half 12) : leftAction half * leftAction half = 1 := by
  have zero : half + half = 0 := by ext index; exact CharTwo.add_self_eq_zero (half index)
  rw [← left_action_add, zero, left_action_zero]

theorem right_action_square (half : Half 12) : rightAction half * rightAction half = 1 := by
  have zero : half + half = 0 := by ext index; exact CharTwo.add_self_eq_zero (half index)
  rw [← right_action_add, zero, right_action_zero]

theorem right_action_commute (first second : Half 12) :
    Commute (rightAction first) (rightAction second) := by
  change _ * _ = _ * _
  rw [← right_action_add, ← right_action_add, add_comm]

theorem cross_action (left right : Half 12) :
    rightAction right * leftAction left =
      complexSign (dot right left) • (leftAction left * rightAction right) := by
  have first := coordinate_action_mul (leftCoordinates left) (rightCoordinates right)
  have second := coordinate_action_mul (rightCoordinates right) (leftCoordinates left)
  have first' : leftAction left * rightAction right = complexSign (dot right left) •
      coordinateAction (leftCoordinates left + rightCoordinates right) := by
    simpa [leftAction, rightAction, standardCocycle, leftHalf, rightHalf,
      leftCoordinates, rightCoordinates, dot] using first
  have second' : rightAction right * leftAction left =
      coordinateAction (leftCoordinates left + rightCoordinates right) := by
    simpa [leftAction, rightAction, standardCocycle, leftHalf, rightHalf,
      leftCoordinates, rightCoordinates, dot, add_comm, sign_zero] using second
  rw [first', smul_smul, sign_square, one_smul]
  exact second'

def involutionF (index : Fin 12) : Module.End ℂ NativeGround :=
  rightAction (Pi.single index 1)

def involutionE (index : Fin 12) : Module.End ℂ NativeGround :=
  leftAction (Pi.single index 1)

end

end D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions
