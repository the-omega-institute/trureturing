/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical charge-average positive form on the literal chosen-ground tensor. -/

import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockHermitian
import D5.S3.VertexAlgebra.TwistedGround.Charge.NativeChargeGeometry
import D5.S3.VertexAlgebra.LatticeHalfFockTensorFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTensorHermitian

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockHermitian
open TwistedGround.OperatorAlgebra TwistedGround.ChargeGeometry TwistedGround.ChargeHermitian
open LatticeHalfFock
open scoped BigOperators TensorProduct

noncomputable section

def coordinateMap (D : LatticeData) (hu : IsUnit D.G.det) (charge : ModTwoCharge D)
    (coordinate : Half (groundRank D hu)) : ActualTensor D hu →ₗ[ℂ] Oscillator D :=
  TensorProduct.lift {
    toFun := fun polynomial => {
      toFun := fun ground => chargeOperator D (groundRepresentation D hu) charge ground coordinate • polynomial
      map_add' := by intro first second; simp [add_smul]
      map_smul' := by intro scalar ground; simp [smul_smul, mul_comm] }
    map_add' := by intro first second; ext ground; simp [smul_add]
    map_smul' := by intro scalar polynomial; ext ground; simp [smul_smul, mul_comm] }

theorem coordinateMap_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : ModTwoCharge D) (coordinate : Half (groundRank D hu))
    (polynomial : Oscillator D) (ground : ActualGround D hu) :
    coordinateMap D hu charge coordinate (polynomial ⊗ₜ[ℂ] ground) =
      chargeOperator D (groundRepresentation D hu) charge ground coordinate • polynomial := rfl

theorem coordinate_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) :
    (∑ coordinate : Half (groundRank D hu),
      coordinateMap D hu 0 coordinate state ⊗ₜ[ℂ] (Pi.single coordinate 1)) = state := by
  classical
  induction state using TensorProduct.induction_on with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, firstProof, secondProof]
  | tmul polynomial ground =>
    simp only [coordinateMap_tmul, charge_zero, Module.End.one_apply,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum]
    congr 1
    ext coordinate
    simp [Pi.single_apply]

def coordinatePairing (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : ModTwoCharge D) (coordinate : Half (groundRank D hu)) :
    ActualTensor D hu →ₗ⋆[ℂ] ActualTensor D hu →ₗ[ℂ] ℂ :=
  { toFun := fun left => (halfForm D (coordinateMap D hu charge coordinate left)).comp
      (coordinateMap D hu charge coordinate)
    map_add' := by intro first second; ext right; simp
    map_smul' := by intro scalar left; ext right; simp }

def tensorForm (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu →ₗ⋆[ℂ] ActualTensor D hu →ₗ[ℂ] ℂ :=
  (Fintype.card (ModTwoCharge D) : ℂ)⁻¹ •
    ∑ charge : ModTwoCharge D, ∑ coordinate : Half (groundRank D hu),
      coordinatePairing D hu charge coordinate

theorem tensorForm_coordinates (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : ActualTensor D hu) :
    tensorForm D hu left right = (Fintype.card (ModTwoCharge D) : ℂ)⁻¹ *
      ∑ charge : ModTwoCharge D, ∑ coordinate : Half (groundRank D hu),
        halfForm D (coordinateMap D hu charge coordinate left)
          (coordinateMap D hu charge coordinate right) := by
  simp [tensorForm, coordinatePairing, LinearMap.sum_apply, LinearMap.smul_apply]

theorem tensorForm_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Oscillator D) (first second : ActualGround D hu) :
    tensorForm D hu (left ⊗ₜ[ℂ] first) (right ⊗ₜ[ℂ] second) =
      halfForm D left right * chargeForm D (groundRepresentation D hu) first second := by
  rw [tensorForm_coordinates]
  simp only [coordinateMap_tmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    RingHom.id_apply, starRingEnd_apply, smul_eq_mul, chargeForm, coordinateForm]
  simp_rw [show ∀ first second value : ℂ, first * (second * value) =
    value * (first * second) from fun _ _ _ => by ring]
  simp only [← Finset.mul_sum]
  simp only [mul_comm]
  ring

theorem tensorForm_isSymm (D : LatticeData) (hu : IsUnit D.G.det) :
    LinearMap.IsSymm (tensorForm D hu) := by
  constructor
  intro left right
  simp only [tensorForm_coordinates, map_mul, map_inv₀, map_natCast, map_sum,
    (halfForm_isSymm D).eq]

theorem tensorForm_real_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) : (tensorForm D hu state state).im = 0 := by
  have identity := congrArg Complex.im ((tensorForm_isSymm D hu).eq state state)
  simp only [Complex.star_def, Complex.conj_im] at identity
  linarith

theorem halfForm_nonnegative (D : LatticeData)
    (positive : (LatticeOscillatorFockMetric.gramReal D).PosDef) (state : Oscillator D) :
    0 ≤ (halfForm D state state).re := by
  by_cases zero : state = 0
  · simp [zero]
  · exact le_of_lt (halfForm_positive D positive state zero)

theorem tensorForm_diagonal_re (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) :
    (tensorForm D hu state state).re = (Fintype.card (ModTwoCharge D) : ℝ)⁻¹ *
      ∑ charge : ModTwoCharge D, ∑ coordinate : Half (groundRank D hu),
        (halfForm D (coordinateMap D hu charge coordinate state)
          (coordinateMap D hu charge coordinate state)).re := by
  rw [tensorForm_coordinates]
  rw [show (Fintype.card (ModTwoCharge D) : ℂ)⁻¹ =
    (((Fintype.card (ModTwoCharge D) : ℝ)⁻¹ : ℝ) : ℂ) by simp]
  simp only [Complex.re_ofReal_mul, Complex.re_sum]

theorem tensorForm_nonnegative (D : LatticeData) (hu : IsUnit D.G.det)
    (positive : (LatticeOscillatorFockMetric.gramReal D).PosDef) (state : ActualTensor D hu) :
    0 ≤ (tensorForm D hu state state).re := by
  rw [tensorForm_diagonal_re]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun charge _ =>
    Finset.sum_nonneg fun coordinate _ => halfForm_nonnegative D positive _)

theorem tensorForm_positive (D : LatticeData) (hu : IsUnit D.G.det)
    (positive : (LatticeOscillatorFockMetric.gramReal D).PosDef)
    (state : ActualTensor D hu) (nonzero : state ≠ 0) :
    0 < (tensorForm D hu state state).re := by
  classical
  have separates : ∃ coordinate, coordinateMap D hu 0 coordinate state ≠ 0 := by
    by_contra absent
    push_neg at absent
    have identity := coordinate_reconstruction D hu state
    simp only [absent, TensorProduct.zero_tmul, Finset.sum_const_zero] at identity
    exact nonzero identity.symm
  obtain ⟨coordinate, value⟩ := separates
  rw [tensorForm_diagonal_re]
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply (Finset.sum_pos_iff_of_nonneg (fun charge _ =>
    Finset.sum_nonneg fun axis _ => halfForm_nonnegative D positive _)).2
  refine ⟨0, Finset.mem_univ _, ?_⟩
  apply (Finset.sum_pos_iff_of_nonneg (fun axis _ => halfForm_nonnegative D positive _)).2
  exact ⟨coordinate, Finset.mem_univ _, halfForm_positive D positive _ value⟩

theorem coordinateMap_tensorEnd (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : ModTwoCharge D) (coordinate : Half (groundRank D hu))
    (operator : Module.End ℂ (Oscillator D)) (state : ActualTensor D hu) :
    coordinateMap D hu charge coordinate (tensorEnd D (ActualGround D hu) operator state) =
      operator (coordinateMap D hu charge coordinate state) := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | tmul polynomial ground => simp [tensorEnd, coordinateMap_tmul]

theorem tensorEnd_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (operator adjoint : Module.End ℂ (Oscillator D))
    (identity : ∀ left right, halfForm D (operator left) right = halfForm D left (adjoint right))
    (left right : ActualTensor D hu) :
    tensorForm D hu (tensorEnd D (ActualGround D hu) operator left) right =
      tensorForm D hu left (tensorEnd D (ActualGround D hu) adjoint right) := by
  simp only [tensorForm_coordinates, coordinateMap_tensorEnd, identity]

theorem tensorCurrent_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (axis : Fin D.rank) (mode : ℤ) (left right : ActualTensor D hu) :
    tensorForm D hu (tensorCurrent D (ActualGround D hu) axis mode left) right =
      tensorForm D hu left (tensorCurrent D (ActualGround D hu) axis (-mode - 1) right) := by
  exact tensorEnd_adjoint D hu _ _ (halfForm_current_adjoint D axis mode) left right

def groundMetricMap (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualGround D hu →ₗ[ℂ] ActualGround D hu where
  toFun ground coordinate := chargeForm D (groundRepresentation D hu) (Pi.single coordinate 1) ground
  map_add' first second := by ext coordinate; exact charge_form_add_right D _ _ _ _
  map_smul' scalar ground := by ext coordinate; exact charge_form_smul_right D _ _ _ _

theorem groundMetricMap_injective (D : LatticeData) (hu : IsUnit D.G.det) :
    Function.Injective (groundMetricMap D hu) := by
  classical
  apply LinearMap.ker_eq_bot.1
  apply LinearMap.ker_eq_bot'.2
  intro ground zero
  apply (charge_form_right_radical D (groundRepresentation D hu) ground).1
  intro other
  have expansion : other = ∑ coordinate, other coordinate • Pi.single coordinate 1 := by
    ext coordinate
    simp [Pi.single_apply]
  rw [expansion]
  have coordinate_zero : ∀ coordinate,
      chargeForm D (groundRepresentation D hu) (Pi.single coordinate 1) ground = 0 := by
    intro coordinate
    exact congrFun zero coordinate
  change chargeForm D (groundRepresentation D hu) _ ground = 0
  induction (Finset.univ : Finset (Half (groundRank D hu))) using Finset.induction_on with
  | empty => simp [charge_form_add_left, charge_form_smul_left, chargeForm, coordinateForm]
  | @insert coordinate remaining absent induction_hypothesis =>
    rw [Finset.sum_insert absent, charge_form_add_left, charge_form_smul_left,
      coordinate_zero, mul_zero, zero_add, induction_hypothesis]

theorem metric_coordinate_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) (coordinate : Half (groundRank D hu))
    (polynomial : Oscillator D) :
    tensorForm D hu state (polynomial ⊗ₜ[ℂ] Pi.single coordinate 1) =
      halfForm D (coordinateMap D hu 0 coordinate
        (TensorProduct.map LinearMap.id (groundMetricMap D hu) state)) polynomial := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, secondProof]
  | tmul matter ground =>
    rw [tensorForm_tmul]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, coordinateMap_tmul,
      charge_zero, Module.End.one_apply, groundMetricMap, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    rw [charge_form_hermitian]
    exact mul_comm _ _

theorem tensorForm_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1) :
    (tensorForm D hu).Nondegenerate := by
  classical
  have left_separating : (tensorForm D hu).SeparatingLeft := by
    intro state radical
    have coordinate_zero : ∀ coordinate,
        coordinateMap D hu 0 coordinate
          (TensorProduct.map LinearMap.id (groundMetricMap D hu) state) = 0 := by
      intro coordinate
      apply (halfForm_nondegenerate D matrixH hHG hGH).1
      intro polynomial
      rw [← metric_coordinate_pairing]
      exact radical _
    have transformed_zero := coordinate_reconstruction D hu
      (TensorProduct.map LinearMap.id (groundMetricMap D hu) state)
    simp only [coordinate_zero, TensorProduct.zero_tmul, Finset.sum_const_zero] at transformed_zero
    let equivalence : ActualGround D hu ≃ₗ[ℂ] ActualGround D hu :=
      LinearEquiv.ofBijective (groundMetricMap D hu)
        ⟨groundMetricMap_injective D hu,
          LinearMap.injective_iff_surjective.1 (groundMetricMap_injective D hu)⟩
    have recovered := congrArg
      (TensorProduct.map (LinearMap.id : Module.End ℂ (Oscillator D)) equivalence.symm.toLinearMap)
      transformed_zero.symm
    have reconstruction : ∀ value : ActualTensor D hu,
        TensorProduct.map LinearMap.id equivalence.symm.toLinearMap
          (TensorProduct.map LinearMap.id (groundMetricMap D hu) value) = value := by
      intro value
      induction value using TensorProduct.induction_on with
      | zero => simp
      | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]
      | tmul polynomial ground =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
        change polynomial ⊗ₜ[ℂ] equivalence.symm (equivalence ground) = _
        rw [LinearEquiv.symm_apply_apply]
    simpa only [reconstruction, map_zero] using recovered
  refine ⟨left_separating, ?_⟩
  intro state radical
  apply left_separating state
  intro other
  have symmetry := (tensorForm_isSymm D hu).eq other state
  rw [radical other, map_zero] at symmetry
  exact symmetry.symm

private theorem groundAdjoint_lift (D : LatticeData) (hu : IsUnit D.G.det)
    (operator adjoint : Module.End ℂ (ActualGround D hu))
    (identity : ∀ first second,
      chargeForm D (groundRepresentation D hu) (operator first) second =
        chargeForm D (groundRepresentation D hu) first (adjoint second))
    (left right : ActualTensor D hu) :
    tensorForm D hu (TensorProduct.map LinearMap.id operator left) right =
      tensorForm D hu left (TensorProduct.map LinearMap.id adjoint right) := by
  induction left using TensorProduct.induction_on generalizing right with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, secondProof]
  | tmul polynomial ground =>
    induction right using TensorProduct.induction_on with
    | zero => simp
    | add first second firstProof secondProof =>
      simp only [map_add, LinearMap.add_apply, firstProof, secondProof]
    | tmul otherPolynomial otherGround =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorForm_tmul, identity]

private theorem actualCentral (D : LatticeData) (hu : IsUnit D.G.det) :
    groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) := by
  exact (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.2.1

theorem tensor_ground_invariant (D : LatticeData) (hu : IsUnit D.G.det)
    (element : Extension D ⧸ K D) (left right : ActualTensor D hu) :
    tensorForm D hu (TensorProduct.map LinearMap.id (groundRepresentation D hu element) left)
      (TensorProduct.map LinearMap.id (groundRepresentation D hu element) right) =
        tensorForm D hu left right := by
  rw [groundAdjoint_lift D hu _ _
    (charge_form_inverse_adjoint D (groundRepresentation D hu) (actualCentral D hu) element)]
  have cancellation : ∀ state : ActualTensor D hu,
      TensorProduct.map LinearMap.id (groundRepresentation D hu element⁻¹)
        (TensorProduct.map LinearMap.id (groundRepresentation D hu element) state) = state := by
    intro state
    induction state using TensorProduct.induction_on with
    | zero => simp
    | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]
    | tmul polynomial ground =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        Representation.inv_self_apply]
  rw [cancellation]

theorem tensor_ground_signed_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (left right : ActualTensor D hu) :
    tensorForm D hu (TensorProduct.map LinearMap.id (groundAction D hu charge) left) right =
      epsilon D charge charge *
        tensorForm D hu left (TensorProduct.map LinearMap.id (groundAction D hu (-charge)) right) := by
  have ground_law :=
    TwistedGround.NativeChargeGeometry.native_ground_signed_adjoint D hu charge
  have lifted := groundAdjoint_lift D hu (groundAction D hu charge)
    (epsilon D charge charge • groundAction D hu (-charge))
    (fun first second => by
      simp only [LinearMap.smul_apply, charge_form_smul_right]
      exact (ground_law first second).1) left right
  have scalar_lift : TensorProduct.map
      (LinearMap.id : Module.End ℂ (Oscillator D))
      (epsilon D charge charge • groundAction D hu (-charge)) =
        epsilon D charge charge • TensorProduct.map LinearMap.id (groundAction D hu (-charge)) := by
    apply TensorProduct.ext'
    intro polynomial ground
    simp [TensorProduct.tmul_smul]
  rw [scalar_lift, LinearMap.smul_apply, map_smul] at lifted
  exact lifted

end
end D5.S3.VertexAlgebra.LatticeHalfFockTensorHermitian
