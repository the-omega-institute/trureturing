import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields
import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyReassembly
import D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostStressBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TensorConformal.OriginalTopologicalApplications

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q B M G)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes (product parity)
open LatticeBcGhostCohomologyFields (translation vacuum)
open LatticeBcGhostCohomologyJacobi
open scoped TensorProduct VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem translation_zero (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1) (state : OriginalCohomology D H) :
    translation D H state = 0 := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [LatticeBcGhostCohomologyFields.translation_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (LatticeBcGhostStressBoundary.cycle_translation_boundary D H
    leftInverse rightInverse representative.val representative.property).2

theorem nonconstant_product_zero (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1) (mode : ℤ) (nonconstant : mode ≠ -1)
    (left right : OriginalCohomology D H) : product D H mode left right = 0 := by
  have law := LatticeBcGhostCohomologyFields.derivative D H left right (mode + 1)
  rw [translation_zero D H leftInverse rightInverse, map_zero,
    LinearMap.zero_apply, show mode + 1 - 1 = mode by omega] at law
  have scalar : -((mode + 1 : ℤ) : ℂ) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (show mode + 1 ≠ 0 by omega)
  exact (smul_eq_zero.mp law.symm).resolve_left scalar

theorem actual_total_mode_zero (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1) (critical : D.rank = 26)
    (mode : ℤ) (state : OriginalCycles D H) :
    (OriginalBoundaries D H).mkQ
      ⟨LatticeBcGhostTotalConformal.totalMode D H mode state.val,
        ((LatticeBcGhostStressBoundary.critical_cycle_preservation D H
          leftInverse rightInverse critical).2.1 mode state.val state.property).1⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (LatticeBcGhostStressBoundary.cycle_mode_boundary D H mode
    state.val state.property).2.1

theorem B0_square (state : State D) : B D 0 (B D 0 state) = 0 := by
  have car := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.b_b (K := ℂ) 0 0)
  simp only [map_add, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at car
  have value := LinearMap.congr_fun car state
  change B D 0 (B D 0 state) + B D 0 (B D 0 state) = 0 at value
  have twice : (2 : ℂ) • B D 0 (B D 0 state) = 0 := by
    simpa only [two_smul] using value
  exact (smul_eq_zero.mp twice).resolve_left (by norm_num)

theorem B0_energy (state : State D) :
    (M D H 0 + G D 0) (B D 0 state) =
      B D 0 ((M D H 0 + G D 0) state) := by
  have first := LinearMap.congr_fun (LatticeBcGhostBrstCharge.ward_identity D H 0)
    (B D 0 state)
  have second := congrArg (B D 0)
    (LinearMap.congr_fun (LatticeBcGhostBrstCharge.ward_identity D H 0) state)
  change Q D H (B D 0 (B D 0 state)) + B D 0 (Q D H (B D 0 state)) = _ at first
  change B D 0 (Q D H (B D 0 state) + B D 0 (Q D H state)) = _ at second
  rw [B0_square D, map_zero, zero_add] at first
  rw [map_add, B0_square D, add_zero] at second
  exact first.symm.trans second

theorem B0_zeroSpace (state : State D)
    (member : state ∈ OriginalBrstReassembly.zeroSpace D H) :
    B D 0 state ∈ OriginalBrstReassembly.zeroSpace D H := by
  change (M D H 0 + G D 0) (B D 0 state) = 0
  rw [B0_energy D H, member, map_zero]

theorem B0_zeroCycle (state : State D)
    (member : state ∈ OriginalBrstReassembly.zeroSpace D H) (cycle : Q D H state = 0) :
    Q D H (B D 0 state) = 0 := by
  have ward := LinearMap.congr_fun (LatticeBcGhostBrstCharge.ward_identity D H 0) state
  change Q D H (B D 0 state) + B D 0 (Q D H state) = _ at ward
  change (M D H 0 + G D 0) state = 0 at member
  simpa only [cycle, map_zero, add_zero, member] using ward

def zeroCycleB0 : Module.End ℂ
    (OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :=
  ((B D 0).comp
    (OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)).subtype).codRestrict
      (OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H))
      (fun state => ⟨B0_zeroSpace D H state.val state.property.1,
        B0_zeroCycle D H state.val state.property.1 state.property.2⟩)

variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

theorem zeroCycleB0_boundary
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H))
    (boundary : state ∈ OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)) :
    zeroCycleB0 D H state ∈
      OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
        (OriginalBrstReassembly.zeroSpace D H)
        (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse) := by
  obtain ⟨preimage, equation⟩ :=
    (OriginalBrstReassembly.boundary_iff D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse) state).mp boundary
  apply (OriginalBrstReassembly.boundary_iff D H leftInverse rightInverse critical
    (OriginalBrstReassembly.zeroSpace D H)
    (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse) _).mpr
  refine ⟨⟨-(B D 0 preimage.val),
    (OriginalBrstReassembly.zeroSpace D H).neg_mem
      (B0_zeroSpace D H preimage.val preimage.property)⟩, ?_⟩
  have ward := LinearMap.congr_fun (LatticeBcGhostBrstCharge.ward_identity D H 0) preimage.val
  change Q D H (B D 0 preimage.val) + B D 0 (Q D H preimage.val) = _ at ward
  rw [preimage.property, equation] at ward
  change Q D H (-(B D 0 preimage.val)) = B D 0 state.val
  rw [map_neg]
  exact (neg_eq_iff_add_eq_zero).mpr ward

def zeroB0 : Module.End ℂ
    (OriginalBrstReassembly.zeroCohomology D H leftInverse rightInverse critical) :=
  (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
    (OriginalBrstReassembly.zeroSpace D H)
    (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mapQ _
      (zeroCycleB0 D H) (zeroCycleB0_boundary D H leftInverse rightInverse critical)

theorem zeroB0_square (state :
    OriginalBrstReassembly.zeroCohomology D H leftInverse rightInverse critical) :
    zeroB0 D H leftInverse rightInverse critical
      (zeroB0 D H leftInverse rightInverse critical state) = 0 := by
  obtain ⟨representative, rfl⟩ :=
    (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mkQ_surjective state
  change (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mkQ
        (zeroCycleB0 D H (zeroCycleB0 D H representative)) = 0
  have vanished : zeroCycleB0 D H (zeroCycleB0 D H representative) = 0 :=
    Subtype.ext (B0_square D representative.val)
  rw [vanished, map_zero]

def absoluteB0 : Module.End ℂ
    (OriginalBrstReassembly.absoluteCohomology D H leftInverse rightInverse critical) :=
  (OriginalBrstReassembly.zeroReductionEquiv D H leftInverse rightInverse critical).symm.toLinearMap.comp
    ((zeroB0 D H leftInverse rightInverse critical).comp
      (OriginalBrstReassembly.zeroReductionEquiv D H leftInverse rightInverse critical).toLinearMap)

theorem absoluteB0_square (state :
    OriginalBrstReassembly.absoluteCohomology D H leftInverse rightInverse critical) :
    absoluteB0 D H leftInverse rightInverse critical
      (absoluteB0 D H leftInverse rightInverse critical state) = 0 := by
  simp only [absoluteB0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, zeroB0_square, map_zero]

theorem associative_left (left right vector : OriginalCohomology D H) :
    leftSum D H 0 (-1) (-1) left right vector =
      product D H (-1) (product D H (-1) left right) vector := by
  unfold leftSum
  rw [finsum_eq_single _ 0]
  · simp [leftTerm, SuperFieldProducts.integerBinomial]
  · intro offset different
    simp [leftTerm, SuperFieldProducts.integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]

include leftInverse rightInverse in
theorem associative_right (firstParity secondParity : ℕ)
    (left right vector : OriginalCohomology D H) :
    rightSum D H firstParity secondParity 0 (-1) (-1) left right vector =
      product D H (-1) left (product D H (-1) right vector) := by
  unfold rightSum
  rw [finsum_eq_single _ 0]
  · simp only [rightTerm]
    norm_num only
    rw [nonconstant_product_zero D H leftInverse rightInverse (-2) (by decide)]
    simp [SuperFieldProducts.weight, SuperFieldProducts.integerBinomial]
  · intro offset different
    have firstMode : (0 + -1 - (offset : ℤ)) ≠ -1 := by omega
    have secondMode : (-1 + -1 - (offset : ℤ)) ≠ -1 := by omega
    simp only [rightTerm,
      nonconstant_product_zero D H leftInverse rightInverse _ firstMode,
      nonconstant_product_zero D H leftInverse rightInverse _ secondMode,
      smul_zero, sub_zero]

include leftInverse rightInverse in
theorem product_associative (left right vector : OriginalCohomology D H) :
    product D H (-1) (product D H (-1) left right) vector =
      product D H (-1) left (product D H (-1) right vector) := by
  have law := mixed_borcherds D H 0 (-1) (-1) left right vector
  rw [associative_left D H] at law
  simp only [associative_right D H leftInverse rightInverse] at law
  have expansion := congrArg₂
    (fun first second => product D H (-1) first (product D H (-1) second vector))
    (LatticeBcGhostCohomologyModes.parity_decomposition D H left)
    (LatticeBcGhostCohomologyModes.parity_decomposition D H right)
  simp only [map_add, LinearMap.add_apply] at expansion
  apply law.trans
  convert expansion using 1 <;> abel

include leftInverse rightInverse in
theorem product_supercommutative (firstParity secondParity : ℕ)
    (left right : OriginalCohomology D H)
    (firstFixed : parity D H firstParity left = left)
    (secondFixed : parity D H secondParity right = right) :
    product D H (-1) left right = SuperFieldProducts.koszul firstParity secondParity •
      product D H (-1) right left := by
  have law := borcherds D H firstParity secondParity (-1) 0 (-1)
    left right (vacuum D H) firstFixed secondFixed
  have leftZero : leftSum D H (-1) 0 (-1) left right (vacuum D H) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro offset
    simp only [leftTerm,
      nonconstant_product_zero D H leftInverse rightInverse (0 + (offset : ℤ)) (by omega),
      map_zero, LinearMap.zero_apply, smul_zero]
  have rightValue : rightSum D H firstParity secondParity (-1) 0 (-1)
      left right (vacuum D H) =
      product D H (-1) left right - SuperFieldProducts.koszul firstParity secondParity •
        product D H (-1) right left := by
    unfold rightSum
    rw [finsum_eq_single _ 0]
    · simp [rightTerm, SuperFieldProducts.weight, SuperFieldProducts.integerBinomial,
        SuperFieldProducts.epsilon, LatticeBcGhostCohomologyFields.creation]
    · intro offset different
      simp [rightTerm, SuperFieldProducts.weight, SuperFieldProducts.integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [leftZero, rightValue] at law
  exact sub_eq_zero.mp law.symm

open LatticeBcGhostTensorJacobi (mu)

theorem zero_mode_derivation (firstParity secondParity : ℕ)
    (left right vector : State D)
    (firstMember : left ∈ LatticeBcGhostTensorStateField.homogeneous firstParity)
    (secondMember : right ∈ LatticeBcGhostTensorStateField.homogeneous secondParity) :
    mu D left 0 (mu D right (-1) vector) =
      mu D (mu D left 0 right) (-1) vector +
        SuperFieldProducts.koszul firstParity secondParity •
          mu D right (-1) (mu D left 0 vector) := by
  have law := LatticeBcGhostTensorJacobi.borcherds D firstParity secondParity
    left right vector firstMember secondMember 0 (-1) 0
  change LatticeBcGhostTensorJacobi.borcherdsLeft D 0 0 (-1) left right vector =
    LatticeBcGhostTensorJacobi.borcherdsRight firstParity secondParity D
      0 0 (-1) left right vector at law
  rw [LatticeBcGhostTensorJacobi.borcherds_left_zero] at law
  have rightValue : LatticeBcGhostTensorJacobi.borcherdsRight firstParity secondParity D
      0 0 (-1) left right vector =
      mu D left 0 (mu D right (-1) vector) -
        SuperFieldProducts.koszul firstParity secondParity •
          mu D right (-1) (mu D left 0 vector) := by
    unfold LatticeBcGhostTensorJacobi.borcherdsRight
    rw [finsum_eq_single _ 0]
    · simp [LatticeBcGhostTensorJacobi.borcherdsRightTerm, mu,
        SuperFieldProducts.weight, SuperFieldProducts.integerBinomial,
        SuperFieldProducts.epsilon]
    · intro offset different
      simp [LatticeBcGhostTensorJacobi.borcherdsRightTerm, SuperFieldProducts.weight,
        SuperFieldProducts.integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [rightValue] at law
  exact (eq_sub_iff_add_eq.mp law).symm

theorem one_mode_commutator (firstParity secondParity : ℕ)
    (left right vector : State D)
    (firstMember : left ∈ LatticeBcGhostTensorStateField.homogeneous firstParity)
    (secondMember : right ∈ LatticeBcGhostTensorStateField.homogeneous secondParity) :
    mu D left 1 (mu D right (-1) vector) =
      mu D (mu D left 1 right) (-1) vector +
        SuperFieldProducts.koszul firstParity secondParity •
          mu D right (-1) (mu D left 1 vector) +
        mu D (mu D left 0 right) 0 vector := by
  classical
  have law := LatticeBcGhostTensorJacobi.borcherds D firstParity secondParity
    left right vector firstMember secondMember 1 (-1) 0
  change LatticeBcGhostTensorJacobi.borcherdsLeft D 1 0 (-1) left right vector =
    LatticeBcGhostTensorJacobi.borcherdsRight firstParity secondParity D
      1 0 (-1) left right vector at law
  have leftValue : LatticeBcGhostTensorJacobi.borcherdsLeft D 1 0 (-1) left right vector =
      mu D (mu D left 0 right) 0 vector + mu D (mu D left 1 right) (-1) vector := by
    unfold LatticeBcGhostTensorJacobi.borcherdsLeft
    rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
    · simp [LatticeBcGhostTensorJacobi.borcherdsLeftTerm, mu,
        SuperFieldProducts.integerBinomial, Ring.choose_natCast]
    · intro offset member
      by_contra outside
      have large : 1 < offset := by
        change offset ∉ ({0, 1} : Finset ℕ) at outside
        simp only [Finset.mem_insert, Finset.mem_singleton] at outside
        omega
      apply member
      have chooseZero : Ring.choose (1 : ℤ) offset = 0 := by
        simpa only [Nat.cast_one, Nat.choose_eq_zero_of_lt large, Nat.cast_zero]
          using (Ring.choose_natCast (R := ℤ) 1 offset)
      simp [LatticeBcGhostTensorJacobi.borcherdsLeftTerm,
        SuperFieldProducts.integerBinomial, chooseZero]
  have rightValue : LatticeBcGhostTensorJacobi.borcherdsRight firstParity secondParity D
      1 0 (-1) left right vector =
      mu D left 1 (mu D right (-1) vector) -
        SuperFieldProducts.koszul firstParity secondParity •
          mu D right (-1) (mu D left 1 vector) := by
    unfold LatticeBcGhostTensorJacobi.borcherdsRight
    rw [finsum_eq_single _ 0]
    · simp [LatticeBcGhostTensorJacobi.borcherdsRightTerm, mu,
        SuperFieldProducts.weight, SuperFieldProducts.integerBinomial,
        SuperFieldProducts.epsilon]
    · intro offset different
      simp [LatticeBcGhostTensorJacobi.borcherdsRightTerm, SuperFieldProducts.weight,
        SuperFieldProducts.integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [leftValue, rightValue] at law
  exact (eq_sub_iff_add_eq.mp law).symm.trans (by abel)

def bState : State D := LatticeAllStateField.vacuum D ⊗ₜ[ℂ]
  BcGhostFockSupport.b (-2) (BcGhostFockSupport.vacuum : BcGhostFockSupport.Fock ℂ)

theorem bState_odd : bState D ∈ LatticeBcGhostTensorStateField.homogeneous 1 := by
  apply LatticeBcGhostTensorStateField.tmul_mem
  have vacuumMember : (BcGhostFockSupport.vacuum : BcGhostFockSupport.Fock ℂ) ∈
      BcGhostSuperGenerators.homogeneous 0 :=
    BcGhostSuperGenerators.single_mem 0 ∅ 1 (by simp [BcGhostSuperGenerators.subsetParity])
  exact BcGhostSuperGenerators.currentMode_mem .b (-1) 0 _ vacuumMember

def defect (grade : ℕ) (left right : State D) : State D :=
  B D 0 (mu D left (-1) right) - mu D (B D 0 left) (-1) right -
    SuperFieldProducts.koszul 1 grade • mu D left (-1) (B D 0 right)

theorem defect_as_actual_b_mode (grade : ℕ) (left right : State D)
    (member : left ∈ LatticeBcGhostTensorStateField.homogeneous grade) :
    defect D grade left right = mu D (B D (-1) left) 0 right := by
  have law := one_mode_commutator D 1 grade (bState D) left right (bState_odd D) member
  simp only [mu, bState, LatticeBcGhostTensorStateField.b_generator] at law
  change B D 0 (mu D left (-1) right) =
    mu D (B D 0 left) (-1) right + SuperFieldProducts.koszul 1 grade •
      mu D left (-1) (B D 0 right) + mu D (B D (-1) left) 0 right at law
  unfold defect
  rw [law]
  abel

theorem actual_B0_second_order (firstParity secondParity : ℕ)
    (left right vector : State D)
    (firstMember : left ∈ LatticeBcGhostTensorStateField.homogeneous firstParity)
    (secondMember : right ∈ LatticeBcGhostTensorStateField.homogeneous secondParity) :
    defect D firstParity left (mu D right (-1) vector) =
      mu D (defect D firstParity left right) (-1) vector +
        SuperFieldProducts.koszul (firstParity + 1) secondParity •
          mu D right (-1) (defect D firstParity left vector) := by
  have oddMember : B D (-1) left ∈
      LatticeBcGhostTensorStateField.homogeneous (firstParity + 1) := by
    have member := LatticeBcGhostTensorStateField.stateField_mem 1 firstParity
      (bState D) left (bState_odd D) firstMember 0
    simpa only [bState, LatticeBcGhostTensorStateField.b_generator,
      show (0 - 1 : ℤ) = -1 by omega, Nat.add_comm] using member
  simp only [defect_as_actual_b_mode D firstParity left _ firstMember]
  exact zero_mode_derivation D (firstParity + 1) secondParity
    (B D (-1) left) right vector oddMember secondMember

include leftInverse rightInverse in
theorem zero_product (left right : State D)
    (firstZero : left ∈ OriginalBrstReassembly.zeroSpace D H)
    (secondZero : right ∈ OriginalBrstReassembly.zeroSpace D H) :
    mu D left (-1) right ∈ OriginalBrstReassembly.zeroSpace D H := by
  have covariance := LinearMap.congr_fun
    (LatticeBcGhostTotalConformal.energy_covariance D H leftInverse rightInverse left (-1)) right
  change (M D H 0 + G D 0) left = 0 at firstZero
  change (M D H 0 + G D 0) right = 0 at secondZero
  change (M D H 0 + G D 0) (mu D left (-1) right) = 0
  simpa [LatticeBcGhostTotalConformal.totalMode, Module.End.mul_apply,
    firstZero, secondZero, mu] using covariance

def absoluteCycleEquiv : OriginalBrstReassembly.cycles D H ⊤ ≃ₗ[ℂ] OriginalCycles D H where
  toFun state := ⟨state.val, state.property.2⟩
  invFun state := ⟨state.val, Submodule.mem_top, state.property⟩
  left_inv state := rfl
  right_inv state := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

theorem absoluteBoundary_transport :
    (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical ⊤
      (OriginalBrstReassembly.top_stable D H)).map (absoluteCycleEquiv D H).toLinearMap =
      OriginalBoundaries D H := by
  ext state
  constructor
  · rintro ⟨representative, member, rfl⟩
    obtain ⟨preimage, equation⟩ :=
      (OriginalBrstReassembly.boundary_iff D H leftInverse rightInverse critical ⊤
        (OriginalBrstReassembly.top_stable D H) representative).mp member
    exact ⟨preimage.val, equation⟩
  · rintro ⟨preimage, equation⟩
    refine ⟨(absoluteCycleEquiv D H).symm state, ?_, by simp⟩
    apply (OriginalBrstReassembly.boundary_iff D H leftInverse rightInverse critical ⊤
      (OriginalBrstReassembly.top_stable D H) _).mpr
    exact ⟨⟨preimage, Submodule.mem_top⟩, equation⟩

def absoluteOriginalEquiv :
    OriginalBrstReassembly.absoluteCohomology D H leftInverse rightInverse critical ≃ₗ[ℂ]
      OriginalCohomology D H :=
  Submodule.Quotient.equiv
    (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical ⊤
      (OriginalBrstReassembly.top_stable D H)) (OriginalBoundaries D H)
    (absoluteCycleEquiv D H) (absoluteBoundary_transport D H leftInverse rightInverse critical)

def originalZeroEquiv : OriginalCohomology D H ≃ₗ[ℂ]
    OriginalBrstReassembly.zeroCohomology D H leftInverse rightInverse critical :=
  (absoluteOriginalEquiv D H leftInverse rightInverse critical).symm.trans
    (OriginalBrstReassembly.zeroReductionEquiv D H leftInverse rightInverse critical)

def originalB0 : Module.End ℂ (OriginalCohomology D H) :=
  (originalZeroEquiv D H leftInverse rightInverse critical).symm.toLinearMap.comp
    ((zeroB0 D H leftInverse rightInverse critical).comp
      (originalZeroEquiv D H leftInverse rightInverse critical).toLinearMap)

theorem originalB0_square (state : OriginalCohomology D H) :
    originalB0 D H leftInverse rightInverse critical
      (originalB0 D H leftInverse rightInverse critical state) = 0 := by
  simp only [originalB0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, zeroB0_square, map_zero]

theorem originalZeroEquiv_symm_mk
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    (originalZeroEquiv D H leftInverse rightInverse critical).symm
      ((OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
        (OriginalBrstReassembly.zeroSpace D H)
        (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mkQ state) =
      (OriginalBoundaries D H).mkQ ⟨state.val, state.property.2⟩ := rfl

theorem originalB0_mk_zero
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    originalB0 D H leftInverse rightInverse critical
      ((OriginalBoundaries D H).mkQ ⟨state.val, state.property.2⟩) =
      (OriginalBoundaries D H).mkQ
        ⟨B D 0 state.val, B0_zeroCycle D H state.val state.property.1 state.property.2⟩ := by
  rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical state]
  simp only [originalB0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact originalZeroEquiv_symm_mk D H leftInverse rightInverse critical
    (zeroCycleB0 D H state)

def zeroCycleProduct
    (left right : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H) :=
  ⟨mu D left.val (-1) right.val,
    zero_product D H leftInverse rightInverse left.val right.val left.property.1 right.property.1,
    LatticeBcGhostCohomologyModes.mode_closed D H
      ⟨left.val, left.property.2⟩ ⟨right.val, right.property.2⟩ (-1)⟩

def originalClass
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    OriginalCohomology D H := (OriginalBoundaries D H).mkQ ⟨state.val, state.property.2⟩

theorem originalClass_product
    (left right : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    product D H (-1) (originalClass D H left) (originalClass D H right) =
      originalClass D H (zeroCycleProduct D H leftInverse rightInverse left right) := rfl

theorem originalClass_B0
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    originalB0 D H leftInverse rightInverse critical (originalClass D H state) =
      originalClass D H (zeroCycleB0 D H state) :=
  originalB0_mk_zero D H leftInverse rightInverse critical state

def zeroCycleDefect (grade : ℕ)
    (left right : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H) :=
  zeroCycleB0 D H (zeroCycleProduct D H leftInverse rightInverse left right) -
    zeroCycleProduct D H leftInverse rightInverse (zeroCycleB0 D H left) right -
      SuperFieldProducts.koszul 1 grade •
        zeroCycleProduct D H leftInverse rightInverse left (zeroCycleB0 D H right)

def quotientDefect (grade : ℕ) (left right : OriginalCohomology D H) : OriginalCohomology D H :=
  originalB0 D H leftInverse rightInverse critical (product D H (-1) left right) -
    product D H (-1) (originalB0 D H leftInverse rightInverse critical left) right -
      SuperFieldProducts.koszul 1 grade •
        product D H (-1) left (originalB0 D H leftInverse rightInverse critical right)

theorem quotientDefect_class (grade : ℕ)
    (left right : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    quotientDefect D H leftInverse rightInverse critical grade
      (originalClass D H left) (originalClass D H right) =
      originalClass D H (zeroCycleDefect D H leftInverse rightInverse grade left right) := by
  simp only [quotientDefect, originalClass_product D H leftInverse rightInverse,
    originalClass_B0 D H leftInverse rightInverse critical]
  change (OriginalBoundaries D H).mkQ _ - (OriginalBoundaries D H).mkQ _ -
    _ • (OriginalBoundaries D H).mkQ _ = (OriginalBoundaries D H).mkQ _
  rw [← map_sub, ← map_smul, ← map_sub]
  rfl

theorem quotient_B0_second_order_on_zero_representatives (firstParity secondParity : ℕ)
    (left right vector : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H))
    (firstMember : left.val ∈ LatticeBcGhostTensorStateField.homogeneous firstParity)
    (secondMember : right.val ∈ LatticeBcGhostTensorStateField.homogeneous secondParity) :
    quotientDefect D H leftInverse rightInverse critical firstParity (originalClass D H left)
      (product D H (-1) (originalClass D H right) (originalClass D H vector)) =
      product D H (-1)
        (quotientDefect D H leftInverse rightInverse critical firstParity
          (originalClass D H left) (originalClass D H right)) (originalClass D H vector) +
        SuperFieldProducts.koszul (firstParity + 1) secondParity •
          product D H (-1) (originalClass D H right)
            (quotientDefect D H leftInverse rightInverse critical firstParity
              (originalClass D H left) (originalClass D H vector)) := by
  simp only [originalClass_product D H leftInverse rightInverse,
    quotientDefect_class D H leftInverse rightInverse critical]
  change (OriginalBoundaries D H).mkQ _ = (OriginalBoundaries D H).mkQ _ +
    _ • (OriginalBoundaries D H).mkQ _
  rw [← map_smul, ← map_add]
  congr 1
  apply Subtype.ext
  exact actual_B0_second_order D firstParity secondParity left.val right.val vector.val
    firstMember secondMember

theorem energy_mem (grade : ℕ) (state : State D)
    (member : state ∈ LatticeBcGhostTensorStateField.homogeneous grade) :
    (M D H 0 + G D 0) state ∈ LatticeBcGhostTensorStateField.homogeneous grade := by
  have preserved := LatticeBcGhostTensorStateField.stateField_mem 0 grade
    (LatticeBcGhostTotalConformal.omega D H) state
    (LatticeBcGhostTotalConformal.omega_even D H) member 1
  rw [show (1 : ℤ) = 0 + 1 by omega,
    LatticeBcGhostTotalConformal.omega_modes] at preserved
  simpa only [zero_add, LatticeBcGhostTotalConformal.totalMode] using preserved

theorem energy_parity (grade : ℕ) (state : State D) :
    LatticeBcGhostTensorStateField.parityPart grade ((M D H 0 + G D 0) state) =
      (M D H 0 + G D 0) (LatticeBcGhostTensorStateField.parityPart grade state) := by
  have firstFixed := (LatticeBcGhostTensorStateField.homogeneous_fixed 0 _).mp
    (energy_mem D H 0 (LatticeBcGhostTensorStateField.parityPart 0 state)
      (LatticeBcGhostTensorStateField.parityPart_mem 0 state))
  have secondFixed := (LatticeBcGhostTensorStateField.homogeneous_fixed 1 _).mp
    (energy_mem D H 1 (LatticeBcGhostTensorStateField.parityPart 1 state)
      (LatticeBcGhostTensorStateField.parityPart_mem 1 state))
  have split := congrArg (fun vector => (M D H 0 + G D 0) vector)
    (LatticeBcGhostTensorStateField.parity_decomposition state)
  rw [map_add] at split
  rcases Nat.mod_two_eq_zero_or_one grade with even | odd
  · rw [LatticeBcGhostCohomologyModes.parityPart_periodic D grade 0 (by simpa using even),
      ← split, map_add, firstFixed]
    have vanished : LatticeBcGhostTensorStateField.parityPart 0
        ((M D H 0 + G D 0) (LatticeBcGhostTensorStateField.parityPart 1 state)) = 0 := by
      rw [← secondFixed]
      exact LatticeBcGhostTensorStateField.parityPart_orthogonal 0 1 (by decide) _
    rw [vanished, add_zero]
  · rw [LatticeBcGhostCohomologyModes.parityPart_periodic D grade 1 (by simpa using odd),
      ← split, map_add, secondFixed]
    have vanished : LatticeBcGhostTensorStateField.parityPart 1
        ((M D H 0 + G D 0) (LatticeBcGhostTensorStateField.parityPart 0 state)) = 0 := by
      rw [← firstFixed]
      exact LatticeBcGhostTensorStateField.parityPart_orthogonal 1 0 (by decide) _
    rw [vanished, zero_add]

def zeroCycleParity (grade : ℕ)
    (state : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H)) :
    OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H) :=
  ⟨LatticeBcGhostTensorStateField.parityPart grade state.val, by
    change (M D H 0 + G D 0) (LatticeBcGhostTensorStateField.parityPart grade state.val) = 0
    rw [← energy_parity D H, state.property.1, map_zero], by
    change Q D H (LatticeBcGhostTensorStateField.parityPart grade state.val) = 0
    rw [LatticeBcGhostCohomologyModes.Q_parityPart, state.property.2, map_zero]⟩

include leftInverse rightInverse critical in
theorem zero_homogeneous_representative (grade : ℕ) (state : OriginalCohomology D H)
    (fixed : parity D H grade state = state) :
    ∃ representative : OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H),
      representative.val ∈ LatticeBcGhostTensorStateField.homogeneous grade ∧
        originalClass D H representative = state := by
  obtain ⟨representative, equation⟩ :=
    (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mkQ_surjective
        (originalZeroEquiv D H leftInverse rightInverse critical state)
  have classEquation : originalClass D H representative = state := by
    unfold originalClass
    rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical, equation]
    exact (originalZeroEquiv D H leftInverse rightInverse critical).symm_apply_apply state
  refine ⟨zeroCycleParity D H grade representative,
    LatticeBcGhostTensorStateField.parityPart_mem grade representative.val, ?_⟩
  change (OriginalBoundaries D H).mkQ
    (LatticeBcGhostCohomologyModes.cycleParity D H grade
      ⟨representative.val, representative.property.2⟩) = state
  rw [← LatticeBcGhostCohomologyModes.parity_mk]
  exact (congrArg (parity D H grade) classEquation).trans fixed

theorem quotient_B0_second_order (firstParity secondParity : ℕ)
    (left right vector : OriginalCohomology D H)
    (firstFixed : parity D H firstParity left = left)
    (secondFixed : parity D H secondParity right = right) :
    quotientDefect D H leftInverse rightInverse critical firstParity left
      (product D H (-1) right vector) =
      product D H (-1)
        (quotientDefect D H leftInverse rightInverse critical firstParity left right) vector +
        SuperFieldProducts.koszul (firstParity + 1) secondParity •
          product D H (-1) right
            (quotientDefect D H leftInverse rightInverse critical firstParity left vector) := by
  obtain ⟨firstState, firstMember, rfl⟩ :=
    zero_homogeneous_representative D H leftInverse rightInverse critical firstParity left firstFixed
  obtain ⟨secondState, secondMember, rfl⟩ :=
    zero_homogeneous_representative D H leftInverse rightInverse critical secondParity right secondFixed
  obtain ⟨thirdState, equation⟩ :=
    (OriginalBrstReassembly.boundaries D H leftInverse rightInverse critical
      (OriginalBrstReassembly.zeroSpace D H)
      (OriginalBrstReassembly.zero_stable D H leftInverse rightInverse)).mkQ_surjective
        (originalZeroEquiv D H leftInverse rightInverse critical vector)
  have classEquation : originalClass D H thirdState = vector := by
    unfold originalClass
    rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical, equation]
    exact (originalZeroEquiv D H leftInverse rightInverse critical).symm_apply_apply vector
  rw [← classEquation]
  exact quotient_B0_second_order_on_zero_representatives D H leftInverse rightInverse critical
    firstParity secondParity firstState secondState thirdState firstMember secondMember

theorem originalB0_odd (grade : ℕ) (state : OriginalCohomology D H)
    (fixed : parity D H grade state = state) :
    parity D H (grade + 1) (originalB0 D H leftInverse rightInverse critical state) =
      originalB0 D H leftInverse rightInverse critical state := by
  obtain ⟨representative, member, rfl⟩ :=
    zero_homogeneous_representative D H leftInverse rightInverse critical grade state fixed
  rw [originalClass_B0]
  have oddMember : B D 0 representative.val ∈
      LatticeBcGhostTensorStateField.homogeneous (grade + 1) := by
    have preserved := LatticeBcGhostTensorStateField.stateField_mem 1 grade
      (bState D) representative.val (bState_odd D) member 1
    simpa only [bState, LatticeBcGhostTensorStateField.b_generator,
      show (1 - 1 : ℤ) = 0 by omega, Nat.add_comm] using preserved
  unfold originalClass
  rw [LatticeBcGhostCohomologyModes.parity_mk]
  congr 1
  apply Subtype.ext
  exact (LatticeBcGhostTensorStateField.homogeneous_fixed (grade + 1) _).mp oddMember

theorem originalB0_vacuum :
    originalB0 D H leftInverse rightInverse critical (vacuum D H) = 0 := by
  let representative :
      OriginalBrstReassembly.cycles D H (OriginalBrstReassembly.zeroSpace D H) :=
    ⟨LatticeBcGhostTensorStateField.vacuum D,
      LatticeBcGhostTotalConformal.vacuum_annihilation D H 0 (by decide),
      LatticeBcGhostBrstCurrent.Q_vacuum D H⟩
  change originalB0 D H leftInverse rightInverse critical
    (originalClass D H representative) = 0
  rw [originalClass_B0]
  have vanished : B D 0 (LatticeBcGhostTensorStateField.vacuum D) = 0 := by
    have creativity := LatticeBcGhostTensorStateField.stateField_creativity D (bState D) 1
      (by decide)
    simpa only [bState, LatticeBcGhostTensorStateField.b_generator,
      show (1 - 1 : ℤ) = 0 by omega] using creativity
  have zero : zeroCycleB0 D H representative = 0 := Subtype.ext vanished
  rw [zero]
  exact map_zero (OriginalBoundaries D H).mkQ

example (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (critical : D.rank = 26) :
    (OriginalBoundaries D H).mkQ
      ⟨LatticeBcGhostTotalConformal.omega D H,
        (LatticeBcGhostStressBoundary.critical_cycle_preservation D H
          leftInverse rightInverse critical).1⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (LatticeBcGhostStressBoundary.omega_boundary D H).2

example (state : OriginalCohomology D H) :
    product D H (-1) (vacuum D H) state = state ∧
      product D H (-1) state (vacuum D H) = state := by
  exact ⟨by simpa using LatticeBcGhostCohomologyFields.vacuum_product D H state (-1),
    LatticeBcGhostCohomologyFields.creation D H state⟩

#print axioms quotient_B0_second_order
#print axioms actual_B0_second_order
#print axioms originalB0
#print axioms originalB0_square
#print axioms originalB0_odd
#print axioms originalB0_vacuum
#print axioms product_associative
#print axioms product_supercommutative

end D5.S3.VertexAlgebra.TensorConformal.OriginalTopologicalApplications
