/- GID: D5/S3/VertexAlgebra/LatticeBcGhostTensorLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostTensorLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed locality of the actual even-matter tensor bc state-field on all homogeneous and mixed states. -/

import D5.S3.VertexAlgebra.LatticeBcGhostTensorStateField
import D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality
import D5.S3.VertexAlgebra.LatticeAllStateLocality
import D5.S3.VertexAlgebra.BcGhostSuperLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostTensorLocality

open D5.S3.VertexAlgebra
open D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateLocality
open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField
open VertexOperatorTensorProduct
open VertexOperatorTensorProductLocality
open LatticeBcGhostTensorStateField
open SuperFieldProducts
open scoped TensorProduct VertexOperator

abbrev State (D : LatticeData) := LatticeBcGhostTensorStateField.State D

variable {D : LatticeData}

def tensorSuperLocal (leftParity rightParity : ℕ) (left right : VertexOperator ℂ (State D)) : Prop :=
  ∃ order : ℕ, SignedLocal left right (koszul leftParity rightParity) order

theorem tensorSuperLocal_zero_left (leftParity rightParity : ℕ)
    (right : VertexOperator ℂ (State D)) : tensorSuperLocal leftParity rightParity 0 right := by
  refine ⟨0, ?_⟩
  intro vector
  funext first second
  simp [ordered, reversed]

theorem tensorSuperLocal_zero_right (leftParity rightParity : ℕ)
    (left : VertexOperator ℂ (State D)) : tensorSuperLocal leftParity rightParity left 0 := by
  refine ⟨0, ?_⟩
  intro vector
  funext first second
  simp [ordered, reversed]

theorem signedLocal_mono (left right : VertexOperator ℂ (State D)) (sign : ℂ)
    (small large : ℕ) (le : small ≤ large)
    (killed : SignedLocal left right sign small) : SignedLocal left right sign large := by
  obtain ⟨extra, hlarge⟩ := Nat.exists_eq_add_of_le le
  intro vector
  rw [hlarge, show small + extra = extra + small by omega, pow_add,
    Module.End.mul_apply]
  have h := killed vector
  rw [h, map_zero]

theorem signedLocal_add_left (leftParity rightParity : ℕ)
    (first second third : VertexOperator ℂ (State D))
    (firstLocal : tensorSuperLocal leftParity rightParity first third)
    (secondLocal : tensorSuperLocal leftParity rightParity second third) :
    tensorSuperLocal leftParity rightParity (first + second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  let order := max firstOrder secondOrder
  refine ⟨order, ?_⟩
  have firstRaised := signedLocal_mono first third (koszul leftParity rightParity)
    firstOrder order (le_max_left _ _) firstKilled
  have secondRaised := signedLocal_mono second third (koszul leftParity rightParity)
    secondOrder order (le_max_right _ _) secondKilled
  intro vector
  have split : ordered (first + second) third vector -
      koszul leftParity rightParity • reversed (first + second) third vector =
      (ordered first third vector - koszul leftParity rightParity • reversed first third vector) +
      (ordered second third vector - koszul leftParity rightParity • reversed second third vector) := by
    funext leftIndex rightIndex
    simp [ordered, reversed, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    abel
  rw [split, map_add]
  simp only [firstRaised vector, secondRaised vector, add_zero]

theorem signedLocal_add_right (leftParity rightParity : ℕ)
    (first second third : VertexOperator ℂ (State D))
    (firstLocal : tensorSuperLocal leftParity rightParity first third)
    (secondLocal : tensorSuperLocal leftParity rightParity first second) :
    tensorSuperLocal leftParity rightParity first (second + third) := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  let order := max firstOrder secondOrder
  refine ⟨order, ?_⟩
  have firstRaised := signedLocal_mono first second (koszul leftParity rightParity)
    secondOrder order (le_max_right _ _) secondKilled
  have secondRaised := signedLocal_mono first third (koszul leftParity rightParity)
    firstOrder order (le_max_left _ _) firstKilled
  intro vector
  have split : ordered first (second + third) vector -
      koszul leftParity rightParity • reversed first (second + third) vector =
      (ordered first second vector - koszul leftParity rightParity • reversed first second vector) +
      (ordered first third vector - koszul leftParity rightParity • reversed first third vector) := by
    funext leftIndex rightIndex
    simp [ordered, reversed, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    abel
  rw [split, map_add]
  simp only [firstRaised vector, secondRaised vector, add_zero]

theorem delta_eval_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    (distribution : ℤ → ℤ → Module.End ℂ V)
    (order : ℕ) (vector : V) :
    (D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality.delta ^ order)
        (fun first second => distribution first second vector) =
      fun first second =>
        (FieldNormalProductLocality.deltaEnd ^ order) distribution first second vector := by
  induction order with
  | zero => rfl
  | succ order inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality.delta
        ((D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality.delta ^ order)
          (fun first second => distribution first second vector)) = _
      rw [inductionHypothesis]
      funext first second
      rfl

theorem signedLocal_of_killed {V : Type*} [AddCommGroup V] [Module ℂ V]
    (left right : VertexOperator ℂ V) (sign : ℂ) (order : ℕ)
    (killed : (FieldNormalProductLocality.deltaEnd ^ order)
      (SuperFieldProducts.superCommutator sign left right) = 0) :
    SignedLocal left right sign order := by
  intro vector
  have initial : ordered left right vector - sign • reversed left right vector =
      fun first second => SuperFieldProducts.superCommutator sign left right first second vector := by
    rfl
  rw [initial, delta_eval_pow, killed]
  rfl

theorem signedLocal_killed {V : Type*} [AddCommGroup V] [Module ℂ V]
    (left right : VertexOperator ℂ V) (sign : ℂ) (order : ℕ)
    (killed : SignedLocal left right sign order) :
    (FieldNormalProductLocality.deltaEnd ^ order)
      (SuperFieldProducts.superCommutator sign left right) = 0 := by
  funext first second
  apply LinearMap.ext
  intro vector
  have initial : ordered left right vector - sign • reversed left right vector =
      fun first second => SuperFieldProducts.superCommutator sign left right first second vector := by
    rfl
  have h := killed vector
  rw [initial, delta_eval_pow] at h
  exact congrFun (congrFun h first) second

theorem super_delta_iterate_eq_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    (distribution : ℤ → ℤ → Module.End ℂ V) (order : ℕ) :
    SuperFieldProducts.delta^[order] distribution =
      (FieldNormalProductLocality.deltaEnd ^ order) distribution := by
  change FieldNormalProductLocality.delta^[order] distribution = _
  exact SuperFieldLocality.delta_iterate_eq_pow distribution order

theorem super_delta_eq_field_delta {V : Type*} [AddCommGroup V]
    (distribution : ℤ → ℤ → V) (order : ℕ) :
    SuperFieldProducts.delta^[order] distribution =
      FieldNormalProductLocality.delta^[order] distribution := by
  induction order with
  | zero => rfl
  | succ order inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      have delta_eq : SuperFieldProducts.delta
          (FieldNormalProductLocality.delta^[order] distribution) =
          FieldNormalProductLocality.delta
            (FieldNormalProductLocality.delta^[order] distribution) := by
        funext first second
        rfl
      rw [delta_eq, Function.iterate_succ_apply']

theorem matter_signedLocal (D : LatticeData) (left right : Carrier D) :
    ∃ order : ℕ, SignedLocal (LatticeAllStateField.Y D left)
      (LatticeAllStateField.Y D right) 1 order := by
  obtain ⟨order, killed⟩ := LatticeAllStateLocality.stateField_locality D left right
  refine ⟨order, signedLocal_of_killed _ _ 1 order ?_⟩
  rw [← super_delta_iterate_eq_pow]
  rw [super_delta_eq_field_delta]
  have comm_eq : SuperFieldProducts.superCommutator 1
      (LatticeAllStateField.Y D left) (LatticeAllStateField.Y D right) =
      FieldNormalProductLocality.commutator (LatticeAllStateField.Y D left)
        (LatticeAllStateField.Y D right) := by
    funext first second
    simp [SuperFieldProducts.superCommutator, FieldNormalProductLocality.commutator]
  rw [comm_eq]
  exact killed

theorem ghost_signedLocal (leftParity rightParity : ℕ) (left right : Fock ℂ)
    (leftMember : left ∈ BcGhostSuperGenerators.homogeneous leftParity)
    (rightMember : right ∈ BcGhostSuperGenerators.homogeneous rightParity) :
    ∃ order : ℕ, SignedLocal (BcGhostSuperStateField.Y left)
      (BcGhostSuperStateField.Y right) (koszul leftParity rightParity) order := by
  obtain ⟨order, killed⟩ := BcGhostSuperLocality.stateField_superLocal leftParity rightParity
    left right leftMember rightMember
  refine ⟨order, signedLocal_of_killed _ _ _ order ?_⟩
  rw [Module.End.pow_apply]
  exact killed

theorem pure_tensor_superLocal (leftParity rightParity : ℕ)
    (leftMatter rightMatter : Carrier D) (leftGhost rightGhost : Fock ℂ)
    (leftMember : leftGhost ∈ BcGhostSuperGenerators.homogeneous leftParity)
    (rightMember : rightGhost ∈ BcGhostSuperGenerators.homogeneous rightParity) :
    tensorSuperLocal leftParity rightParity
      (stateField D (leftMatter ⊗ₜ[ℂ] leftGhost))
      (stateField D (rightMatter ⊗ₜ[ℂ] rightGhost)) := by
  obtain ⟨matterOrder, matterKilled⟩ := matter_signedLocal D leftMatter rightMatter
  obtain ⟨ghostOrder, ghostKilled⟩ := ghost_signedLocal leftParity rightParity leftGhost rightGhost
    leftMember rightMember
  refine ⟨matterOrder + ghostOrder, ?_⟩
  rw [LatticeBcGhostTensorStateField.stateField_tmul,
    LatticeBcGhostTensorStateField.stateField_tmul]
  simpa [one_mul] using signedLocal_tensor (LatticeAllStateField.Y D leftMatter)
    (LatticeAllStateField.Y D rightMatter)
    (BcGhostSuperStateField.Y leftGhost) (BcGhostSuperStateField.Y rightGhost)
    1 (koszul leftParity rightParity) matterOrder ghostOrder matterKilled ghostKilled

theorem homogeneous_superLocal (D : LatticeData) (leftParity rightParity : ℕ)
    (left right : State D)
    (leftMember : left ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightMember : right ∈ LatticeBcGhostTensorStateField.homogeneous rightParity) :
    tensorSuperLocal leftParity rightParity
      (stateField D left) (stateField D right) := by
  refine LatticeBcGhostTensorStateField.homogeneous_induction leftParity
    (fun left => tensorSuperLocal leftParity rightParity
      (stateField D left) (stateField D right)) ?_ ?_ ?_ left leftMember
  · simpa only [map_zero] using tensorSuperLocal_zero_left leftParity rightParity (stateField D right)
  · intro matter ghost ghostMember
    refine LatticeBcGhostTensorStateField.homogeneous_induction rightParity
      (fun right => tensorSuperLocal leftParity rightParity
        (stateField D (matter ⊗ₜ[ℂ] ghost)) (stateField D right)) ?_ ?_ ?_ right rightMember
    · simpa only [map_zero] using
        tensorSuperLocal_zero_right leftParity rightParity (stateField D (matter ⊗ₜ[ℂ] ghost))
    · intro inputMatter inputGhost inputMember
      exact pure_tensor_superLocal leftParity rightParity matter inputMatter
        ghost inputGhost ghostMember inputMember
    · intro first second firstIH secondIH
      rw [map_add]
      exact signedLocal_add_right leftParity rightParity _ _ _ secondIH firstIH
  · intro first second firstIH secondIH
    rw [map_add]
    exact signedLocal_add_left leftParity rightParity _ _ _ firstIH secondIH

theorem homogeneous_superFieldLocal (D : LatticeData) (leftParity rightParity : ℕ)
    (left right : State D)
    (leftMember : left ∈ LatticeBcGhostTensorStateField.homogeneous leftParity)
    (rightMember : right ∈ LatticeBcGhostTensorStateField.homogeneous rightParity) :
    SuperFieldProducts.SuperLocal leftParity rightParity
      (stateField D left) (stateField D right) := by
  obtain ⟨order, killed⟩ := homogeneous_superLocal D leftParity rightParity left right
    leftMember rightMember
  refine ⟨order, ?_⟩
  rw [super_delta_iterate_eq_pow]
  exact signedLocal_killed _ _ _ order killed

def mixedSuperCommutator (left right : State D) : ℤ → ℤ → Module.End ℂ (State D) :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    SuperFieldProducts.superCommutator (koszul leftParity rightParity)
      (stateField D (LatticeBcGhostTensorStateField.parityPart leftParity left))
      (stateField D (LatticeBcGhostTensorStateField.parityPart rightParity right))

theorem mixed_locality (D : LatticeData) (left right : State D) :
    ∃ order : ℕ, SuperFieldProducts.delta^[order] (mixedSuperCommutator left right) = 0 := by
  classical
  have component (leftParity rightParity : ℕ) :=
    homogeneous_superLocal D leftParity rightParity
      (LatticeBcGhostTensorStateField.parityPart leftParity left)
      (LatticeBcGhostTensorStateField.parityPart rightParity right)
      (LatticeBcGhostTensorStateField.parityPart_mem leftParity left)
      (LatticeBcGhostTensorStateField.parityPart_mem rightParity right)
  let orders (leftParity rightParity : ℕ) := Classical.choose (component leftParity rightParity)
  let common := ∑ leftParity ∈ Finset.range 2,
    ∑ rightParity ∈ Finset.range 2, orders leftParity rightParity
  refine ⟨common, ?_⟩
  rw [super_delta_iterate_eq_pow]
  rw [mixedSuperCommutator, map_sum]
  apply Finset.sum_eq_zero
  intro leftParity leftParityMember
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro rightParity rightParityMember
  apply signedLocal_killed
  apply signedLocal_mono _ _ _ (orders leftParity rightParity) common
  · have row : orders leftParity rightParity ≤
        ∑ index ∈ Finset.range 2, orders leftParity index :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) rightParityMember
    have outer : (∑ index ∈ Finset.range 2, orders leftParity index) ≤ common := by
      dsimp [common]
      exact Finset.single_le_sum
        (fun index _ => Nat.zero_le (∑ j ∈ Finset.range 2, orders index j))
        leftParityMember
    exact row.trans outer
  · exact Classical.choose_spec (component leftParity rightParity)

end D5.S3.VertexAlgebra.LatticeBcGhostTensorLocality
