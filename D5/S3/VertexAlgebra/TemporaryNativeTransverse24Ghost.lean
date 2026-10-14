import D5.S3.VertexAlgebra.TemporaryNativeTransverse24Kernel

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24

open Module LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (beta : Charge D) (frame : OriginalAdaptedFrameData D beta)

theorem B0_lower (polynomial : Polynomial) : B D 0 (lane D beta frame false polynomial) = 0 := by
  rw [lane_tensor]
  simp [B, original_b_zero_down_up.1]

theorem B0_upper (polynomial : Polynomial) :
    B D 0 (lane D beta frame true polynomial) = lane D beta frame false polynomial := by
  rw [lane_tensor, lane_tensor]
  simp [B, original_b_zero_down_up.2]

theorem J0_lane (upper : Bool) (polynomial : Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (lane D beta frame upper polynomial) =
      (if upper then 2 else 1 : ℂ) • lane D beta frame upper polynomial := by
  rw [lane_eq_physical]
  change LatticeBcGhostBrstGhostNumber.J D
    (Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ] downWord (epsilonSites upper) down) = _
  simp only [LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul, LinearMap.id_apply, polarized_J,
    TensorProduct.tmul_smul]
  cases upper <;> norm_num [epsilonSites, epsilonCount, etaCount, thetaCount, physicalLane,
    Finset.filter_singleton]

theorem B0_realize (pair : Polynomial × Polynomial) :
    B D 0 (realize D beta frame pair) = realize D beta frame (pair.2, 0) := by
  simp [realize, map_add, B0_lower, B0_upper]

theorem J0_realize (pair : Polynomial × Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair) =
      realize D beta frame (pair.1, (2 : ℂ) • pair.2) := by
  simp [realize, map_add, J0_lane, map_smul]

theorem B0_preserves (state : State D) (member : state ∈ fixedReduced D beta frame) :
    B D 0 state ∈ fixedReduced D beta frame := by
  rw [← realize_extract D beta frame state member, B0_realize]
  exact realize_mem D beta frame _

theorem J0_preserves (state : State D) (member : state ∈ fixedReduced D beta frame) :
    LatticeBcGhostBrstGhostNumber.J D state ∈ fixedReduced D beta frame := by
  rw [← realize_extract D beta frame state member, J0_realize]
  exact realize_mem D beta frame _

def reducedB0 : Module.End ℂ (fixedReduced D beta frame) :=
  ((B D 0).comp (fixedReduced D beta frame).subtype).codRestrict (fixedReduced D beta frame)
    (fun state => B0_preserves D beta frame state state.property)

def reducedJ0 : Module.End ℂ (fixedReduced D beta frame) :=
  ((LatticeBcGhostBrstGhostNumber.J D).comp (fixedReduced D beta frame).subtype).codRestrict
    (fixedReduced D beta frame) (fun state => J0_preserves D beta frame state state.property)

theorem B0_transport (pair : Polynomial × Polynomial) :
    (reducedEquiv D beta frame).symm (reducedB0 D beta frame (reducedEquiv D beta frame pair)) =
      (pair.2, 0) := by
  change extract D beta frame (B D 0 (realize D beta frame pair)) = _
  rw [B0_realize, extract_realize]

theorem J0_transport (pair : Polynomial × Polynomial) :
    (reducedEquiv D beta frame).symm (reducedJ0 D beta frame (reducedEquiv D beta frame pair)) =
      (pair.1, (2 : ℂ) • pair.2) := by
  change extract D beta frame (LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair)) = _
  rw [J0_realize, extract_realize]

theorem B0_realize_zero_iff (pair : Polynomial × Polynomial) :
    B D 0 (realize D beta frame pair) = 0 ↔ pair.2 = 0 := by
  rw [B0_realize]
  constructor
  · intro killed
    have equality : realize D beta frame (pair.2, 0) = realize D beta frame (0, 0) := by
      have zeroImage : realize D beta frame (0, 0) = 0 := map_zero _
      exact killed.trans zeroImage.symm
    exact congrArg Prod.fst (realize_injective D beta frame equality)
  · intro zero
    simp [zero, realize]

def fixedRelative : Submodule ℂ (State D) :=
  fixedReduced D beta frame ⊓ LinearMap.ker (B D 0)

theorem fixedRelative_mem (state : State D) :
    state ∈ fixedRelative D beta frame ↔ state ∈ fixedReduced D beta frame ∧
      readLane D beta frame true state = 0 := by
  constructor
  · rintro ⟨member, killed⟩
    refine ⟨member, ?_⟩
    have zero := (B0_realize_zero_iff D beta frame (extract D beta frame state)).mp
      (by simpa only [realize_extract D beta frame state member] using (LinearMap.mem_ker.mp killed))
    exact zero
  · rintro ⟨member, upperZero⟩
    refine ⟨member, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [← realize_extract D beta frame state member]
    exact (B0_realize_zero_iff D beta frame _).mpr upperZero

theorem lower_relative (polynomial : Polynomial) :
    lane D beta frame false polynomial ∈ fixedRelative D beta frame := by
  exact ⟨lane_mem D beta frame false polynomial, B0_lower D beta frame polynomial⟩

def relativeRealize : Polynomial →ₗ[ℂ] fixedRelative D beta frame :=
  (lane D beta frame false).codRestrict (fixedRelative D beta frame) (lower_relative D beta frame)

def relativeEquiv : Polynomial ≃ₗ[ℂ] fixedRelative D beta frame where
  toLinearMap := relativeRealize D beta frame
  invFun state := readLane D beta frame false state
  left_inv polynomial := by
    change readLane D beta frame false (lane D beta frame false polynomial) = polynomial
    simpa using readLane_lane D beta frame false false polynomial
  right_inv state := by
    apply Subtype.ext
    obtain ⟨member, upperZero⟩ := (fixedRelative_mem D beta frame state).mp state.property
    have recovered := realize_extract D beta frame state member
    change lane D beta frame false (readLane D beta frame false state) = (state : State D)
    change lane D beta frame false (readLane D beta frame false state) +
      lane D beta frame true (readLane D beta frame true state) = (state : State D) at recovered
    rw [upperZero, map_zero, add_zero] at recovered
    exact recovered

theorem relativeEquiv_apply (polynomial : Polynomial) :
    (relativeEquiv D beta frame polynomial : State D) = lane D beta frame false polynomial := rfl

theorem relativeEquiv_symm (state : fixedRelative D beta frame) :
    (relativeEquiv D beta frame).symm state = readLane D beta frame false state := rfl

theorem J0_realize_eigen_iff (degree : ℂ) (pair : Polynomial × Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair) = degree • realize D beta frame pair ↔
      pair.1 = degree • pair.1 ∧ (2 : ℂ) • pair.2 = degree • pair.2 := by
  rw [J0_realize, ← map_smul]
  constructor
  · intro equality
    have coordinates := realize_injective D beta frame equality
    exact ⟨congrArg Prod.fst coordinates, congrArg Prod.snd coordinates⟩
  · rintro ⟨lowerEquality, upperEquality⟩
    apply congrArg (realize D beta frame)
    exact Prod.ext lowerEquality upperEquality

theorem J0_degree_one_iff (pair : Polynomial × Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair) = realize D beta frame pair ↔
      pair.2 = 0 := by
  have criterion := J0_realize_eigen_iff D beta frame 1 pair
  simp only [one_smul] at criterion
  rw [criterion]
  simp only [one_smul, true_and]
  constructor
  · intro equality
    have vanished : (1 : ℂ) • pair.2 = 0 := by
      calc
        _ = ((2 : ℂ) - 1) • pair.2 := by norm_num
        _ = (2 : ℂ) • pair.2 - pair.2 := by rw [sub_smul, one_smul]
        _ = 0 := sub_eq_zero.mpr equality
    simpa using vanished
  · intro zero
    simp [zero]

theorem J0_degree_two_iff (pair : Polynomial × Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair) = (2 : ℂ) • realize D beta frame pair ↔
      pair.1 = 0 := by
  rw [J0_realize_eigen_iff]
  simp only [and_true]
  constructor
  · intro equality
    have vanished : (1 : ℂ) • pair.1 = 0 := by
      calc
        _ = ((2 : ℂ) - 1) • pair.1 := by norm_num
        _ = (2 : ℂ) • pair.1 - pair.1 := by rw [sub_smul, one_smul]
        _ = 0 := sub_eq_zero.mpr equality.symm
    simpa using vanished
  · intro zero
    simp [zero]

theorem J0_other_degree_vanishes (degree : ℂ) (notOne : degree ≠ 1) (notTwo : degree ≠ 2)
    (pair : Polynomial × Polynomial)
    (homogeneous : LatticeBcGhostBrstGhostNumber.J D (realize D beta frame pair) =
      degree • realize D beta frame pair) : pair = 0 := by
  obtain ⟨lowerEquality, upperEquality⟩ := (J0_realize_eigen_iff D beta frame degree pair).mp homogeneous
  have lowerZero : (degree - 1) • pair.1 = 0 := by
    rw [sub_smul, one_smul, ← lowerEquality, sub_self]
  have upperZero : (degree - 2) • pair.2 = 0 := by
    rw [sub_smul, ← upperEquality, sub_self]
  exact Prod.ext ((smul_eq_zero.mp lowerZero).resolve_left (sub_ne_zero.mpr notOne))
    ((smul_eq_zero.mp upperZero).resolve_left (sub_ne_zero.mpr notTwo))

theorem relative_absolute_degree_one (state : fixedRelative D beta frame) :
    LatticeBcGhostBrstGhostNumber.J D (state : State D) = state := by
  obtain ⟨polynomial, equality⟩ := (relativeEquiv D beta frame).surjective state
  rw [← equality, relativeEquiv_apply]
  simpa using J0_lane D beta frame false polynomial

theorem epsilon_upper_absolute_degree_two (polynomial : Polynomial) :
    LatticeBcGhostBrstGhostNumber.J D (lane D beta frame true polynomial) =
      (2 : ℂ) • lane D beta frame true polynomial := by
  simpa using J0_lane D beta frame true polynomial

theorem realize_original_ghost_signs (pair : Polynomial × Polynomial) :
    realize D beta frame pair =
      Finsupp.single beta (matterEmbedding D beta frame pair.1) ⊗ₜ[ℂ] Finsupp.single {1} (1 : ℂ) -
      Finsupp.single beta (matterEmbedding D beta frame pair.2) ⊗ₜ[ℂ] Finsupp.single {1, 3} (1 : ℂ) := by
  simp [realize, lane_tensor, down_original_basis, up_original_basis, sub_eq_add_neg,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24
