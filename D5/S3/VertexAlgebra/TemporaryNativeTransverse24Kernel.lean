import D5.S3.VertexAlgebra.TemporaryNativeTransverse24Coordinates

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24

open Module LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (beta : Charge D) (frame : OriginalAdaptedFrameData D beta)

def actualK : Module.End ℂ (State D) :=
  K D (frame.frame frame.xAxis) (frame.frame frame.yAxis) (by simpa using frame.xDual frame.xAxis)

theorem actualK_original : actualK D beta frame =
    K D frame.nullDirection (adaptedPartner D beta frame.nullDirection)
      (adaptedPartner_relations D beta frame.nullDirection frame.nullSelf frame.coefficientNonzero).1 := by
  simp only [actualK, frame.xRow, frame.yRow]

def originalFixedReduced : Submodule ℂ (State D) :=
  LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.ker
    (K D frame.nullDirection (adaptedPartner D beta frame.nullDirection)
      (adaptedPartner_relations D beta frame.nullDirection frame.nullSelf frame.coefficientNonzero).1)

def actualP : Module.End ℂ (State D) :=
  OriginalQQuartetSource.P D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse
    frame.xAxis frame.yAxis

def fixedReduced : Submodule ℂ (State D) :=
  LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.ker (actualK D beta frame)

theorem fixedReduced_mem (state : State D) :
    state ∈ fixedReduced D beta frame ↔
      chargeProjection D beta state = state ∧ actualK D beta frame state = 0 := by
  simp only [fixedReduced, Submodule.mem_inf, chargeEmbedding_range_iff, LinearMap.mem_ker]

theorem fixedReduced_eq_fixed_P_range : fixedReduced D beta frame =
    LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.range (actualP D beta frame) := by
  rw [fixedReduced, actualK, actualP,
    original_K_kernel_eq_P_range D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse
      frame.xAxis frame.yAxis frame.xDual frame.yDual]

theorem actualK_nativeWord (index : NativeIndex D) :
    actualK D beta frame (nativeWord D frame.frame beta index) =
      (kappa D frame.xAxis frame.yAxis index.1 index.2 : ℂ) • nativeWord D frame.frame beta index := by
  exact original_K_all_frequency_count D frame.frame frame.xAxis frame.yAxis frame.xDual frame.yDual
    beta index.1 1 index.2

theorem actualK_coefficients (state : State D) (sector : chargeProjection D beta state = state)
    (index : NativeIndex D) :
    nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta
      (actualK D beta frame state) index =
      (kappa D frame.xAxis frame.yAxis index.1 index.2 : ℂ) *
        nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta
          state index := by
  classical
  let coefficients := nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse
    beta state
  have expansion : state = ∑ key ∈ coefficients.support,
      coefficients key • nativeWord D frame.frame beta key :=
    (native_sector_finite_expansion D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse
      beta state sector).symm
  have image : actualK D beta frame state = ∑ key ∈ coefficients.support,
      (coefficients key * (kappa D frame.xAxis frame.yAxis key.1 key.2 : ℂ)) •
        nativeWord D frame.frame beta key := by
    rw [expansion]
    simp only [map_sum, map_smul, actualK_nativeWord, smul_smul]
  rw [image, nativeCoefficient_sum]
  by_cases member : index ∈ coefficients.support
  · simp [member, coefficients, mul_comm]
  · have vanished : coefficients index = 0 := Finsupp.notMem_support_iff.mp member
    simp only [if_neg member]
    change 0 = _ * coefficients index
    rw [vanished, mul_zero]

theorem kernel_coefficients_vanish (state : State D) (member : state ∈ fixedReduced D beta frame)
    (index : NativeIndex D) (nonzero : kappa D frame.xAxis frame.yAxis index.1 index.2 ≠ 0) :
    nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta
      state index = 0 := by
  obtain ⟨sector, killed⟩ := (fixedReduced_mem D beta frame state).mp member
  have equality := actualK_coefficients D beta frame state sector index
  rw [killed, map_zero, Finsupp.zero_apply] at equality
  have castNonzero : (kappa D frame.xAxis frame.yAxis index.1 index.2 : ℂ) ≠ 0 := by
    exact_mod_cast nonzero
  exact (mul_eq_zero.mp equality.symm).resolve_left castNonzero

theorem fixedReduced_iff_coefficients (state : State D) :
    state ∈ fixedReduced D beta frame ↔ chargeProjection D beta state = state ∧
      ∀ index : NativeIndex D, kappa D frame.xAxis frame.yAxis index.1 index.2 ≠ 0 →
        nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta
          state index = 0 := by
  classical
  constructor
  · intro member
    exact ⟨((fixedReduced_mem D beta frame state).mp member).1,
      kernel_coefficients_vanish D beta frame state member⟩
  · rintro ⟨sector, supported⟩
    apply (fixedReduced_mem D beta frame state).mpr
    refine ⟨sector, ?_⟩
    rw [← native_sector_finite_expansion D frame.frame frame.inverse frame.leftFrameInverse
      frame.rightFrameInverse beta state sector]
    simp only [map_sum, map_smul, actualK_nativeWord]
    apply Finset.sum_eq_zero
    intro index member
    by_cases zero : kappa D frame.xAxis frame.yAxis index.1 index.2 = 0
    · simp [zero]
    · simp [supported index zero]

theorem lane_monomial_mem (upper : Bool) (powers : Exponent) :
    nativeWord D frame.frame beta (laneIndex D beta frame upper powers) ∈ fixedReduced D beta frame := by
  apply (fixedReduced_mem D beta frame _).mpr
  refine ⟨nativeWord_sector D frame.frame beta _, ?_⟩
  rw [actualK_nativeWord, laneIndex_zero_occupation]
  simp

theorem lane_mem (upper : Bool) (polynomial : Polynomial) :
    lane D beta frame upper polynomial ∈ fixedReduced D beta frame := by
  have contained : LinearMap.range (lane D beta frame upper) ≤ fixedReduced D beta frame := by
    rw [lane, Module.Basis.constr_range]
    apply Submodule.span_le.mpr
    rintro state ⟨powers, rfl⟩
    exact lane_monomial_mem D beta frame upper powers
  exact contained ⟨polynomial, rfl⟩

theorem realize_mem (pair : Polynomial × Polynomial) :
    realize D beta frame pair ∈ fixedReduced D beta frame := by
  exact Submodule.add_mem _ (lane_mem D beta frame false pair.1) (lane_mem D beta frame true pair.2)

theorem realize_extract_zero_word (index : NativeIndex D)
    (zero : kappa D frame.xAxis frame.yAxis index.1 index.2 = 0) :
    realize D beta frame (extract D beta frame (nativeWord D frame.frame beta index)) =
      nativeWord D frame.frame beta index := by
  obtain ⟨powers, upper, equality⟩ := zero_occupation_exhaustion D beta frame index zero
  rw [← equality]
  cases upper <;> simp [extract, realize, readLane_nativeWord, lane_monomial]

theorem realize_extract (state : State D) (member : state ∈ fixedReduced D beta frame) :
    realize D beta frame (extract D beta frame state) = state := by
  classical
  have sector := ((fixedReduced_mem D beta frame state).mp member).1
  let coefficients := nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse
    frame.rightFrameInverse beta state
  have expansion : ∑ index ∈ coefficients.support, coefficients index • nativeWord D frame.frame beta index =
      state := native_sector_finite_expansion D frame.frame frame.inverse frame.leftFrameInverse
        frame.rightFrameInverse beta state sector
  calc
    realize D beta frame (extract D beta frame state) =
        realize D beta frame (extract D beta frame
          (∑ index ∈ coefficients.support, coefficients index • nativeWord D frame.frame beta index)) :=
      congrArg (fun vector : State D => realize D beta frame (extract D beta frame vector)) expansion.symm
    _ = ∑ index ∈ coefficients.support, coefficients index • nativeWord D frame.frame beta index := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro index supportMember
      by_cases zero : kappa D frame.xAxis frame.yAxis index.1 index.2 = 0
      · rw [realize_extract_zero_word D beta frame index zero]
      · have vanished := kernel_coefficients_vanish D beta frame state member index zero
        change coefficients index = 0 at vanished
        simp [vanished]
    _ = state := expansion

def realizeReduced : Polynomial × Polynomial →ₗ[ℂ] fixedReduced D beta frame :=
  (realize D beta frame).codRestrict (fixedReduced D beta frame) (realize_mem D beta frame)

def reducedEquiv : (Polynomial × Polynomial) ≃ₗ[ℂ] fixedReduced D beta frame where
  toLinearMap := realizeReduced D beta frame
  invFun state := extract D beta frame state
  left_inv pair := extract_realize D beta frame pair
  right_inv state := by
    apply Subtype.ext
    exact realize_extract D beta frame state state.property

theorem reducedEquiv_apply (pair : Polynomial × Polynomial) :
    (reducedEquiv D beta frame pair : State D) = realize D beta frame pair := rfl

theorem reducedEquiv_symm (state : fixedReduced D beta frame) :
    (reducedEquiv D beta frame).symm state = extract D beta frame state := rfl

theorem exact_realize_range : LinearMap.range (realize D beta frame) = fixedReduced D beta frame := by
  apply le_antisymm
  · rintro state ⟨pair, rfl⟩
    exact realize_mem D beta frame pair
  · intro state member
    exact ⟨extract D beta frame state, realize_extract D beta frame state member⟩

theorem exact_realize_range_P : LinearMap.range (realize D beta frame) =
    LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.range (actualP D beta frame) := by
  rw [exact_realize_range, fixedReduced_eq_fixed_P_range]

def projectedEquiv : (Polynomial × Polynomial) ≃ₗ[ℂ]
    ↥(LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.range (actualP D beta frame)) :=
  (reducedEquiv D beta frame).trans (LinearEquiv.ofEq _ _ (fixedReduced_eq_fixed_P_range D beta frame))

theorem fixedReduced_eq_original : fixedReduced D beta frame = originalFixedReduced D beta frame := by
  simp only [fixedReduced, originalFixedReduced, actualK_original]

def originalReducedEquiv : (Polynomial × Polynomial) ≃ₗ[ℂ] originalFixedReduced D beta frame :=
  (reducedEquiv D beta frame).trans (LinearEquiv.ofEq _ _ (fixedReduced_eq_original D beta frame))

theorem actualP_realize (pair : Polynomial × Polynomial) :
    actualP D beta frame (realize D beta frame pair) = realize D beta frame pair := by
  have rangeMember := (fixedReduced_eq_fixed_P_range D beta frame ▸ realize_mem D beta frame pair).2
  obtain ⟨preimage, equality⟩ := rangeMember
  rw [← equality]
  have idempotent := native_P_idempotent D frame.frame frame.inverse frame.leftFrameInverse
    frame.rightFrameInverse frame.xAxis frame.yAxis
  exact congrArg (fun operator : Module.End ℂ (State D) => operator preimage) idempotent

theorem every_nonzero_charge_reduced_model (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (criticalRank : D.rank = 26) (chargeNonzero : beta ≠ 0) :
    ∃ adapted : OriginalAdaptedFrameData D beta,
      Nonempty ((Polynomial × Polynomial) ≃ₗ[ℂ] fixedReduced D beta adapted) := by
  obtain ⟨adapted⟩ := original_nonzero_charge_adapted_frame_exists D H leftGramInverse rightGramInverse
    criticalRank beta chargeNonzero
  exact ⟨adapted, ⟨reducedEquiv D beta adapted⟩⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24
