import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis15

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem ghost_sign_square (site : ℕ) (subset : Finset ℕ) :
    sign (K := ℂ) site subset * sign (K := ℂ) site subset = 1 := by
  unfold sign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem ghost_sign_erase_three (subset : Finset ℕ) :
    sign (K := ℂ) 3 (subset.erase 3) = sign (K := ℂ) 3 subset := by
  have unchanged : (subset.erase 3).filter (fun site => site < 3) =
      subset.filter (fun site => site < 3) := by
    ext site
    by_cases equal : site = 3 <;> simp [equal]
  simp only [sign, unchanged]

theorem ghost_sign_toggleOne_three (subset : Finset ℕ) :
    sign (K := ℂ) 3 (toggleOne subset) = -sign (K := ℂ) 3 subset := by
  by_cases present : 1 ∈ subset
  · have absent : 1 ∉ subset.erase 1 := Finset.notMem_erase 1 subset
    have signInsertion : sign (K := ℂ) 3 (insert 1 (subset.erase 1)) =
        -sign (K := ℂ) 3 (subset.erase 1) := by
      simp [sign, Finset.filter_insert, absent, pow_succ, mul_comm]
    rw [Finset.insert_erase present] at signInsertion
    simp [toggleOne, present, signInsertion]
  · simp [toggleOne, present, sign, Finset.filter_insert, pow_succ, mul_comm]

theorem polarizationSign_erase_three (subset : Finset ℕ) (present : 3 ∈ subset) :
    polarizationSign subset = -polarizationSign (subset.erase 3) := by
  conv_lhs => rw [← Finset.insert_erase present]
  simp [polarizationSign, Finset.filter_insert, pow_succ, mul_comm]

theorem toggleOne_erase_three (subset : Finset ℕ) :
    toggleOne (subset.erase 3) = (toggleOne subset).erase 3 := by
  by_cases present : 1 ∈ subset
  · have presentErase : 1 ∈ subset.erase 3 :=
      Finset.mem_erase.mpr ⟨by decide, present⟩
    simp only [toggleOne, if_pos present, if_pos presentErase]
    simpa using (Finset.erase_right_comm (s := subset) (a := 3) (b := 1))
  · have absentErase : 1 ∉ subset.erase 3 := by
      intro member
      exact present (Finset.mem_of_mem_erase member)
    simp only [toggleOne, if_neg present, if_neg absentErase]
    exact (Finset.erase_insert_of_ne (s := subset) (a := 1) (b := 3) (by decide)).symm

theorem original_b_zero_signed_word (subset : Finset ℕ) :
    b (K := ℂ) 0 (downWord subset down) =
      if 3 ∈ subset then sign (K := ℂ) 3 subset • downWord (subset.erase 3) down else 0 := by
  classical
  by_cases present : 3 ∈ subset
  · have occupied : 3 ∈ toggleOne subset := (toggleOne_mem 3 subset (by decide)).mpr present
    rw [if_pos present, signed_down_word, signed_down_word]
    simp [polarizedBasis, b, annihilate, annihilateBasis, Finsupp.linearCombination_single,
      occupied, ← toggleOne_erase_three, ghost_sign_toggleOne_three,
      polarizationSign_erase_three subset present, Finsupp.smul_single,
      smul_smul, mul_comm, mul_left_comm, mul_assoc]
  · have unoccupied : 3 ∉ toggleOne subset := by
      simpa only [toggleOne_mem 3 subset (by decide)] using present
    simp [present, signed_down_word, polarizedBasis, b, annihilate,
      annihilateBasis, Finsupp.linearCombination_single, unoccupied]

theorem original_c_zero_b_zero_single (subset : Finset ℕ) :
    c (K := ℂ) 0 (b (K := ℂ) 0 (Finsupp.single subset (1 : ℂ))) =
      if 3 ∈ subset then Finsupp.single subset (1 : ℂ) else 0 := by
  classical
  by_cases present : 3 ∈ subset
  · simp [b, c, annihilate, create, annihilateBasis, createBasis,
      Finsupp.linearCombination_single, present, Finset.insert_erase present,
      ghost_sign_erase_three, Finsupp.smul_single, ghost_sign_square]
  · simp [b, c, annihilate, annihilateBasis, Finsupp.linearCombination_single, present]

theorem original_c_zero_b_zero_signed_word (subset : Finset ℕ) :
    c (K := ℂ) 0 (b (K := ℂ) 0 (downWord subset down)) =
      if 3 ∈ subset then downWord subset down else 0 := by
  rw [signed_down_word]
  simp only [polarizedBasis, map_smul, original_c_zero_b_zero_single]
  have occupancy := toggleOne_mem 3 subset (by decide)
  by_cases present : 3 ∈ subset
  · simp [present, occupancy.mpr present]
  · have unoccupied : 3 ∉ toggleOne subset := by simpa only [occupancy] using present
    simp [present, unoccupied]

theorem nativeWord_Bzero (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (index : NativeIndex D) :
    B D 0 (nativeWord D frame beta index) =
      if 3 ∈ index.2 then sign (K := ℂ) 3 index.2 •
        nativeWord D frame beta (index.1, index.2.erase 3) else 0 := by
  classical
  simp only [nativeWord, B, TensorProduct.map_tmul, LinearMap.id_apply,
    original_b_zero_signed_word]
  by_cases present : 3 ∈ index.2
  · simp [present, TensorProduct.tmul_smul]
  · simp [present]

theorem nativeWord_Czero_Bzero (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (index : NativeIndex D) :
    C D 0 (B D 0 (nativeWord D frame beta index)) =
      if 3 ∈ index.2 then nativeWord D frame beta index else 0 := by
  classical
  simp only [nativeWord, B, C, TensorProduct.map_tmul, LinearMap.id_apply,
    original_c_zero_b_zero_signed_word]
  by_cases present : 3 ∈ index.2 <;> simp [present]

section NativeRelativeCoordinates

variable (D : LatticeData)
variable (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D)

theorem nativeCzeroBzero_coefficient (psi : State D) (sector : chargeProjection D beta psi = psi)
    (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta (C D 0 (B D 0 psi)) index =
      if 3 ∈ index.2 then nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index else 0 := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
  have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
    (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
  have image : C D 0 (B D 0 psi) = ∑ key ∈ coefficients.support,
      (if 3 ∈ key.2 then coefficients key else 0) • nativeWord D frame beta key := by
    rw [expansion]
    simp only [map_sum, map_smul, nativeWord_Czero_Bzero]
    apply Finset.sum_congr rfl
    intro key member
    by_cases present : 3 ∈ key.2 <;> simp [present]
  rw [image, nativeCoefficient_sum]
  by_cases member : index ∈ coefficients.support
  · simp [member, coefficients]
  · have vanished : coefficients index = 0 := Finsupp.notMem_support_iff.mp member
    change (if index ∈ coefficients.support then _ else 0) = if 3 ∈ index.2 then coefficients index else 0
    simp [member, vanished]

theorem native_relative_epsilon_coefficients (psi : State D)
    (sector : chargeProjection D beta psi = psi) (relative : B D 0 psi = 0)
    (index : NativeIndex D) (present : 3 ∈ index.2) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index = 0 := by
  have diagonal := nativeCzeroBzero_coefficient D frame inverse leftFrameInverse rightFrameInverse beta psi sector index
  simpa [relative, present] using diagonal.symm

theorem native_relative_support (psi : State D) (sector : chargeProjection D beta psi = psi)
    (relative : B D 0 psi = 0) (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index ≠ 0) :
    3 ∉ index.2 := by
  intro present
  exact nonzero (native_relative_epsilon_coefficients D frame inverse leftFrameInverse rightFrameInverse
    beta psi sector relative index present)

theorem native_relative_iff_support (psi : State D) (sector : chargeProjection D beta psi = psi) :
    B D 0 psi = 0 ↔
      ∀ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
        3 ∉ index.2 := by
  classical
  constructor
  · intro relative index member
    exact native_relative_support D frame inverse leftFrameInverse rightFrameInverse beta psi sector relative
      index (Finsupp.mem_support_iff.mp member)
  · intro support
    let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
    have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
      (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
    rw [expansion]
    simp only [map_sum, map_smul, nativeWord_Bzero]
    apply Finset.sum_eq_zero
    intro index member
    simp [support index member]

theorem native_relative_finite_expansion (psi : State D) (sector : chargeProjection D beta psi = psi)
    (relative : B D 0 psi = 0) :
    ∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support.filter
        (fun key => 3 ∉ key.2),
      nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index •
        nativeWord D frame beta index = psi := by
  classical
  have support := (native_relative_iff_support D frame inverse leftFrameInverse rightFrameInverse beta psi sector).mp relative
  rw [Finset.filter_eq_self.mpr support]
  exact native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector

end NativeRelativeCoordinates

abbrev RelativeNativeIndex (D : LatticeData) := (Index D →₀ ℕ) × {subset : Finset ℕ // 3 ∉ subset}

def relativeIndexInclusion (D : LatticeData) (index : RelativeNativeIndex D) : NativeIndex D :=
  (index.1, index.2.val)

theorem relativeIndexInclusion_injective (D : LatticeData) :
    Function.Injective (relativeIndexInclusion D) := by
  intro first second equalImages
  apply Prod.ext
  · exact congrArg (fun pair : NativeIndex D => pair.1) equalImages
  · apply Subtype.ext
    exact congrArg (fun pair : NativeIndex D => pair.2) equalImages

def relativeNativeWord (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (index : RelativeNativeIndex D) : State D :=
  nativeWord D frame beta (relativeIndexInclusion D index)

def nativeRelativeSector (D : LatticeData) (beta : Charge D) : Submodule ℂ (State D) :=
  LinearMap.range (chargeEmbedding D beta) ⊓ LinearMap.ker (B D 0)

theorem nativeRelativeSector_mem_iff (D : LatticeData) (beta : Charge D) (psi : State D) :
    psi ∈ nativeRelativeSector D beta ↔ chargeProjection D beta psi = psi ∧ B D 0 psi = 0 := by
  simp only [nativeRelativeSector, Submodule.mem_inf, chargeEmbedding_range_iff, LinearMap.mem_ker]

theorem relativeNativeWord_mem (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (index : RelativeNativeIndex D) :
    relativeNativeWord D frame beta index ∈ nativeRelativeSector D beta := by
  rw [nativeRelativeSector_mem_iff]
  constructor
  · exact nativeWord_sector D frame beta (relativeIndexInclusion D index)
  · simpa [relativeNativeWord, relativeIndexInclusion, index.2.property] using
      nativeWord_Bzero D frame beta (relativeIndexInclusion D index)

theorem relativeNativeWord_linearIndependent (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) : LinearIndependent ℂ (relativeNativeWord D frame beta) :=
  (nativeWord_linearIndependent D frame inverse leftFrameInverse rightFrameInverse beta).comp
    (relativeIndexInclusion D) (relativeIndexInclusion_injective D)

theorem native_relative_span_eq (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) :
    Submodule.span ℂ (Set.range (relativeNativeWord D frame beta)) = nativeRelativeSector D beta := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact relativeNativeWord_mem D frame beta index
  · intro psi member
    obtain ⟨sector, relative⟩ := (nativeRelativeSector_mem_iff D beta psi).mp member
    rw [← native_relative_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector relative]
    apply Submodule.sum_mem
    intro index indexMember
    apply Submodule.smul_mem
    have absent : 3 ∉ index.2 := (Finset.mem_filter.mp indexMember).2
    exact Submodule.subset_span ⟨(index.1, ⟨index.2, absent⟩), rfl⟩

def nativeRelativeBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) : Module.Basis (RelativeNativeIndex D) ℂ (nativeRelativeSector D beta) :=
  (Module.Basis.span (relativeNativeWord_linearIndependent D frame inverse leftFrameInverse rightFrameInverse beta)).map
    (LinearEquiv.ofEq (Submodule.span ℂ (Set.range (relativeNativeWord D frame beta)))
      (nativeRelativeSector D beta)
      (native_relative_span_eq D frame inverse leftFrameInverse rightFrameInverse beta))

theorem nativeRelativeBasis_apply (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (index : RelativeNativeIndex D) :
    (nativeRelativeBasis D frame inverse leftFrameInverse rightFrameInverse beta index : State D) =
      relativeNativeWord D frame beta index := by
  simp only [nativeRelativeBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.span_apply]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
