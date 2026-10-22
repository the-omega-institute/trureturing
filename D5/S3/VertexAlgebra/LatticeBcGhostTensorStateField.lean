/- GID: D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostTensorStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual lattice matter tensor bc state-field and its basic vacuum, creation, parity, and translation bridges. -/

import D5.S3.VertexAlgebra.VertexOperatorTensorProduct
import D5.S3.VertexAlgebra.LatticeAllStateField
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import D5.S3.VertexAlgebra.BcGhostSuperStateField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostTensorStateField

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeFiniteNegativeGeneration
open BcGhostFockSupport BcGhostSuperGenerators
open LatticeAllStateField LatticeSugawaraConformal
open VertexOperatorTensorProduct
open scoped TensorProduct VertexOperator

abbrev State (D : LatticeData) := LatticeBcGhostBrstCharge.State D

variable {D : LatticeData}

def vacuum (D : LatticeData) : State D :=
  LatticeAllStateField.vacuum D ⊗ₜ[ℂ] (BcGhostFockSupport.vacuum : Fock ℂ)

def stateField (D : LatticeData) : State D →ₗ[ℂ] VertexOperator ℂ (State D) :=
  TensorProduct.lift (fieldBilinear.compl₁₂ (LatticeAllStateField.Y D)
    BcGhostSuperStateField.Y)

theorem stateField_tmul (D : LatticeData) (matter : Carrier D) (ghost : Fock ℂ) :
    stateField D (matter ⊗ₜ[ℂ] ghost) =
      field (LatticeAllStateField.Y D matter) (BcGhostSuperStateField.Y ghost) := by
  rfl

theorem stateField_creation_tmul (D : LatticeData) (matter : Carrier D) (ghost : Fock ℂ) :
    ((stateField D (matter ⊗ₜ[ℂ] ghost))[[-1]]) (vacuum D) = matter ⊗ₜ[ℂ] ghost := by
  rw [stateField_tmul, field_mode, vacuum, mode_tmul]
  rw [finsum_eq_single _ (-1)]
  · simp only [show (-1 : ℤ) - 1 - (-1) = -1 by norm_num,
      LatticeAllStateField.stateField_creation,
      BcGhostSuperStateField.stateField_creation]
  · intro index different
    by_cases nonnegative : 0 ≤ index
    · rw [LatticeAllStateField.stateField_creativity D matter index nonnegative,
        TensorProduct.zero_tmul]
    · have ghostNonnegative : 0 ≤ (-1 : ℤ) - 1 - index := by omega
      rw [BcGhostSuperStateField.stateField_creativity ghost (-1 - 1 - index) ghostNonnegative,
        TensorProduct.tmul_zero]

theorem stateField_creation (D : LatticeData) (state : State D) :
    ((stateField D state)[[-1]]) (vacuum D) = state := by
  induction state using TensorProduct.induction_on with
  | zero => simp [vacuum]
  | tmul matter ghost => exact stateField_creation_tmul D matter ghost
  | add first second firstIH secondIH =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, firstIH, secondIH]

theorem stateField_creativity_tmul (D : LatticeData) (matter : Carrier D) (ghost : Fock ℂ)
    (mode : ℤ) (nonnegative : 0 ≤ mode) :
    ((stateField D (matter ⊗ₜ[ℂ] ghost))[[mode]]) (vacuum D) = 0 := by
  rw [stateField_tmul, field_mode, vacuum, mode_tmul]
  apply finsum_eq_zero_of_forall_eq_zero
  intro index
  by_cases indexNonnegative : 0 ≤ index
  · rw [LatticeAllStateField.stateField_creativity D matter index indexNonnegative,
      TensorProduct.zero_tmul]
  · have ghostNonnegative : 0 ≤ mode - 1 - index := by omega
    rw [BcGhostSuperStateField.stateField_creativity ghost (mode - 1 - index) ghostNonnegative,
      TensorProduct.tmul_zero]

theorem stateField_creativity (D : LatticeData) (state : State D) (mode : ℤ)
    (nonnegative : 0 ≤ mode) :
    ((stateField D state)[[mode]]) (vacuum D) = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => simp [vacuum]
  | tmul matter ghost => exact stateField_creativity_tmul D matter ghost mode nonnegative
  | add first second firstIH secondIH =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, firstIH, secondIH, add_zero]

theorem stateField_vacuum (D : LatticeData) :
    stateField D (vacuum D) =
      identityField (State D) := by
  rw [vacuum, stateField_tmul, LatticeAllStateField.stateField_vacuum,
    BcGhostSuperStateField.stateField_vacuum]
  change field (identityField (Carrier D)) (identityField (Fock ℂ)) = _
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    field_identity_left, identityField_mode, identityField_mode]
  apply TensorProduct.ext
  ext matter ghost
  by_cases h : -power - 1 = -1
  · simp [h]
  · simp [h]

def translation (D : LatticeData) : Module.End ℂ (State D) :=
  tensorTranslation (LatticeSugawaraConformal.translation D)
    BcGhostSuperGenerators.translation

theorem translation_vacuum (D : LatticeData) : translation D (vacuum D) = 0 := by
  simp [translation, vacuum, tensorTranslation,
    LatticeAllStateField.translation_kills_vacuum,
    BcGhostSuperGenerators.translation_vacuum]

theorem stateField_covariance_tmul (D : LatticeData) (matter : Carrier D) (ghost : Fock ℂ)
    (mode : ℤ) :
    translation D * ((stateField D (matter ⊗ₜ[ℂ] ghost))[[mode]]) -
        ((stateField D (matter ⊗ₜ[ℂ] ghost))[[mode]]) * translation D =
      -(mode : ℂ) • ((stateField D (matter ⊗ₜ[ℂ] ghost))[[mode - 1]]) := by
  rw [stateField_tmul]
  exact translation_covariant (LatticeAllStateField.Y D matter)
    (BcGhostSuperStateField.Y ghost)
    (LatticeSugawaraConformal.translation D)
    BcGhostSuperGenerators.translation
    (fun index => LatticeAllStateField.stateField_covariance D matter index)
    (fun index => BcGhostSuperStateField.stateField_covariance ghost index) mode

theorem stateField_covariance (D : LatticeData) (state : State D) (mode : ℤ) :
    translation D * ((stateField D state)[[mode]]) -
        ((stateField D state)[[mode]]) * translation D =
      -(mode : ℂ) • ((stateField D state)[[mode - 1]]) := by
  induction state using TensorProduct.induction_on with
  | zero => simp [stateField]
  | tmul matter ghost => exact stateField_covariance_tmul D matter ghost mode
  | add first second firstIH secondIH =>
      simp only [map_add, Pi.add_apply, add_mul, mul_add, smul_add]
      calc
        _ = (translation D * ((stateField D first)[[mode]]) -
          ((stateField D first)[[mode]]) * translation D) +
          (translation D * ((stateField D second)[[mode]]) -
          ((stateField D second)[[mode]]) * translation D) := by abel
        _ = _ := by rw [firstIH, secondIH]

def parityPart (parity : ℕ) : Module.End ℂ (State D) :=
  TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
    (BcGhostSuperGenerators.parityPart parity)

def homogeneous (parity : ℕ) : Submodule ℂ (State D) :=
  LinearMap.range (parityPart parity)

theorem parityPart_tmul (parity : ℕ) (matter : Carrier D) (ghost : Fock ℂ) :
    parityPart parity (matter ⊗ₜ[ℂ] ghost) =
      matter ⊗ₜ[ℂ] BcGhostSuperGenerators.parityPart parity ghost := by
  rfl

theorem parityPart_mem (parity : ℕ) (state : State D) :
    parityPart parity state ∈ homogeneous parity := by
  exact ⟨state, rfl⟩

theorem parityPart_idempotent (parity : ℕ) (state : State D) :
    parityPart parity (parityPart parity state) = parityPart parity state := by
  induction state using TensorProduct.induction_on with
  | zero => simp [parityPart]
  | tmul matter ghost =>
      rw [parityPart_tmul, parityPart_tmul]
      rw [BcGhostSuperGenerators.parityPart_identity parity _
        (BcGhostSuperGenerators.parityPart_mem parity ghost)]
  | add first second firstIH secondIH =>
      simp only [map_add, firstIH, secondIH]

theorem parityPart_orthogonal (first second : ℕ) (different : first % 2 ≠ second % 2)
    (state : State D) : parityPart first (parityPart second state) = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => simp [parityPart]
  | tmul matter ghost =>
      rw [parityPart_tmul, parityPart_tmul]
      have vanish : BcGhostSuperGenerators.parityPart first
          (BcGhostSuperGenerators.parityPart second ghost) = 0 := by
        apply Finsupp.ext
        intro sites
        simp only [BcGhostSuperGenerators.parityPart_coeff, Finsupp.zero_apply]
        by_cases hfirst : subsetParity sites = first % 2
        · simp [hfirst, different]
        · simp [hfirst]
      rw [vanish, TensorProduct.tmul_zero]
  | add first second firstIH secondIH =>
      simp only [map_add, firstIH, secondIH, add_zero]

theorem parity_decomposition (state : State D) :
    parityPart 0 state + parityPart 1 state = state := by
  induction state using TensorProduct.induction_on with
  | zero => simp [parityPart]
  | tmul matter ghost =>
      rw [parityPart_tmul, parityPart_tmul,
        ← TensorProduct.tmul_add, BcGhostSuperGenerators.parity_decomposition]
  | add first second firstIH secondIH =>
      simp only [map_add]
      calc
        _ = (parityPart 0 first + parityPart 1 first) +
          (parityPart 0 second + parityPart 1 second) := by abel
        _ = _ := by rw [firstIH, secondIH]

theorem homogeneous_fixed (parity : ℕ) (state : State D) :
    state ∈ homogeneous parity ↔ parityPart parity state = state := by
  constructor
  · rintro ⟨input, rfl⟩
    exact parityPart_idempotent parity input
  · intro fixed
    exact ⟨state, fixed⟩

theorem tmul_mem (parity : ℕ) (matter : Carrier D) (ghost : Fock ℂ)
    (member : ghost ∈ BcGhostSuperGenerators.homogeneous parity) :
    matter ⊗ₜ[ℂ] ghost ∈ homogeneous parity := by
  apply (homogeneous_fixed parity _).mpr
  rw [parityPart_tmul, BcGhostSuperGenerators.parityPart_identity parity ghost member]

theorem homogeneous_induction (parity : ℕ) (predicate : State D → Prop)
    (zero : predicate 0)
    (pure : ∀ matter ghost, ghost ∈ BcGhostSuperGenerators.homogeneous parity →
      predicate (matter ⊗ₜ[ℂ] ghost))
    (add : ∀ first second, predicate first → predicate second → predicate (first + second))
    (state : State D) (member : state ∈ homogeneous parity) : predicate state := by
  obtain ⟨input, rfl⟩ := member
  induction input using TensorProduct.induction_on with
  | zero => simpa using zero
  | tmul matter ghost =>
      exact pure matter (BcGhostSuperGenerators.parityPart parity ghost)
        (BcGhostSuperGenerators.parityPart_mem parity ghost)
  | add first second firstIH secondIH =>
      simpa only [map_add] using add _ _ firstIH secondIH

theorem homogeneous_intersection_zero (state : State D)
    (even : state ∈ homogeneous 0) (odd : state ∈ homogeneous 1) : state = 0 := by
  have first := (homogeneous_fixed 0 state).mp even
  have second := (homogeneous_fixed 1 state).mp odd
  have vanish := parityPart_orthogonal 0 1 (by norm_num) state
  rw [second, first] at vanish
  exact vanish

theorem stateField_mem_tmul (stateParity inputParity : ℕ)
    (matterState matterInput : Carrier D) (ghostState ghostInput : Fock ℂ)
    (stateMember : ghostState ∈ BcGhostSuperGenerators.homogeneous stateParity)
    (inputMember : ghostInput ∈ BcGhostSuperGenerators.homogeneous inputParity)
    (mode : ℤ) :
    ((stateField D (matterState ⊗ₜ[ℂ] ghostState))[[mode]])
      (matterInput ⊗ₜ[ℂ] ghostInput) ∈ homogeneous (stateParity + inputParity) := by
  classical
  rw [stateField_tmul, field_mode, mode_tmul]
  have finite := diagonal_finite (LatticeAllStateField.Y D matterState)
    (BcGhostSuperStateField.Y ghostState) mode matterInput ghostInput
  rw [finsum_eq_sum_of_support_subset _ (s := finite.toFinset) (by
    intro index member
    exact finite.mem_toFinset.mpr member)]
  apply (homogeneous (stateParity + inputParity)).sum_mem
  intro index member
  apply tmul_mem
  exact BcGhostSuperStateField.stateField_mem stateParity ghostState stateMember
    (mode - 1 - index) inputParity ghostInput inputMember

theorem stateField_mem (stateParity inputParity : ℕ) (state input : State D)
    (stateMember : state ∈ homogeneous stateParity)
    (inputMember : input ∈ homogeneous inputParity) (mode : ℤ) :
    ((stateField D state)[[mode]]) input ∈ homogeneous (stateParity + inputParity) := by
  apply homogeneous_induction stateParity
    (fun state => ((stateField D state)[[mode]]) input ∈ homogeneous (stateParity + inputParity))
      _ _ _ state stateMember
  · simp
  · intro matterState ghostState stateMember
    apply homogeneous_induction inputParity
      (fun input => ((stateField D (matterState ⊗ₜ[ℂ] ghostState))[[mode]]) input ∈
        homogeneous (stateParity + inputParity)) _ _ _ input inputMember
    · simp
    · intro matterInput ghostInput inputMember
      exact stateField_mem_tmul stateParity inputParity matterState matterInput ghostState
        ghostInput stateMember inputMember mode
    · intro first second firstIH secondIH
      rw [map_add]
      exact (homogeneous _).add_mem firstIH secondIH
  · intro first second firstIH secondIH
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using
      (homogeneous (stateParity + inputParity)).add_mem firstIH secondIH

theorem stateField_lower_truncation (D : LatticeData) (state input : State D) :
    ∃ bound : ℤ, ∀ mode : ℤ, bound < mode → ((stateField D state)[[mode]]) input = 0 := by
  exact ⟨upper (stateField D state) input,
    fun mode bound => mode_zero_above (stateField D state) input mode bound⟩

theorem stateField_mode_tmul (D : LatticeData) (matterState matterInput : Carrier D)
    (ghostState ghostInput : Fock ℂ) (mode : ℤ) :
    ((stateField D (matterState ⊗ₜ[ℂ] ghostState))[[mode]])
      (matterInput ⊗ₜ[ℂ] ghostInput) =
    ∑ᶠ index : ℤ, ((LatticeAllStateField.Y D matterState)[[index]]) matterInput ⊗ₜ[ℂ]
      ((BcGhostSuperStateField.Y ghostState)[[mode - 1 - index]]) ghostInput := by
  rw [stateField_tmul, field_mode, mode_tmul]

theorem b_generator (D : LatticeData) (mode : ℤ) :
    ((stateField D (LatticeAllStateField.vacuum D ⊗ₜ[ℂ]
      b (-2) (BcGhostFockSupport.vacuum : Fock ℂ)))[[mode]]) =
        LatticeBcGhostBrstCharge.B D (mode - 1) := by
  rw [stateField_tmul, LatticeAllStateField.stateField_vacuum,
    BcGhostSuperStateField.stateField_b_generator]
  change ((field (identityField (Carrier D)) (currentField .b))[[mode]]) = _
  rw [field_identity_left, currentField_modes]
  rfl

theorem c_generator (D : LatticeData) (mode : ℤ) :
    ((stateField D (LatticeAllStateField.vacuum D ⊗ₜ[ℂ]
      c 1 (BcGhostFockSupport.vacuum : Fock ℂ)))[[mode]]) =
        LatticeBcGhostBrstCharge.C D (mode + 2) := by
  rw [stateField_tmul, LatticeAllStateField.stateField_vacuum,
    BcGhostSuperStateField.stateField_c_generator]
  change ((field (identityField (Carrier D)) (currentField .c))[[mode]]) = _
  rw [field_identity_left, currentField_modes]
  rfl

theorem matter_generator (D : LatticeData) (axis : Fin D.rank) (mode : ℤ) :
    ((stateField D ((((LatticeFiniteNegativeGeneration.neutralField D axis)[[-1]])
      (LatticeAllStateField.vacuum D)) ⊗ₜ[ℂ]
        (BcGhostFockSupport.vacuum : Fock ℂ)))[[mode]]) =
      TensorProduct.map (LatticeFiniteNegativeGeneration.neutralMode D axis mode)
        (LinearMap.id : Module.End ℂ (Fock ℂ)) := by
  rw [stateField_tmul, LatticeAllStateField.stateField_current,
    BcGhostSuperStateField.stateField_vacuum]
  change ((field (LatticeFiniteNegativeGeneration.neutralField D axis)
    (identityField (Fock ℂ)))[[mode]]) = _
  rw [field_identity_right, LatticeSugawaraCurrents.neutralField_ncoeff]

theorem translation_original (D : LatticeData)
    (inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : inverse * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * inverse = 1) :
    translation D = LatticeBcGhostBrstCharge.M D inverse (-1) +
      LatticeBcGhostBrstCharge.G D (-1) := by
  rw [translation, tensorTranslation,
    ← LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D inverse hHG hGH]
  rfl

end D5.S3.VertexAlgebra.LatticeBcGhostTensorStateField
