/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Character codes are relation orthogonals; degenerate families are audited. -/
/- Library-search audit trail (2026-08-29):
   * Exact repository searches for role-code duality and the source title found no theorem.
   * `BinaryCharacterSemanticRedundancy` gives complementary dimensions, not orthogonality.
   * Range/kernel and annihilator-shape searches found no D5 equality with these definitions.
   * Pinned Mathlib's dual and bilinear-form files provide dual-map rank and double orthogonals.
   * The power-character and quartic-completion modules use multiplicative roots, not this F2 code.
-/

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Dual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

open Matrix Module

/-- The standard coordinate pairing on `K^I`, specialized to `K = ZMod 2` in FPOD 93. -/
def standardCoordinatePairing (K I : Type*) [CommSemiring K] [Fintype I] :
    LinearMap.BilinForm K (I -> K) :=
  dotProductBilin K K

/-- Coefficient vectors whose linear combination of the character family is zero. -/
def characterRelationSpace
    (K : Type*) [CommSemiring K]
    {V : Type*} [AddCommMonoid V] [Module K V]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual K V) : Submodule K (I -> K) :=
  LinearMap.ker (Fintype.linearCombination K characters)

/-- The code of realizable joint character profiles. -/
def characterCode
    (K : Type*) [Semiring K]
    {V : Type*} [AddCommMonoid V] [Module K V]
    {I : Type*}
    (characters : I -> Module.Dual K V) : Submodule K (I -> K) :=
  LinearMap.range (LinearMap.pi characters)

/-- Orthogonal complementation for the standard coordinate pairing. -/
def characterOrthogonalComplement
    (K : Type*) [CommSemiring K]
    {I : Type*} [Fintype I]
    (space : Submodule K (I -> K)) : Submodule K (I -> K) :=
  (standardCoordinatePairing K I).orthogonal space

private theorem standardCoordinatePairing_symm
    (K I : Type*) [Field K] [Fintype I] :
    (standardCoordinatePairing K I).IsSymm := by
  constructor
  exact dotProduct_comm

private theorem standardCoordinatePairing_nondegenerate
    (K I : Type*) [Field K] [Fintype I] :
    (standardCoordinatePairing K I).Nondegenerate := by
  apply
    (standardCoordinatePairing_symm K I).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro vector vanishes
  apply dotProduct_eq_zero vector
  exact vanishes

set_option maxHeartbeats 2000000 in
-- Dual-map range normalization in the reverse inclusion needs the larger elaboration budget.
/-- The realizable character code is the standard orthogonal complement of all relations.
For FPOD 93.1, instantiate `K` with `ZMod 2`; the theorem itself needs no finiteness of `V`. -/
theorem character_code_eq_relation_space_orthogonal
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual K V) :
    characterCode K characters =
      characterOrthogonalComplement K (characterRelationSpace K characters) := by
  classical
  let profileMap : V →ₗ[K] (I -> K) := LinearMap.pi characters
  have synthesis_eq_dual : Fintype.linearCombination K characters =
      profileMap.dualMap.comp (dotProductEquiv K I).toLinearMap := by
    apply LinearMap.ext
    intro coefficients
    apply LinearMap.ext
    intro state
    simp [profileMap, Fintype.linearCombination_apply, dotProductEquiv, dotProduct]
  have synthesis_range :
      LinearMap.range (Fintype.linearCombination K characters) =
        LinearMap.range profileMap.dualMap := by
    rw [synthesis_eq_dual]
    exact LinearMap.range_comp_of_range_eq_top profileMap.dualMap
      (LinearEquiv.range (dotProductEquiv K I))
  have code_finrank : Module.finrank K (characterCode K characters) =
      Module.finrank K
        (LinearMap.range (Fintype.linearCombination K characters)) := by
    rw [characterCode]
    change Module.finrank K (LinearMap.range profileMap) = _
    rw [synthesis_range]
    exact (LinearMap.finrank_range_dualMap_eq_finrank_range profileMap).symm
  have code_le : characterCode K characters <=
      characterOrthogonalComplement K (characterRelationSpace K characters) := by
    rintro profile ⟨state, rfl⟩
    intro relation relation_mem
    have relation_zero := LinearMap.mem_ker.mp relation_mem
    have evaluated := LinearMap.congr_fun relation_zero state
    change (∑ i, relation i * characters i state) = 0
    simpa [standardCoordinatePairing, Fintype.linearCombination_apply] using evaluated
  apply le_antisymm code_le
  have orthogonal_finrank :
      Module.finrank K
          (characterOrthogonalComplement K (characterRelationSpace K characters)) =
        Module.finrank K (I -> K) -
          Module.finrank K (characterRelationSpace K characters) := by
    exact LinearMap.BilinForm.finrank_orthogonal
      (standardCoordinatePairing_nondegenerate K I) _
  have rank_nullity :
      Module.finrank K
          (LinearMap.range (Fintype.linearCombination K characters)) +
        Module.finrank K (characterRelationSpace K characters) =
          Module.finrank K (I -> K) := by
    change
      Module.finrank K
          (LinearMap.range (Fintype.linearCombination K characters)) +
        Module.finrank K
          (LinearMap.ker (Fintype.linearCombination K characters)) =
            Module.finrank K (I -> K)
    exact LinearMap.finrank_range_add_finrank_ker
      (Fintype.linearCombination K characters)
  have equal_finrank : Module.finrank K (characterCode K characters) =
      Module.finrank K
        (characterOrthogonalComplement K (characterRelationSpace K characters)) := by
    rw [code_finrank, orthogonal_finrank]
    omega
  exact (Submodule.eq_of_le_of_finrank_le code_le (by omega)).ge

#print axioms character_code_eq_relation_space_orthogonal

/-- Standard orthogonal complementation is involutive on every finite coordinate space. -/
theorem standard_orthogonal_complement_involutive
    (K : Type*) [Field K]
    {I : Type*} [Fintype I]
    (space : Submodule K (I -> K)) :
    characterOrthogonalComplement K (characterOrthogonalComplement K space) = space := by
  exact LinearMap.BilinForm.orthogonal_orthogonal
    (standardCoordinatePairing_nondegenerate K I)
    (standardCoordinatePairing_symm K I).isRefl space

#print axioms standard_orthogonal_complement_involutive

/-- A field-like coefficient hypothesis is necessary for the uniform theorem: over `ℤ`, the
single functional `x ↦ 2x` has zero relation space but its code contains only even integers. -/
theorem field_coefficients_are_necessary :
    let characters :=
      fun _ : Unit => (2 : ℤ) • (LinearMap.id : Module.Dual ℤ ℤ)
    characterCode ℤ characters ≠
      characterOrthogonalComplement ℤ (characterRelationSpace ℤ characters) := by
  dsimp only
  let characters :=
    fun _ : Unit => (2 : ℤ) • (LinearMap.id : Module.Dual ℤ ℤ)
  have relation_bot : characterRelationSpace ℤ characters = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro relation relation_mem
    have relation_zero := LinearMap.mem_ker.mp relation_mem
    have evaluated := LinearMap.congr_fun relation_zero 1
    have coordinate_zero : relation () * 2 = 0 := by
      simpa [characters, Fintype.linearCombination_apply] using evaluated
    have relation_unit : relation () = 0 :=
      (mul_eq_zero.mp coordinate_zero).resolve_right (by norm_num)
    funext i
    cases i
    exact relation_unit
  intro equality
  have one_mem_orthogonal :
      (fun _ : Unit => (1 : ℤ)) ∈
        characterOrthogonalComplement ℤ (characterRelationSpace ℤ characters) := by
    rw [relation_bot]
    simp [characterOrthogonalComplement]
  have one_mem_code : (fun _ : Unit => (1 : ℤ)) ∈ characterCode ℤ characters := by
    rw [equality]
    exact one_mem_orthogonal
  rcases one_mem_code with ⟨state, profile_eq⟩
  have parity := congrFun profile_eq ()
  simp [characters] at parity
  omega

#print axioms field_coefficients_are_necessary

section DegenerateAudit

-- FPOD 93 fixes the coefficient field to `ZMod 2` and has no exponent parameter `n` to audit.

-- An empty character family has zero code and the full relation space.
example
    (K : Type*) [Field K]
    (V : Type*) [AddCommGroup V] [Module K V]
    (characters : Empty -> Module.Dual K V) :
    characterCode K characters = ⊥ ∧ characterRelationSpace K characters = ⊤ := by
  constructor
  · rw [Submodule.eq_bot_iff]
    rintro profile ⟨state, rfl⟩
    exact Subsingleton.elim _ _
  · ext profile
    simp [characterRelationSpace, Fintype.linearCombination_apply]

-- A family of zero characters has zero code and every coefficient vector is a relation.
example
    (K : Type*) [Field K]
    (V : Type*) [AddCommGroup V] [Module K V]
    {I : Type*} [Fintype I] :
    characterCode K (fun _ : I => (0 : Module.Dual K V)) = ⊥ ∧
      characterRelationSpace K (fun _ : I => (0 : Module.Dual K V)) = ⊤ := by
  constructor
  · rw [Submodule.eq_bot_iff]
    rintro profile ⟨state, rfl⟩
    ext i
    simp
  · ext profile
    simp [characterRelationSpace, Fintype.linearCombination_apply]

-- A single identity character has full one-coordinate code and no nonzero relation.
example (K : Type*) [Field K] :
    characterCode K (fun _ : Unit => (LinearMap.id : Module.Dual K K)) = ⊤ ∧
      characterRelationSpace K
        (fun _ : Unit => (LinearMap.id : Module.Dual K K)) = ⊥ := by
  constructor
  · rw [eq_top_iff]
    intro profile _
    refine ⟨profile (), ?_⟩
    funext i
    cases i
    rfl
  · rw [Submodule.eq_bot_iff]
    intro profile profile_mem
    have relation_zero := LinearMap.mem_ker.mp profile_mem
    have evaluated := LinearMap.congr_fun relation_zero 1
    funext i
    cases i
    simpa [Fintype.linearCombination_apply] using evaluated

-- Two copies of one character are linearly dependent through the vector `(1, -1)`.
example (K : Type*) [Field K] :
    ∃ relation : Fin 2 -> K,
      relation ≠ 0 ∧
        relation ∈ characterRelationSpace K
          (fun _ : Fin 2 => (LinearMap.id : Module.Dual K K)) := by
  classical
  refine ⟨![1, -1], ?_, ?_⟩
  · intro relation_zero
    have first_coordinate := congrFun relation_zero 0
    simp at first_coordinate
  · rw [characterRelationSpace, LinearMap.mem_ker]
    apply LinearMap.ext
    intro scalar
    simp [Fintype.linearCombination_apply, Fin.sum_univ_two]

end DegenerateAudit

end D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
