/- GID: D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit]
   utility: none
   digest: Actual finite diagrams have homogeneous interval bases. -/

import D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalSplit
import Mathlib.LinearAlgebra.Basis.Prod

namespace D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition

open Module FiniteIntervalSplit

universe u v

variable {K : Type u} [Field K] {n : ℕ} {V : Fin n → Type v}
  [∀ index, AddCommGroup (V index)] [∀ index, Module K (V index)]

structure IntervalBasis (diagram : Diagram K V) where
  Occurrence : Type
  finite : Fintype Occurrence
  birth : Occurrence → Fin n
  last : Occurrence → Fin n
  ordered : ∀ occurrence, birth occurrence ≤ last occurrence
  vectors : ∀ (_occurrence : Occurrence) index, V index
  unsupported : ∀ occurrence index, ¬ (birth occurrence ≤ index ∧ index ≤ last occurrence) →
    vectors occurrence index = 0
  basis : ∀ index, Basis {occurrence // birth occurrence ≤ index ∧ index ≤ last occurrence} K
    (V index)
  basis_vectors : ∀ index occurrence, basis index occurrence = vectors occurrence.val index
  naturality : ∀ occurrence source target (ordered : source ≤ target),
    diagram.map source target ordered (vectors occurrence source) =
      if birth occurrence ≤ source ∧ target ≤ last occurrence then vectors occurrence target else 0

attribute [instance] IntervalBasis.finite

theorem exists_interval_basis [∀ index, FiniteDimensional K (V index)]
    (diagram : Diagram K V) : Nonempty (IntervalBasis diagram) := by
  classical
  generalize dimension_eq : (∑ index, finrank K (V index)) = dimension
  induction dimension using Nat.strong_induction_on generalizing V with
  | h dimension previous =>
    by_cases zero : ∀ index, ∀ vector : V index, vector = 0
    · have : ∀ index, Subsingleton (V index) := fun index =>
        ⟨fun first second => (zero index first).trans (zero index second).symm⟩
      refine ⟨{
        Occurrence := Empty
        finite := inferInstance
        birth := Empty.elim
        last := Empty.elim
        ordered := fun occurrence => Empty.elim occurrence
        vectors := fun occurrence => Empty.elim occurrence
        unsupported := fun occurrence => Empty.elim occurrence
        basis := fun index => Basis.empty (V index)
        basis_vectors := ?_
        naturality := fun occurrence => Empty.elim occurrence }⟩
      intro index occurrence
      exact Empty.elim occurrence.val
    · have nonzero : ∃ index, ∃ vector : V index, vector ≠ 0 := by
        simpa only [not_forall] using zero
      obtain ⟨birth, last, vectors, functionals, ordered, earlier_zero, unsupported,
        normalized, vector_naturality, functional_naturality, ⟨equivalences, coordinates⟩,
        projector_naturality, kernel_naturality, descent⟩ := exists_interval_split diagram nonzero
      let kernels : Fin n → Type v := fun index => LinearMap.ker (functionals index)
      let kernel_map : ∀ source target, source ≤ target → kernels source →ₗ[K] kernels target :=
        fun source target ordered =>
          ((diagram.map source target ordered).domRestrict (LinearMap.ker (functionals source)))
            |>.codRestrict (LinearMap.ker (functionals target)) fun vector =>
              kernel_naturality source target ordered vector.val vector.property
      let kernel_diagram : Diagram K kernels := {
        map := kernel_map
        identity := by
          intro index
          ext vector
          change diagram.map index index le_rfl vector.val = vector.val
          rw [diagram.identity]
          rfl
        composition := by
          intro source middle target first second
          ext vector
          exact LinearMap.congr_fun
            (diagram.composition source middle target first second) vector.val }
      have smaller : (∑ index, finrank K (kernels index)) < dimension := by
        simpa only [← dimension_eq] using descent
      obtain ⟨remaining⟩ := previous _ smaller kernel_diagram rfl
      let line_indices := fun index => {star : Unit // birth ≤ index ∧ index ≤ last}
      let line_vectors : ∀ index, line_indices index → Submodule.span K {vectors index} :=
        fun index _ => ⟨vectors index, Submodule.mem_span_singleton_self _⟩
      have line_independent : ∀ index, LinearIndependent K (line_vectors index) := by
        intro index
        apply (linearIndependent_subsingleton_index_iff _).mpr
        intro occurrence unequal
        have vector_zero : vectors index = 0 := congrArg Subtype.val unequal
        have impossible := normalized index occurrence.property
        simp [vector_zero] at impossible
      have line_spanning : ∀ index,
          ⊤ ≤ Submodule.span K (Set.range (line_vectors index)) := by
        intro index vector _
        obtain ⟨scalar, scalar_eq⟩ := Submodule.mem_span_singleton.mp vector.property
        by_cases supported : birth ≤ index ∧ index ≤ last
        · have represented : vector = scalar • line_vectors index ⟨(), supported⟩ := by
            apply Subtype.ext
            exact scalar_eq.symm
          rw [represented]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨⟨(), supported⟩, rfl⟩)
        · have vector_zero : vector = 0 := by
            apply Subtype.ext
            simpa only [(unsupported index supported).1, smul_zero, Submodule.coe_zero]
              using scalar_eq.symm
          rw [vector_zero]
          exact Submodule.zero_mem _
      let line_basis : ∀ index, Basis (line_indices index) K (Submodule.span K {vectors index}) :=
        fun index => Basis.mk (line_independent index) (line_spanning index)
      let occurrences := Unit ⊕ remaining.Occurrence
      let new_birth : occurrences → Fin n := Sum.elim (fun _ => birth) remaining.birth
      let new_last : occurrences → Fin n := Sum.elim (fun _ => last) remaining.last
      let new_vectors : ∀ occurrence : occurrences, ∀ index, V index :=
        Sum.elim (fun _ => vectors)
          (fun occurrence index => (remaining.vectors occurrence index).val)
      let index_equivalence : ∀ index,
          (line_indices index ⊕ {occurrence : remaining.Occurrence //
            remaining.birth occurrence ≤ index ∧ index ≤ remaining.last occurrence}) ≃
          {occurrence : occurrences //
            new_birth occurrence ≤ index ∧ index ≤ new_last occurrence} :=
        fun index => {
          toFun := fun occurrence => match occurrence with
            | Sum.inl star => ⟨Sum.inl star.val, star.property⟩
            | Sum.inr previous => ⟨Sum.inr previous.val, previous.property⟩
          invFun := fun occurrence => match occurrence with
            | ⟨Sum.inl star, supported⟩ => Sum.inl ⟨star, supported⟩
            | ⟨Sum.inr previous, supported⟩ => Sum.inr ⟨previous, supported⟩
          left_inv := by intro occurrence; cases occurrence <;> rfl
          right_inv := by intro occurrence; rcases occurrence with ⟨occurrence, supported⟩
                          cases occurrence <;> rfl }
      let new_basis : ∀ index, Basis
          {occurrence : occurrences // new_birth occurrence ≤ index ∧ index ≤ new_last occurrence}
          K (V index) := fun index =>
        (((line_basis index).prod (remaining.basis index)).map (equivalences index).symm)
          |>.reindex (index_equivalence index)
      have inverse_coordinates : ∀ index pair,
          (equivalences index).symm pair = (pair.1 : V index) + (pair.2 : V index) := by
        intro index pair
        have recorded := coordinates index ((equivalences index).symm pair)
        simp only [LinearEquiv.apply_symm_apply] at recorded
        rw [recorded.1, recorded.2]
        rw [add_comm, sub_add_cancel]
      refine ⟨{
        Occurrence := occurrences
        finite := inferInstance
        birth := new_birth
        last := new_last
        ordered := ?_
        vectors := new_vectors
        unsupported := ?_
        basis := new_basis
        basis_vectors := ?_
        naturality := ?_ }⟩
      · intro occurrence
        cases occurrence with
        | inl star => exact ordered
        | inr previous => exact remaining.ordered previous
      · intro occurrence index outside
        cases occurrence with
        | inl star => exact (unsupported index outside).1
        | inr previous =>
          exact congrArg Subtype.val (remaining.unsupported previous index outside)
      · intro index occurrence
        rcases occurrence with ⟨occurrence, supported⟩
        cases occurrence with
        | inl star =>
          simp only [new_basis, Basis.reindex_apply, Basis.map_apply]
          change (equivalences index).symm
            ((line_basis index).prod (remaining.basis index) (Sum.inl ⟨star, supported⟩)) =
              vectors index
          rw [inverse_coordinates]
          simp [line_basis, line_vectors]
        | inr previous =>
          simp only [new_basis, Basis.reindex_apply, Basis.map_apply]
          change (equivalences index).symm
            ((line_basis index).prod (remaining.basis index) (Sum.inr ⟨previous, supported⟩)) =
              (remaining.vectors previous index).val
          rw [inverse_coordinates]
          simp [remaining.basis_vectors]
      · intro occurrence source target order
        cases occurrence with
        | inl star => exact vector_naturality source target order
        | inr previous =>
          have actual := congrArg Subtype.val (remaining.naturality previous source target order)
          change diagram.map source target order (remaining.vectors previous source).val =
            (if remaining.birth previous ≤ source ∧ target ≤ remaining.last previous then
              remaining.vectors previous target else 0).val at actual
          by_cases active : remaining.birth previous ≤ source ∧ target ≤ remaining.last previous
          · simpa [new_vectors, new_birth, new_last, active] using actual
          · simpa [new_vectors, new_birth, new_last, active] using actual

end D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition
