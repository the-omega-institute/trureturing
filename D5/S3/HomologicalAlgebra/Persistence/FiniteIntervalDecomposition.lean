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

open Module CategoryTheory FiniteIntervalSplit

universe u v

variable {K : Type u} [Field K] {n : ℕ}

theorem exists_interval_basis (diagram : Fin n ⥤ ModuleCat.{v} K)
    [∀ index, FiniteDimensional K (diagram.obj index)] :
    ∃ (Occurrence : Type) (finite : Fintype Occurrence),
      ∃ (birth last : Occurrence → Fin n)
        (vectors : ∀ (_occurrence : Occurrence) index, diagram.obj index)
        (basis : ∀ index, Basis
          {occurrence // birth occurrence ≤ index ∧ index ≤ last occurrence} K
          (diagram.obj index)),
        (∀ occurrence, birth occurrence ≤ last occurrence) ∧
        (∀ occurrence index, ¬ (birth occurrence ≤ index ∧ index ≤ last occurrence) →
          vectors occurrence index = 0) ∧
        (∀ index occurrence, basis index occurrence = vectors occurrence.val index) ∧
        (∀ occurrence source target (ordered : source ≤ target),
          (diagram.map (homOfLE ordered)).hom (vectors occurrence source) =
            if birth occurrence ≤ source ∧ target ≤ last occurrence then
              vectors occurrence target else 0) := by
  classical
  generalize dimension_eq : (∑ index, finrank K (diagram.obj index)) = dimension
  induction dimension using Nat.strong_induction_on generalizing diagram with
  | h dimension previous =>
    let V := fun index => diagram.obj index
    let maps := fun source target (ordered : source ≤ target) =>
      (diagram.map (homOfLE ordered)).hom
    have identity : ∀ index, maps index index le_rfl = LinearMap.id := by
      intro index
      change (diagram.map (𝟙 index)).hom = _
      rw [diagram.map_id, ModuleCat.hom_id]
    have composition : ∀ source middle target (first : source ≤ middle)
        (second : middle ≤ target),
        (maps middle target second).comp (maps source middle first) =
          maps source target (first.trans second) := by
      intro source middle target first second
      exact (congrArg ModuleCat.Hom.hom
        (diagram.map_comp (homOfLE first) (homOfLE second))).symm
    by_cases zero : ∀ index, ∀ vector : V index, vector = 0
    · have : ∀ index, Subsingleton (V index) := fun index =>
        ⟨fun first second => (zero index first).trans (zero index second).symm⟩
      refine ⟨Empty, inferInstance, Empty.elim, Empty.elim,
        (fun occurrence => Empty.elim occurrence), (fun index => Basis.empty (V index)),
        (fun occurrence => Empty.elim occurrence),
        (fun occurrence => Empty.elim occurrence), ?_,
        (fun occurrence => Empty.elim occurrence)⟩
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
          ((maps source target ordered).domRestrict (LinearMap.ker (functionals source)))
            |>.codRestrict (LinearMap.ker (functionals target)) fun vector =>
              kernel_naturality source target ordered vector.val vector.property
      let kernel_diagram : Fin n ⥤ ModuleCat.{v} K := {
        obj index := ModuleCat.of K (kernels index)
        map arrow := ModuleCat.ofHom (kernel_map _ _ (leOfHom arrow))
        map_id := by
          intro index
          apply ModuleCat.hom_ext
          ext vector
          change maps index index le_rfl vector.val = vector.val
          rw [identity]
          rfl
        map_comp := by
          intro source middle target first second
          apply ModuleCat.hom_ext
          ext vector
          exact (LinearMap.congr_fun
            (composition source middle target (leOfHom first) (leOfHom second)) vector.val).symm }
      have smaller : (∑ index, finrank K (kernels index)) < dimension := by
        simpa only [← dimension_eq] using descent
      obtain ⟨Remaining, remaining_finite, remaining_birth, remaining_last, remaining_vectors,
        remaining_basis, remaining_ordered, remaining_unsupported, remaining_basis_vectors,
        remaining_naturality⟩ := previous _ smaller kernel_diagram rfl
      letI := remaining_finite
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
      let occurrences := Unit ⊕ Remaining
      let new_birth : occurrences → Fin n := Sum.elim (fun _ => birth) remaining_birth
      let new_last : occurrences → Fin n := Sum.elim (fun _ => last) remaining_last
      let new_vectors : ∀ occurrence : occurrences, ∀ index, V index :=
        Sum.elim (fun _ => vectors)
          (fun occurrence index => (remaining_vectors occurrence index).val)
      let index_equivalence : ∀ index,
          (line_indices index ⊕ {occurrence : Remaining //
            remaining_birth occurrence ≤ index ∧ index ≤ remaining_last occurrence}) ≃
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
        (((line_basis index).prod (remaining_basis index)).map (equivalences index).symm)
          |>.reindex (index_equivalence index)
      have inverse_coordinates : ∀ index pair,
          (equivalences index).symm pair = (pair.1 : V index) + (pair.2 : V index) := by
        intro index pair
        have recorded := coordinates index ((equivalences index).symm pair)
        simp only [LinearEquiv.apply_symm_apply] at recorded
        rw [recorded.1, recorded.2]
        rw [add_comm, sub_add_cancel]
      refine ⟨occurrences, inferInstance, new_birth, new_last, new_vectors, new_basis,
        ?_, ?_, ?_, ?_⟩
      · intro occurrence
        cases occurrence with
        | inl star => exact ordered
        | inr previous => exact remaining_ordered previous
      · intro occurrence index outside
        cases occurrence with
        | inl star => exact (unsupported index outside).1
        | inr previous =>
          exact congrArg Subtype.val (remaining_unsupported previous index outside)
      · intro index occurrence
        rcases occurrence with ⟨occurrence, supported⟩
        cases occurrence with
        | inl star =>
          simp only [new_basis, Basis.reindex_apply, Basis.map_apply]
          change (equivalences index).symm
            ((line_basis index).prod (remaining_basis index) (Sum.inl ⟨star, supported⟩)) =
              vectors index
          rw [inverse_coordinates]
          simp [line_basis, line_vectors]
        | inr previous =>
          simp only [new_basis, Basis.reindex_apply, Basis.map_apply]
          change (equivalences index).symm
            ((line_basis index).prod (remaining_basis index) (Sum.inr ⟨previous, supported⟩)) =
              (remaining_vectors previous index).val
          rw [inverse_coordinates]
          simp [remaining_basis_vectors]
      · intro occurrence source target order
        cases occurrence with
        | inl star => exact vector_naturality source target order
        | inr previous =>
          have actual := congrArg Subtype.val (remaining_naturality previous source target order)
          change maps source target order (remaining_vectors previous source).val =
            (if remaining_birth previous ≤ source ∧ target ≤ remaining_last previous then
              remaining_vectors previous target else 0).val at actual
          by_cases active : remaining_birth previous ≤ source ∧ target ≤ remaining_last previous
          · simpa [new_vectors, new_birth, new_last, active] using actual
          · simpa [new_vectors, new_birth, new_last, active] using actual

end D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition
