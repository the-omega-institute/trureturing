/- GID: D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Basis.VectorSpace]
   utility: none
   digest: A nonzero finite diagram has a natural interval split and smaller kernel dimension. -/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

namespace D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalSplit

open Module

universe u v

variable {K : Type u} [Field K] {n : ℕ} {V : Fin n → Type v}
  [∀ index, AddCommGroup (V index)] [∀ index, Module K (V index)]

structure Diagram (K : Type u) [Field K] {n : ℕ} (V : Fin n → Type v)
    [∀ index, AddCommGroup (V index)] [∀ index, Module K (V index)] where
  map : ∀ source target, source ≤ target → V source →ₗ[K] V target
  identity : ∀ index, map index index le_rfl = LinearMap.id
  composition : ∀ source middle target (first : source ≤ middle) (second : middle ≤ target),
    (map middle target second).comp (map source middle first) =
      map source target (first.trans second)

theorem exists_interval_split [∀ index, FiniteDimensional K (V index)]
    (diagram : Diagram K V) (nonzero : ∃ index, ∃ vector : V index, vector ≠ 0) :
    ∃ (birth last : Fin n) (vectors : ∀ index, V index)
      (functionals : ∀ index, V index →ₗ[K] K),
      birth ≤ last ∧
      (∀ index, index < birth → ∀ vector : V index, vector = 0) ∧
      (∀ index, ¬ (birth ≤ index ∧ index ≤ last) →
        vectors index = 0 ∧ functionals index = 0) ∧
      (∀ index, birth ≤ index ∧ index ≤ last → functionals index (vectors index) = 1) ∧
      (∀ source target (ordered : source ≤ target),
        diagram.map source target ordered (vectors source) =
          if birth ≤ source ∧ target ≤ last then vectors target else 0) ∧
      (∀ source target (ordered : source ≤ target),
        (functionals target).comp (diagram.map source target ordered) =
          if birth ≤ source ∧ target ≤ last then functionals source else 0) ∧
      (∃ equivalences : ∀ index,
          V index ≃ₗ[K] ((Submodule.span K {vectors index}) × LinearMap.ker (functionals index)),
        ∀ index vector,
          ((equivalences index vector).1 : V index) = functionals index vector • vectors index ∧
          ((equivalences index vector).2 : V index) =
            vector - functionals index vector • vectors index) ∧
      (∀ source target (ordered : source ≤ target) vector,
        diagram.map source target ordered (functionals source vector • vectors source) =
          functionals target (diagram.map source target ordered vector) • vectors target) ∧
      (∀ source target (ordered : source ≤ target) vector,
        functionals source vector = 0 →
          functionals target (diagram.map source target ordered vector) = 0) ∧
      (∑ index, finrank K (LinearMap.ker (functionals index))) <
        ∑ index, finrank K (V index) := by
  classical
  let live := Finset.univ.filter fun index => ∃ vector : V index, vector ≠ 0
  have live_nonempty : live.Nonempty := by
    obtain ⟨index, vector, unequal⟩ := nonzero
    exact ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, vector, unequal⟩⟩
  let birth := live.min' live_nonempty
  have birth_live : birth ∈ live := Finset.min'_mem _ _
  obtain ⟨initial, initial_nonzero⟩ := (Finset.mem_filter.mp birth_live).2
  have earlier_zero : ∀ index, index < birth → ∀ vector : V index, vector = 0 := by
    intro index earlier vector
    by_contra unequal
    have member : index ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, vector, unequal⟩
    exact (not_le_of_gt earlier) (Finset.min'_le live index member)
  let surviving := Finset.univ.filter fun index =>
    ∃ ordered : birth ≤ index, diagram.map birth index ordered initial ≠ 0
  have birth_survives : birth ∈ surviving := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, le_rfl, ?_⟩
    simpa [diagram.identity] using initial_nonzero
  have surviving_nonempty : surviving.Nonempty := ⟨birth, birth_survives⟩
  let last := surviving.max' surviving_nonempty
  obtain ⟨birth_last, last_nonzero⟩ :=
    (Finset.mem_filter.mp (Finset.max'_mem surviving surviving_nonempty)).2
  let terminal := diagram.map birth last birth_last initial
  have terminal_nonzero : terminal ≠ 0 := last_nonzero
  let terminal_functional := (LinearMap.toSpanSingleton K (V last) terminal).leftInverse
  have terminal_normalized : terminal_functional terminal = 1 := by
    simpa [terminal_functional, LinearMap.toSpanSingleton_apply] using
      LinearMap.leftInverse_apply_of_inj
        (LinearMap.ker_toSpanSingleton K terminal_nonzero) (1 : K)
  let vectors : ∀ index, V index := fun index =>
    if supported : birth ≤ index ∧ index ≤ last then
      diagram.map birth index supported.1 initial else 0
  let functionals : ∀ index, V index →ₗ[K] K := fun index =>
    if supported : birth ≤ index ∧ index ≤ last then
      terminal_functional.comp (diagram.map index last supported.2) else 0
  have unsupported_zero : ∀ index, ¬ (birth ≤ index ∧ index ≤ last) →
      vectors index = 0 ∧ functionals index = 0 := by
    intro index unsupported
    simp [vectors, functionals, unsupported]
  have normalized : ∀ index, birth ≤ index ∧ index ≤ last →
      functionals index (vectors index) = 1 := by
    intro index supported
    simp only [functionals, vectors, dif_pos supported, LinearMap.comp_apply]
    change terminal_functional
      (diagram.map index last supported.2 (diagram.map birth index supported.1 initial)) = 1
    have composite := LinearMap.congr_fun
      (diagram.composition birth index last supported.1 supported.2) initial
    exact (congrArg terminal_functional composite).trans terminal_normalized
  have vector_naturality : ∀ source target (ordered : source ≤ target),
      diagram.map source target ordered (vectors source) =
        if birth ≤ source ∧ target ≤ last then vectors target else 0 := by
    intro source target ordered
    by_cases active : birth ≤ source ∧ target ≤ last
    · have source_supported : birth ≤ source ∧ source ≤ last :=
        ⟨active.1, ordered.trans active.2⟩
      have target_supported : birth ≤ target ∧ target ≤ last :=
        ⟨active.1.trans ordered, active.2⟩
      simp only [if_pos active, vectors, dif_pos source_supported, dif_pos target_supported]
      rw [← LinearMap.comp_apply, diagram.composition]
    · rw [if_neg active]
      by_cases supported : birth ≤ source ∧ source ≤ last
      · have birth_target : birth ≤ target := supported.1.trans ordered
        have vanished : diagram.map birth target birth_target initial = 0 := by
          by_contra unequal
          have member : target ∈ surviving :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, birth_target, unequal⟩
          exact active ⟨supported.1, Finset.le_max' surviving target member⟩
        simp only [vectors, dif_pos supported]
        rw [← LinearMap.comp_apply, diagram.composition]
        exact vanished
      · simp [vectors, supported]
  have functional_naturality : ∀ source target (ordered : source ≤ target),
      (functionals target).comp (diagram.map source target ordered) =
        if birth ≤ source ∧ target ≤ last then functionals source else 0 := by
    intro source target ordered
    by_cases active : birth ≤ source ∧ target ≤ last
    · have source_supported : birth ≤ source ∧ source ≤ last :=
        ⟨active.1, ordered.trans active.2⟩
      have target_supported : birth ≤ target ∧ target ≤ last :=
        ⟨active.1.trans ordered, active.2⟩
      simp only [if_pos active, functionals, dif_pos source_supported, dif_pos target_supported]
      rw [LinearMap.comp_assoc, diagram.composition]
    · rw [if_neg active]
      by_cases supported : birth ≤ target ∧ target ≤ last
      · have source_earlier : source < birth := by
          by_contra earlier
          exact active ⟨le_of_not_gt earlier, supported.2⟩
        ext vector
        rw [earlier_zero source source_earlier vector]
        simp
      · simp [functionals, supported]
  have projector_naturality : ∀ source target (ordered : source ≤ target) vector,
      diagram.map source target ordered (functionals source vector • vectors source) =
        functionals target (diagram.map source target ordered vector) • vectors target := by
    intro source target ordered vector
    have scalar_eq := LinearMap.congr_fun (functional_naturality source target ordered) vector
    rw [map_smul, vector_naturality]
    by_cases active : birth ≤ source ∧ target ≤ last
    · simpa [active] using congrArg (fun scalar : K => scalar • vectors target) scalar_eq.symm
    · simp only [active, if_false, smul_zero]
      simpa [active] using congrArg (fun scalar : K => scalar • vectors target) scalar_eq.symm
  have kernel_naturality : ∀ source target (ordered : source ≤ target) vector,
      functionals source vector = 0 →
        functionals target (diagram.map source target ordered vector) = 0 := by
    intro source target ordered vector in_kernel
    have scalar_eq := LinearMap.congr_fun (functional_naturality source target ordered) vector
    split_ifs at scalar_eq <;> simpa [in_kernel] using scalar_eq
  have projection_identity : ∀ index, ∀ vector ∈ Submodule.span K {vectors index},
      functionals index vector • vectors index = vector := by
    intro index vector member
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp member
    by_cases supported : birth ≤ index ∧ index ≤ last
    · simp [map_smul, normalized index supported]
    · rw [(unsupported_zero index supported).1]
      simp
  have complement : ∀ index,
      IsCompl (Submodule.span K {vectors index}) (LinearMap.ker (functionals index)) := by
    intro index
    let projection : V index →ₗ[K] Submodule.span K {vectors index} :=
      ((functionals index).smulRight (vectors index)).codRestrict _ fun vector =>
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have fixes : ∀ vector : Submodule.span K {vectors index}, projection vector = vector := by
      intro vector
      apply Subtype.ext
      exact projection_identity index vector vector.property
    have kernels : LinearMap.ker projection = LinearMap.ker (functionals index) := by
      ext vector
      change projection vector = 0 ↔ functionals index vector = 0
      rw [Subtype.ext_iff]
      change functionals index vector • vectors index = 0 ↔ functionals index vector = 0
      by_cases supported : birth ≤ index ∧ index ≤ last
      · have vector_nonzero : vectors index ≠ 0 := by
          intro zero
          have impossible := normalized index supported
          simp [zero] at impossible
        simp [smul_eq_zero, vector_nonzero]
      · simp [(unsupported_zero index supported).2]
    simpa only [kernels] using LinearMap.isCompl_of_proj fixes
  let equivalences : ∀ index,
      V index ≃ₗ[K] ((Submodule.span K {vectors index}) × LinearMap.ker (functionals index)) :=
    fun index => (Submodule.prodEquivOfIsCompl
      (Submodule.span K {vectors index}) (LinearMap.ker (functionals index))
      (complement index)).symm
  have coordinates : ∀ index vector,
      ((equivalences index vector).1 : V index) = functionals index vector • vectors index ∧
      ((equivalences index vector).2 : V index) =
        vector - functionals index vector • vectors index := by
    intro index vector
    let split_vector : (Submodule.span K {vectors index}) × LinearMap.ker (functionals index) :=
      (⟨functionals index vector • vectors index,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩,
       ⟨vector - functionals index vector • vectors index, by
         rw [LinearMap.mem_ker]
         by_cases supported : birth ≤ index ∧ index ≤ last
         · simp [map_sub, map_smul, normalized index supported]
         · simp [(unsupported_zero index supported).2]⟩)
    have identified : equivalences index vector = split_vector := by
      apply (Submodule.prodEquivOfIsCompl
        (Submodule.span K {vectors index}) (LinearMap.ker (functionals index))
        (complement index)).symm_apply_eq.mpr
      simp [split_vector]
    rw [identified]
    exact ⟨rfl, rfl⟩
  have dimension_le : ∀ index, finrank K (LinearMap.ker (functionals index)) ≤
      finrank K (V index) := fun index => (LinearMap.ker (functionals index)).finrank_le
  have dimension_strict : finrank K (LinearMap.ker (functionals birth)) <
      finrank K (V birth) := by
    have supported : birth ≤ birth ∧ birth ≤ last := ⟨le_rfl, birth_last⟩
    have vector_nonzero : vectors birth ≠ 0 := by
      intro zero
      have impossible := normalized birth supported
      simp [zero] at impossible
    have dimension := Submodule.finrank_add_eq_of_isCompl (complement birth)
    rw [finrank_span_singleton vector_nonzero] at dimension
    rw [← dimension, Nat.add_comm]
    exact Nat.lt_succ_self _
  refine ⟨birth, last, vectors, functionals, birth_last, earlier_zero, unsupported_zero,
    normalized, vector_naturality, functional_naturality, ⟨equivalences, coordinates⟩,
    projector_naturality, kernel_naturality, ?_⟩
  exact Finset.sum_lt_sum (fun index _ => dimension_le index)
    ⟨birth, Finset.mem_univ _, dimension_strict⟩

end D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalSplit
