/- GID: D5/S3/HomologicalAlgebra/Persistence/RealDecomposition
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition,
     D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness]
   utility: none
   digest: Natural interval classification and fixed same-image quantitative matching. -/

import D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition
import D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

namespace D5.S3.HomologicalAlgebra.Persistence.RealDecomposition

open CategoryTheory Module FiniteIntervalSplit FiniteIntervalDecomposition
  RealIntervalUniqueness

universe u v

variable {K : Type u} [Field K] {n : ℕ}

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_unique_decomposition (diagram : Fin n ⥤ ModuleCat.{v} K)
    [∀ index, FiniteDimensional K (diagram.obj index)] (grid : Fin n ↪o ℝ) :
    let V := fun index => diagram.obj index
    let maps := fun source target (ordered : source ≤ target) =>
      (diagram.map (homOfLE ordered)).hom
    let intervalSpace := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
      Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
        (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
    let intervalArrow := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
        (ordered : source ≤ target) =>
      (((LinearMap.pi fun occurrence : Index =>
          if (target : WithTop ℝ) < family.2 occurrence then
            (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
          (intervalSpace family source)).codRestrict (intervalSpace family target) (by
        classical
        intro coordinates occurrence unsupported
        by_cases survives : (target : WithTop ℝ) < family.2 occurrence
        · have not_born : ¬ family.1 occurrence ≤ source := by
            intro born
            exact unsupported ⟨born.trans ordered, survives⟩
          simpa [survives] using coordinates.property occurrence (by tauto)
        · simp [survives]));
    let intervalSum := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
      ({ obj time := ModuleCat.of K (intervalSpace family time)
         map {source target} arrow :=
           ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
         map_id time := by
           classical
           ext coordinates occurrence
           by_cases survives : (time : WithTop ℝ) < family.2 occurrence
           · simp [intervalArrow, apply_ite, ite_apply, survives]
           · have zero : coordinates.val occurrence = 0 :=
               coordinates.property occurrence (by tauto)
             simp [intervalArrow, apply_ite, ite_apply, survives, zero]
         map_comp {source middle target} first second := by
           classical
           ext coordinates occurrence
           by_cases survives : (target : WithTop ℝ) < family.2 occurrence
           · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
               lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
             simp [intervalArrow, apply_ite, ite_apply, survives, middle_survives]
           · simp [intervalArrow, apply_ite, ite_apply, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
    let prefixedDiagram : WithBot (Fin n) ⥤ ModuleCat.{v} K := {
      obj slot := match slot with
        | ⊥ => ModuleCat.of K (ULift.{v} PUnit.{1})
        | (index : Fin n) => ModuleCat.of K (V index)
      map {source target} arrow := by
        cases source with
        | bot => exact ModuleCat.ofHom 0
        | coe source =>
          cases target with
          | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom arrow))
          | coe target =>
            exact ModuleCat.ofHom
              (maps source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
      map_id index := by
        cases index with
        | bot =>
          ext vector
        | coe index =>
          change ModuleCat.ofHom (maps index index le_rfl) = _
          exact congrArg ModuleCat.ofHom (congrArg ModuleCat.Hom.hom (diagram.map_id index))
      map_comp {source middle target} first second := by
        cases source with
        | bot =>
          have : Subsingleton (ULift.{v} PUnit.{1}) := by
            infer_instance
          ext vector
          have zero : vector = 0 := Subsingleton.elim _ _
          subst vector
          simp
        | coe source =>
          cases middle with
          | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom first))
          | coe middle =>
            cases target with
            | bot => exact False.elim (WithBot.not_coe_le_bot middle (leOfHom second))
            | coe target =>
              change ModuleCat.ofHom _ = ModuleCat.ofHom _ ≫ ModuleCat.ofHom _
              exact diagram.map_comp _ _
    }
    let selectedCell : ℝ → WithBot (Fin n) := fun time => by
      classical
      exact Finset.univ.sup fun index => if grid index ≤ time then
        (index : WithBot (Fin n)) else ⊥
    let selector := (show Monotone (selectedCell) from by
      classical
      intro source target ordered
      apply Finset.sup_mono_fun
      intro index _
      by_cases born : grid index ≤ source
      · simp [born, born.trans ordered]
      · simp [born]).functor
    ∃ (Occurrence : Type v) (finite : Fintype Occurrence),
      letI := finite;
      ∃ (family : (Occurrence → ℝ) × (Occurrence → WithTop ℝ)),
        (∀ occurrence, (family.1 occurrence : WithTop ℝ) < family.2 occurrence) ∧
        ∃ isomorphism : (selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K ≅
            intervalSum family,
          ∀ {Second : Type v} [Fintype Second]
            (second : (Second → ℝ) × (Second → WithTop ℝ))
            (second_positive : ∀ occurrence, (second.1 occurrence : WithTop ℝ) <
              second.2 occurrence),
            ((selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K ≅
              intervalSum second) →
            ∀ birth death,
              Fintype.card {occurrence // family.1 occurrence = birth ∧
                family.2 occurrence = death} =
              Fintype.card {occurrence // second.1 occurrence = birth ∧
                second.2 occurrence = death} := by
  classical
  let V := fun index => diagram.obj index
  let maps := fun source target (ordered : source ≤ target) =>
    (diagram.map (homOfLE ordered)).hom
  let intervalSpace := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
    Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
      (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
  let intervalArrow := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
      (ordered : source ≤ target) =>
    (((LinearMap.pi fun occurrence : Index =>
        if (target : WithTop ℝ) < family.2 occurrence then
          (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
        (intervalSpace family source)).codRestrict (intervalSpace family target) (by
      classical
      intro coordinates occurrence unsupported
      by_cases survives : (target : WithTop ℝ) < family.2 occurrence
      · have not_born : ¬ family.1 occurrence ≤ source := by
          intro born
          exact unsupported ⟨born.trans ordered, survives⟩
        simpa [survives] using coordinates.property occurrence (by tauto)
      · simp [survives]));
  let intervalSum := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
    ({ obj time := ModuleCat.of K (intervalSpace family time)
       map {source target} arrow :=
         ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
       map_id time := by
         classical
         ext coordinates occurrence
         by_cases survives : (time : WithTop ℝ) < family.2 occurrence
         · simp [intervalArrow, apply_ite, ite_apply, survives]
         · have zero : coordinates.val occurrence = 0 :=
             coordinates.property occurrence (by tauto)
           simp [intervalArrow, apply_ite, ite_apply, survives, zero]
       map_comp {source middle target} first second := by
         classical
         ext coordinates occurrence
         by_cases survives : (target : WithTop ℝ) < family.2 occurrence
         · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
             lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
           simp [intervalArrow, apply_ite, ite_apply, survives, middle_survives]
         · simp [intervalArrow, apply_ite, ite_apply, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
  let prefixedDiagram : WithBot (Fin n) ⥤ ModuleCat.{v} K := {
    obj slot := match slot with
      | ⊥ => ModuleCat.of K (ULift.{v} PUnit.{1})
      | (index : Fin n) => ModuleCat.of K (V index)
    map {source target} arrow := by
      cases source with
      | bot => exact ModuleCat.ofHom 0
      | coe source =>
        cases target with
        | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom arrow))
        | coe target =>
          exact ModuleCat.ofHom
            (maps source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
    map_id index := by
      cases index with
      | bot =>
        ext vector
      | coe index =>
        change ModuleCat.ofHom (maps index index le_rfl) = _
        exact congrArg ModuleCat.ofHom (congrArg ModuleCat.Hom.hom (diagram.map_id index))
    map_comp {source middle target} first second := by
      cases source with
      | bot =>
        have : Subsingleton (ULift.{v} PUnit.{1}) := by
          infer_instance
        ext vector
        have zero : vector = 0 := Subsingleton.elim _ _
        subst vector
        simp
      | coe source =>
        cases middle with
        | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom first))
        | coe middle =>
          cases target with
          | bot => exact False.elim (WithBot.not_coe_le_bot middle (leOfHom second))
          | coe target =>
            change ModuleCat.ofHom _ = ModuleCat.ofHom _ ≫ ModuleCat.ofHom _
            exact diagram.map_comp _ _
  }
  let selectedCell : ℝ → WithBot (Fin n) := fun time =>
    Finset.univ.sup fun index => if grid index ≤ time then (index : WithBot (Fin n)) else ⊥
  let selector := (show Monotone (selectedCell) from by
    intro source target ordered
    apply Finset.sup_mono_fun
    intro index _
    by_cases born : grid index ≤ source
    · simp [born, born.trans ordered]
    · simp [born]).functor
  have construction : ∃ (Occurrence : Type v) (finite : Fintype Occurrence),
      letI := finite;
      ∃ family : (Occurrence → ℝ) × (Occurrence → WithTop ℝ),
        (∀ occurrence, (family.1 occurrence : WithTop ℝ) < family.2 occurrence) ∧
        Nonempty ((selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K ≅
          intervalSum family) := by
    obtain ⟨BasisOccurrence, basis_finite, basis_birth, basis_last, basis_vectors,
      basis_basis, basis_ordered, basis_unsupported, basis_basis_vectors,
      basis_naturality⟩ := exists_interval_basis diagram
    letI := basis_finite
    let family : (ULift.{v} BasisOccurrence → ℝ) ×
        (ULift.{v} BasisOccurrence → WithTop ℝ) :=
      ⟨fun occurrence => grid (basis_birth occurrence.down),
        fun occurrence => if next : (basis_last occurrence.down).val + 1 < n then
          (grid ⟨(basis_last occurrence.down).val + 1, next⟩ : WithTop ℝ) else ⊤⟩
    have family_positive : ∀ occurrence, (family.1 occurrence : WithTop ℝ) <
        family.2 occurrence := by
      intro occurrence
      dsimp only [family]
      split_ifs with next
      · apply WithTop.coe_lt_coe.mpr
        apply grid.strictMono
        have ordered := basis_ordered occurrence.down
        change (basis_birth occurrence.down).val < (basis_last occurrence.down).val + 1
        omega
      · exact WithTop.coe_lt_top _
    have born_test : ∀ (index : Fin n) (time : ℝ),
        (index : WithBot (Fin n)) ≤ selectedCell time ↔ grid index ≤ time := by
      intro index time
      change (index : WithBot (Fin n)) ≤ Finset.univ.sup _ ↔ _
      rw [Finset.le_sup_iff (WithBot.bot_lt_coe index)]
      constructor
      · rintro ⟨other, _, below⟩
        by_cases born : grid other ≤ time
        · have ordered : index ≤ other := by simpa [born] using below
          exact (grid.strictMono.monotone ordered).trans born
        · simp [born] at below
      · intro born
        exact ⟨index, Finset.mem_univ _, by simp [born]⟩
    have death_test : ∀ occurrence time,
        selectedCell time ≤ (basis_last occurrence.down : WithBot (Fin n)) ↔
          (time : WithTop ℝ) < family.2 occurrence := by
      intro occurrence time
      by_cases next : (basis_last occurrence.down).val + 1 < n
      · simp only [family, dif_pos next]
        rw [WithTop.coe_lt_coe]
        constructor
        · intro below
          by_contra not_before
          have next_born := (born_test ⟨(basis_last occurrence.down).val + 1, next⟩ time).mpr
            (le_of_not_gt not_before)
          have impossible := WithBot.coe_le_coe.mp (next_born.trans below)
          change (basis_last occurrence.down).val + 1 ≤ (basis_last occurrence.down).val at impossible
          omega
        · intro before
          apply Finset.sup_le
          intro index _
          by_cases born : grid index ≤ time
          · have ordered := grid.strictMono.lt_iff_lt.mp (born.trans_lt before)
            have below : index ≤ basis_last occurrence.down := by
              change index.val ≤ (basis_last occurrence.down).val
              change index.val < (basis_last occurrence.down).val + 1 at ordered
              omega
            simpa [born] using (WithBot.coe_le_coe.mpr below)
          · simp [born]
      · have bounded : selectedCell time ≤ (basis_last occurrence.down : WithBot (Fin n)) := by
          apply Finset.sup_le
          intro index _
          by_cases born : grid index ≤ time
          · have below : index ≤ basis_last occurrence.down := by
              have range := index.isLt
              change index.val ≤ (basis_last occurrence.down).val
              omega
            simpa [born] using (WithBot.coe_le_coe.mpr below)
          · simp [born]
        simp [family, next, bounded]
    have support_test : ∀ occurrence time,
        family.1 occurrence ≤ time ∧ (time : WithTop ℝ) < family.2 occurrence ↔
          (basis_birth occurrence.down : WithBot (Fin n)) ≤ selectedCell time ∧
            selectedCell time ≤ (basis_last occurrence.down : WithBot (Fin n)) := by
      intro occurrence time
      change grid (basis_birth occurrence.down) ≤ time ∧ _ ↔ _
      rw [← born_test, ← death_test]
    have zero_coordinates : ∀ time, selectedCell time = ⊥ →
        Subsingleton (intervalSpace family time) := by
      intro time selected
      refine ⟨fun first second => ?_⟩
      ext occurrence
      have unsupported : ¬ (family.1 occurrence ≤ time ∧
          (time : WithTop ℝ) < family.2 occurrence) := by
        intro supported
        have impossible := (support_test occurrence time).mp supported
        rw [selected] at impossible
        exact WithBot.not_coe_le_bot _ impossible.1
      rw [first.property occurrence unsupported, second.property occurrence unsupported]
    let vector_map : ∀ slot time, intervalSpace family time →ₗ[K]
        ULift.{u} (prefixedDiagram.obj slot) := fun slot time => by
      cases slot with
      | bot => exact 0
      | coe index =>
        change intervalSpace family time →ₗ[K] ULift.{u} (V index)
        exact ULift.moduleEquiv.symm.toLinearMap.comp
          (∑ occurrence : BasisOccurrence,
            LinearMap.smulRight
              ((LinearMap.proj (ULift.up occurrence)).comp (intervalSpace family time).subtype)
              (basis_vectors occurrence index))
    have vector_map_bijective : ∀ slot time, selectedCell time = slot →
        Function.Bijective (vector_map slot time) := by
      intro slot time selected
      cases slot with
      | bot =>
        have := zero_coordinates time selected
        have : Subsingleton (ULift.{u} (prefixedDiagram.obj ⊥)) := by
          change Subsingleton (ULift.{u} (ULift.{v} PUnit))
          infer_instance
        exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun target =>
          ⟨0, Subsingleton.elim _ _⟩⟩
      | coe index =>
        let restriction : intervalSpace family time ≃ₗ[K]
            ({occurrence // basis_birth occurrence ≤ index ∧ index ≤ basis_last occurrence} → K) := {
          toFun := fun coordinates occurrence => coordinates.val (ULift.up occurrence.val)
          invFun := fun coordinates => ⟨fun occurrence =>
            if supported : basis_birth occurrence.down ≤ index ∧ index ≤ basis_last occurrence.down
            then coordinates ⟨occurrence.down, supported⟩ else 0, by
              intro occurrence unsupported
              have absent : ¬ (basis_birth occurrence.down ≤ index ∧
                  index ≤ basis_last occurrence.down) := by
                simpa [selected] using (support_test occurrence time).not.mp unsupported
              simp [absent]⟩
          left_inv := by
            intro coordinates
            ext occurrence
            by_cases supported : basis_birth occurrence.down ≤ index ∧
                index ≤ basis_last occurrence.down
            · simp [supported]
            · have absent : ¬ (family.1 occurrence ≤ time ∧
                  (time : WithTop ℝ) < family.2 occurrence) := by
                apply (support_test occurrence time).not.mpr
                simpa [selected] using supported
              have zero : coordinates.val occurrence = 0 := coordinates.property occurrence absent
              simp [supported, zero]
          right_inv := by intro coordinates; funext occurrence; simp [occurrence.property]
          map_add' := by intro left right; rfl
          map_smul' := by intro scalar coordinates; rfl }
        have reconstruction : ∀ coordinates : intervalSpace family time,
            (∑ occurrence : BasisOccurrence,
              coordinates.val (ULift.up occurrence) • basis_vectors occurrence index) =
            (basis_basis index).equivFun.symm (restriction coordinates) := by
          intro coordinates
          rw [Basis.equivFun_symm_apply]
          simp only [restriction, basis_basis_vectors]
          have complement : (∑ occurrence : {occurrence //
              ¬ (basis_birth occurrence ≤ index ∧ index ≤ basis_last occurrence)},
              coordinates.val (ULift.up occurrence.val) •
                basis_vectors occurrence.val index) = 0 := by
            apply Finset.sum_eq_zero
            intro occurrence _
            simp [basis_unsupported occurrence.val index occurrence.property]
          have total := Fintype.sum_subtype_add_sum_subtype
            (fun occurrence => basis_birth occurrence ≤ index ∧ index ≤ basis_last occurrence)
            (fun occurrence =>
              coordinates.val (ULift.up occurrence) • basis_vectors occurrence index)
          rw [complement, add_zero] at total
          exact total.symm
        have equality : vector_map (index : WithBot (Fin n)) time =
            (restriction.trans ((basis_basis index).equivFun.symm.trans
              ULift.moduleEquiv.symm)).toLinearMap := by
          apply LinearMap.ext
          intro coordinates
          let lifting : V index ≃ₗ[K] ULift.{u} (V index) :=
            (ULift.moduleEquiv (R := K)).symm
          change vector_map (index : WithBot (Fin n)) time coordinates =
            lifting ((basis_basis index).equivFun.symm (restriction coordinates))
          have lifted := congrArg lifting (reconstruction coordinates)
          simpa [vector_map, prefixedDiagram, lifting, LinearEquiv.trans_apply] using lifted
        rw [equality]
        exact (restriction.trans ((basis_basis index).equivFun.symm.trans
          ULift.moduleEquiv.symm)).bijective
    let components : ∀ time, (intervalSum family).obj time ≅
        ((selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K).obj time := fun time =>
      (LinearEquiv.ofBijective (vector_map (selectedCell time) time)
        (vector_map_bijective (selectedCell time) time rfl)).toModuleIso
    have square : ∀ source target (ordered : source ≤ target)
        (source_slot target_slot : WithBot (Fin n)),
        selectedCell source = source_slot → selectedCell target = target_slot →
        ∀ slot_ordered : source_slot ≤ target_slot,
        (vector_map target_slot target).comp (intervalArrow family source target ordered) =
          (ULift.moduleEquiv.symm.toLinearMap.comp
            ((prefixedDiagram.map (homOfLE slot_ordered)).hom.comp
              ULift.moduleEquiv.toLinearMap)).comp (vector_map source_slot source) := by
        intro source target ordered source_slot target_slot source_cell target_cell slot_ordered
        cases source_slot with
        | bot =>
          have := zero_coordinates source source_cell
          apply LinearMap.ext
          intro coordinates
          have zero : coordinates = 0 := Subsingleton.elim _ _
          subst coordinates
          simp
          rfl
        | coe source_index =>
          cases target_slot with
          | bot =>
            exact False.elim (WithBot.not_coe_le_bot _ slot_ordered)
          | coe target_index =>
            apply LinearMap.ext
            intro coordinates
            apply ULift.ext
            simp [prefixedDiagram, vector_map, maps,
              map_sum, map_smul, basis_naturality]
            apply Finset.sum_congr rfl
            intro occurrence _
            by_cases born : basis_birth occurrence ≤ source_index
            · have survival : (target : WithTop ℝ) < family.2 (ULift.up occurrence) ↔
                  target_index ≤ basis_last occurrence := by
                simpa [target_cell] using (death_test (ULift.up occurrence) target).symm
              by_cases survives : target_index ≤ basis_last occurrence <;>
                rw [basis_naturality occurrence source_index target_index
                  (WithBot.coe_le_coe.mp slot_ordered)] <;>
                simp [intervalArrow, apply_ite, ite_apply, born, survives, survival] <;>
                change (0 : ULift.{u} (V target_index)) =
                  coordinates.val (ULift.up occurrence) • (0 : ULift.{u} (V target_index)) <;>
                simp
            · have absent : ¬ (family.1 (ULift.up occurrence) ≤ source ∧
                  (source : WithTop ℝ) < family.2 (ULift.up occurrence)) := by
                rw [support_test, source_cell]
                intro supported
                exact born (WithBot.coe_le_coe.mp supported.1)
              have zero : coordinates.val (ULift.up occurrence) = 0 :=
                coordinates.property (ULift.up occurrence) absent
              simp [intervalArrow, apply_ite, ite_apply, born, zero]
    let isomorphism : intervalSum family ≅
        (selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K :=
      NatIso.ofComponents components (by
        intro source target arrow
        apply ModuleCat.hom_ext
        exact square source target (leOfHom arrow) (selectedCell source) (selectedCell target)
          rfl rfl (leOfHom (selector.map arrow)))
    exact ⟨ULift.{v} BasisOccurrence, inferInstance, family, family_positive,
      ⟨isomorphism.symm⟩⟩
  obtain ⟨Occurrence, finite, first, first_positive, ⟨first_isomorphism⟩⟩ := construction
  letI := finite
  refine ⟨Occurrence, finite, first, first_positive, first_isomorphism, ?_⟩
  intro Second _ second second_positive competing
  let isomorphism : intervalSum first ≅ intervalSum second :=
    first_isomorphism.symm ≪≫ competing
  have equal_ranks : ∀ source target (ordered : source ≤ target),
      finrank K (LinearMap.range (intervalArrow first source target ordered)) =
        finrank K (LinearMap.range (intervalArrow second source target ordered)) := by
    intro source target ordered
    let source_equivalence : intervalSpace first source ≃ₗ[K]
        intervalSpace second source := (isomorphism.app source).toLinearEquiv
    let target_equivalence : intervalSpace first target ≃ₗ[K]
        intervalSpace second target := (isomorphism.app target).toLinearEquiv
    have square := congrArg ModuleCat.Hom.hom (isomorphism.hom.naturality (homOfLE ordered))
    change target_equivalence.toLinearMap.comp (intervalArrow first source target ordered) =
      (intervalArrow second source target ordered).comp source_equivalence.toLinearMap at square
    have transported := congrArg LinearMap.range square
    rw [LinearMap.range_comp, LinearEquiv.range_comp] at transported
    rw [← transported]
    exact (target_equivalence.finrank_map_eq _).symm
  classical
  have image_rank : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ))
      source target (ordered : source ≤ target),
      (finrank K (LinearMap.range (intervalArrow family source target ordered)) : ℤ) =
        ∑ occurrence, if family.1 occurrence ≤ source ∧
          (target : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0 := by
    intro Index _ family source target ordered
    let Live := {occurrence : Index // family.1 occurrence ≤ source ∧
      (target : WithTop ℝ) < family.2 occurrence}
    let lift_coordinates : (Live → K) →ₗ[K] intervalSpace family source := {
      toFun := fun coordinates => ⟨fun occurrence =>
        if supported : family.1 occurrence ≤ source ∧
            (target : WithTop ℝ) < family.2 occurrence then coordinates ⟨occurrence, supported⟩
        else 0, by
          intro occurrence unsupported
          change (if supported : family.1 occurrence ≤ source ∧
            (target : WithTop ℝ) < family.2 occurrence then coordinates ⟨occurrence, supported⟩
            else 0) = 0
          split_ifs with supported
          · exact False.elim (unsupported ⟨supported.1,
              lt_of_le_of_lt (WithTop.coe_le_coe.mpr ordered) supported.2⟩)
          · rfl⟩
      map_add' := by
        intro left right
        ext occurrence
        by_cases supported : family.1 occurrence ≤ source ∧
            (target : WithTop ℝ) < family.2 occurrence <;> simp [supported]
      map_smul' := by intro scalar coordinates; ext occurrence; simp }
    let equivalence : (Live → K) ≃ₗ[K]
        LinearMap.range (intervalArrow family source target ordered) := {
      toFun := fun coordinates =>
        ⟨intervalArrow family source target ordered (lift_coordinates coordinates),
          ⟨lift_coordinates coordinates, rfl⟩⟩
      invFun := fun image occurrence => image.val.val occurrence.val
      left_inv := by
        intro coordinates
        funext occurrence
        simp [intervalArrow, apply_ite, ite_apply, lift_coordinates, occurrence.property]
      right_inv := by
        rintro ⟨image, preimage, rfl⟩
        ext occurrence
        by_cases survives : (target : WithTop ℝ) < family.2 occurrence
        · by_cases born : family.1 occurrence ≤ source
          · simp [intervalArrow, apply_ite, ite_apply, lift_coordinates, survives, born]
          · have zero : preimage.val occurrence = 0 := preimage.property occurrence (by tauto)
            simp [intervalArrow, apply_ite, ite_apply, lift_coordinates, survives, born, zero]
        · simp [intervalArrow, apply_ite, ite_apply, lift_coordinates, survives]
      map_add' := by
        intro left right
        apply Subtype.ext
        change intervalArrow family source target ordered (lift_coordinates (left + right)) =
          intervalArrow family source target ordered (lift_coordinates left) +
            intervalArrow family source target ordered (lift_coordinates right)
        rw [map_add, map_add]
      map_smul' := by
        intro scalar coordinates
        apply Subtype.ext
        change intervalArrow family source target ordered
          (lift_coordinates (scalar • coordinates)) =
          scalar • intervalArrow family source target ordered (lift_coordinates coordinates)
        rw [map_smul, map_smul] }
    rw [← equivalence.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp [Live, Fintype.card_subtype]
  have equal_counts : ∀ source target, source ≤ target →
      (∑ occurrence, if first.1 occurrence ≤ source ∧
        (target : WithTop ℝ) < first.2 occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if second.1 occurrence ≤ source ∧
        (target : WithTop ℝ) < second.2 occurrence then (1 : ℤ) else 0 := by
    intro source target ordered
    rw [← image_rank Occurrence first source target ordered,
      ← image_rank Second second source target ordered, equal_ranks source target ordered]
  intro birth death
  let births := Finset.univ.image first.1 ∪ Finset.univ.image second.1
  let earlier := births.filter fun endpoint => endpoint < birth
  obtain ⟨before, before_lt, birth_cut⟩ : ∃ before : ℝ, before < birth ∧
      ∀ endpoint ∈ births, (endpoint ≤ birth ∧ ¬ endpoint ≤ before ↔ endpoint = birth) := by
    by_cases inhabited : earlier.Nonempty
    · refine ⟨earlier.max' inhabited, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.max'_mem earlier inhabited)).2
      · intro endpoint member
        constructor
        · rintro ⟨below, not_before⟩
          apply le_antisymm below
          by_contra not_above
          have belongs : endpoint ∈ earlier :=
            Finset.mem_filter.mpr ⟨member, lt_of_not_ge not_above⟩
          exact not_before (Finset.le_max' earlier endpoint belongs)
        · intro equal
          subst endpoint
          exact ⟨le_rfl, not_le_of_gt (Finset.mem_filter.mp (Finset.max'_mem earlier inhabited)).2⟩
    · refine ⟨birth - 1, by linarith, ?_⟩
      intro endpoint member
      constructor
      · rintro ⟨below, _⟩
        apply le_antisymm below
        by_contra not_above
        exact inhabited ⟨endpoint, Finset.mem_filter.mpr ⟨member, lt_of_not_ge not_above⟩⟩
      · rintro rfl
        exact ⟨le_rfl, by linarith⟩
  have birth_difference : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ)),
      (∀ occurrence, family.1 occurrence ∈ births) → ∀ time : ℝ,
      (∑ occurrence, if family.1 occurrence ≤ birth ∧
        (time : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0) -
      (∑ occurrence, if family.1 occurrence ≤ before ∧
        (time : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if family.1 occurrence = birth ∧
        (time : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0 := by
    intro Index _ family members time
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro occurrence _
    have cutoff := birth_cut (family.1 occurrence) (members occurrence)
    have monotone : family.1 occurrence ≤ before → family.1 occurrence ≤ birth :=
      fun below => below.trans before_lt.le
    by_cases survives : (time : WithTop ℝ) < family.2 occurrence
    · by_cases below : family.1 occurrence ≤ before
      · have not_equal : family.1 occurrence ≠ birth := by
          intro equal
          exact (cutoff.mpr equal).2 below
        simp [survives, below, monotone below, not_equal]
      · by_cases born : family.1 occurrence ≤ birth
        · have equal := cutoff.mp ⟨born, below⟩
          simp [survives, equal, not_le_of_gt before_lt]
        · have not_equal : family.1 occurrence ≠ birth := fun equal => born (equal ▸ le_rfl)
          simp [survives, below, born, not_equal]
    · simp [survives]
  have equal_birth_counts : ∀ time, birth ≤ time →
      (∑ occurrence, if first.1 occurrence = birth ∧
        (time : WithTop ℝ) < first.2 occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if second.1 occurrence = birth ∧
        (time : WithTop ℝ) < second.2 occurrence then (1 : ℤ) else 0 := by
    intro time ordered
    rw [← birth_difference Occurrence first (fun occurrence =>
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩)),
      ← birth_difference Second second (fun occurrence =>
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩)),
      equal_counts birth time ordered, equal_counts before time (before_lt.le.trans ordered)]
  let deaths := (Finset.univ.filter fun occurrence => first.2 occurrence ≠ ⊤).image
      (fun occurrence => (first.2 occurrence).untopD 0) ∪
    (Finset.univ.filter fun occurrence => second.2 occurrence ≠ ⊤).image
      (fun occurrence => (second.2 occurrence).untopD 0)
  have first_death_member : ∀ occurrence (endpoint : ℝ),
      first.2 occurrence = (endpoint : WithTop ℝ) →
      endpoint ∈ deaths := by
    intro occurrence endpoint equal
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨occurrence, by simp [equal], by simp [equal]⟩
  have second_death_member : ∀ occurrence (endpoint : ℝ),
      second.2 occurrence = (endpoint : WithTop ℝ) →
      endpoint ∈ deaths := by
    intro occurrence endpoint equal
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨occurrence, by simp [equal], by simp [equal]⟩
  have multiplicity_sum : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ)),
      (Fintype.card {occurrence //
        family.1 occurrence = birth ∧ family.2 occurrence = death} : ℤ) =
      ∑ occurrence, if family.1 occurrence = birth ∧ family.2 occurrence = death
        then (1 : ℤ) else 0 := by
    intro Index _ family
    simp [Fintype.card_subtype]
  apply Int.ofNat_inj.mp
  rw [multiplicity_sum Occurrence first, multiplicity_sum Second second]
  induction death using WithTop.recTopCoe with
  | top =>
    let endpoints := deaths ∪ {birth}
    have inhabited : endpoints.Nonempty := ⟨birth, by simp [endpoints]⟩
    let time := endpoints.max' inhabited
    have birth_le : birth ≤ time := Finset.le_max' _ _ (by simp [endpoints])
    have tail : ∀ endpoint ∈ deaths, endpoint ≤ time := fun endpoint member =>
      Finset.le_max' _ _ (Finset.mem_union_left _ member)
    have essential : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ)),
        (∀ occurrence (endpoint : ℝ),
          family.2 occurrence = (endpoint : WithTop ℝ) → endpoint ∈ deaths) →
        (∑ occurrence, if family.1 occurrence = birth ∧
          (time : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0) =
        ∑ occurrence, if family.1 occurrence = birth ∧ family.2 occurrence = ⊤
          then (1 : ℤ) else 0 := by
      intro Index _ family members
      apply Finset.sum_congr rfl
      intro occurrence _
      rcases eq_or_ne (family.2 occurrence) ⊤ with infinite | finite
      · simp [infinite]
      · obtain ⟨endpoint, equal⟩ := WithTop.ne_top_iff_exists.mp finite
        have below := tail endpoint (members occurrence endpoint equal.symm)
        simp [← equal, not_lt_of_ge below]
    rw [← essential Occurrence first first_death_member, ← essential Second second second_death_member]
    exact equal_birth_counts time birth_le
  | coe endpoint =>
    by_cases positive : birth < endpoint
    · let earlier_deaths := (deaths.filter fun value => value < endpoint) ∪ {birth}
      have inhabited : earlier_deaths.Nonempty := ⟨birth, by simp [earlier_deaths]⟩
      let time := earlier_deaths.max' inhabited
      have birth_le : birth ≤ time := Finset.le_max' _ _ (by simp [earlier_deaths])
      have time_lt : time < endpoint := by
        rcases Finset.mem_union.mp (Finset.max'_mem earlier_deaths inhabited) with member | member
        · exact (Finset.mem_filter.mp member).2
        · have equal : time = birth := Finset.mem_singleton.mp member
          rw [equal]
          exact positive
      have death_cut : ∀ value ∈ deaths,
          (time < value ∧ ¬ endpoint < value ↔ value = endpoint) := by
        intro value member
        constructor
        · rintro ⟨above, below⟩
          apply le_antisymm (le_of_not_gt below)
          by_contra not_above
          have belongs : value ∈ earlier_deaths := Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨member, lt_of_not_ge not_above⟩)
          exact (not_le_of_gt above) (Finset.le_max' _ _ belongs)
        · rintro rfl
          exact ⟨time_lt, lt_irrefl _⟩
      have death_difference : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ)),
          (∀ occurrence (value : ℝ),
            family.2 occurrence = (value : WithTop ℝ) → value ∈ deaths) →
          (∑ occurrence, if family.1 occurrence = birth ∧
            (time : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0) -
          (∑ occurrence, if family.1 occurrence = birth ∧
            (endpoint : WithTop ℝ) < family.2 occurrence then (1 : ℤ) else 0) =
          ∑ occurrence, if family.1 occurrence = birth ∧
            family.2 occurrence = (endpoint : WithTop ℝ) then (1 : ℤ) else 0 := by
        intro Index _ family members
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro occurrence _
        rcases eq_or_ne (family.2 occurrence) ⊤ with infinite | finite
        · simp [infinite]
        · obtain ⟨value, equal⟩ := WithTop.ne_top_iff_exists.mp finite
          have cutoff := death_cut value (members occurrence value equal.symm)
          have monotone : endpoint < value → time < value := fun above => time_lt.trans above
          simp only [← equal, WithTop.coe_lt_coe, WithTop.coe_inj]
          split_ifs <;> simp_all
      rw [← death_difference Occurrence first first_death_member,
        ← death_difference Second second second_death_member,
        equal_birth_counts time birth_le, equal_birth_counts endpoint positive.le]
    · have empty : ∀ (Index : Type v) [Fintype Index] (family : (Index → ℝ) × (Index → WithTop ℝ))
          (family_positive : ∀ occurrence, (family.1 occurrence : WithTop ℝ) <
            family.2 occurrence),
          (∑ occurrence, if family.1 occurrence = birth ∧
            family.2 occurrence = (endpoint : WithTop ℝ) then (1 : ℤ) else 0) = 0 := by
        intro Index _ family family_positive
        apply Finset.sum_eq_zero
        intro occurrence _
        have invalid : ¬ (family.1 occurrence = birth ∧
            family.2 occurrence = (endpoint : WithTop ℝ)) := by
          rintro ⟨born, died⟩
          have length := family_positive occurrence
          rw [born, died, WithTop.coe_lt_coe] at length
          exact positive length
        simp [invalid]
      rw [empty Occurrence first first_positive, empty Second second second_positive]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_quantitative_image_matching {Source Target : Type v}
    [Fintype Source] [Fintype Target]
    (sourceFamily : (Source → ℝ) × (Source → WithTop ℝ))
    (targetFamily : (Target → ℝ) × (Target → WithTop ℝ))
    (source_positive : ∀ occurrence, (sourceFamily.1 occurrence : WithTop ℝ) <
      sourceFamily.2 occurrence)
    (target_positive : ∀ occurrence, (targetFamily.1 occurrence : WithTop ℝ) <
      targetFamily.2 occurrence) :
    let intervalSpace := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
      Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
        (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
    let intervalArrow := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
        (ordered : source ≤ target) =>
      (((LinearMap.pi fun occurrence : Index =>
          if (target : WithTop ℝ) < family.2 occurrence then
            (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
          (intervalSpace family source)).codRestrict (intervalSpace family target) (by
        classical
        intro coordinates occurrence unsupported
        by_cases survives : (target : WithTop ℝ) < family.2 occurrence
        · have not_born : ¬ family.1 occurrence ≤ source := by
            intro born
            exact unsupported ⟨born.trans ordered, survives⟩
          simpa [survives] using coordinates.property occurrence (by tauto)
        · simp [survives]));
    let intervalSum := fun {Index : Type v}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
      ({ obj time := ModuleCat.of K (intervalSpace family time)
         map {source target} arrow :=
           ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
         map_id time := by
           classical
           ext coordinates occurrence
           by_cases survives : (time : WithTop ℝ) < family.2 occurrence
           · simp [intervalArrow, survives]
           · have zero : coordinates.val occurrence = 0 :=
               coordinates.property occurrence (by tauto)
             simp [intervalArrow, survives, zero]
         map_comp {source middle target} first second := by
           classical
           ext coordinates occurrence
           by_cases survives : (target : WithTop ℝ) < family.2 occurrence
           · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
               lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
             simp [intervalArrow, survives, middle_survives]
           · simp [intervalArrow, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
    let intervalSpaceLarge := fun {Index : Type (max u v)}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
      Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
        (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
    let intervalArrowLarge := fun {Index : Type (max u v)}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
        (ordered : source ≤ target) =>
      (((LinearMap.pi fun occurrence : Index =>
          if (target : WithTop ℝ) < family.2 occurrence then
            (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
          (intervalSpaceLarge family source)).codRestrict (intervalSpaceLarge family target) (by
        classical
        intro coordinates occurrence unsupported
        by_cases survives : (target : WithTop ℝ) < family.2 occurrence
        · have not_born : ¬ family.1 occurrence ≤ source := by
            intro born
            exact unsupported ⟨born.trans ordered, survives⟩
          simpa [survives] using coordinates.property occurrence (by tauto)
        · simp [survives]));
    let intervalSumLarge := fun {Index : Type (max u v)}
        (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
      ({ obj time := ModuleCat.of K (intervalSpaceLarge family time)
         map {source target} arrow :=
           ModuleCat.ofHom (intervalArrowLarge family source target (leOfHom arrow))
         map_id time := by
           classical
           ext coordinates occurrence
           by_cases survives : (time : WithTop ℝ) < family.2 occurrence
           · simp [intervalArrowLarge, survives]
           · have zero : coordinates.val occurrence = 0 :=
               coordinates.property occurrence (by tauto)
             simp [intervalArrowLarge, survives, zero]
         map_comp {source middle target} first second := by
           classical
           ext coordinates occurrence
           by_cases survives : (target : WithTop ℝ) < family.2 occurrence
           · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
               lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
             simp [intervalArrowLarge, survives, middle_survives]
           · simp [intervalArrowLarge, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
    ∀ morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily,
      ∃ (Occurrence : Type v) (finite : Fintype Occurrence),
        letI := finite;
        ∃ family : (Occurrence → ℝ) × (Occurrence → WithTop ℝ),
          (∀ occurrence, (family.1 occurrence : WithTop ℝ) < family.2 occurrence) ∧
          ∃ imageIso : Abelian.image morphism ≅ intervalSum family,
            (∀ time, Function.Surjective
              ((Abelian.factorThruImage morphism ≫ imageIso.hom).app time).hom) ∧
            (∀ time, Function.Injective
              ((imageIso.inv ≫ Abelian.image.ι morphism).app time).hom) ∧
            (Abelian.factorThruImage morphism ≫ imageIso.hom) ≫
              (imageIso.inv ≫ Abelian.image.ι morphism) = morphism ∧
            ∃ (sourceBirthEnumeration : ∀ birth, Fin (Fintype.card
                {occurrence // sourceFamily.1 occurrence = birth}) ≃
                  {occurrence // sourceFamily.1 occurrence = birth})
              (imageBirthEnumeration : ∀ birth, Fin (Fintype.card
                {occurrence // family.1 occurrence = birth}) ≃
                  {occurrence // family.1 occurrence = birth})
              (imageDeathEnumeration : ∀ death, Fin (Fintype.card
                {occurrence // family.2 occurrence = death}) ≃
                  {occurrence // family.2 occurrence = death})
              (targetDeathEnumeration : ∀ death, Fin (Fintype.card
                {occurrence // targetFamily.2 occurrence = death}) ≃
                  {occurrence // targetFamily.2 occurrence = death}),
              (∀ birth, Antitone fun ordinal =>
                sourceFamily.2 (sourceBirthEnumeration birth ordinal).val) ∧
              (∀ birth, Antitone fun ordinal =>
                family.2 (imageBirthEnumeration birth ordinal).val) ∧
              (∀ death, Monotone fun ordinal =>
                family.1 (imageDeathEnumeration death ordinal).val) ∧
              (∀ death, Monotone fun ordinal =>
                targetFamily.1 (targetDeathEnumeration death ordinal).val) ∧
              ∃ (sourceEmbedding : Occurrence ↪ Source) (targetEmbedding : Occurrence ↪ Target),
                (∀ occurrence, family.2 occurrence ≤ sourceFamily.2 (sourceEmbedding occurrence) ∧
                  ∃ sameBirth : sourceFamily.1 (sourceEmbedding occurrence) = family.1 occurrence,
                    ((sourceBirthEnumeration (family.1 occurrence)).symm
                      ⟨sourceEmbedding occurrence, sameBirth⟩).val =
                    ((imageBirthEnumeration (family.1 occurrence)).symm ⟨occurrence, rfl⟩).val) ∧
                (∀ occurrence, targetFamily.1 (targetEmbedding occurrence) ≤ family.1 occurrence ∧
                  ∃ sameDeath : targetFamily.2 (targetEmbedding occurrence) = family.2 occurrence,
                    ((targetDeathEnumeration (family.2 occurrence)).symm
                      ⟨targetEmbedding occurrence, sameDeath⟩).val =
                    ((imageDeathEnumeration (family.2 occurrence)).symm ⟨occurrence, rfl⟩).val) ∧
                ∀ (etaK etaC : ℝ) (kernel_nonnegative : 0 ≤ etaK)
                  (cokernel_nonnegative : 0 ≤ etaC)
                  (kernel_trivial : ∀ time, LinearMap.ker (morphism.app time).hom ≤
                    LinearMap.ker (intervalArrow sourceFamily time (time + etaK) (by linarith)))
                  (cokernel_trivial : ∀ time,
                    LinearMap.range (intervalArrow targetFamily time (time + etaC) (by linarith)) ≤
                      LinearMap.range (morphism.app (time + etaC)).hom),
                  (∀ occurrence,
                    targetFamily.1 (targetEmbedding occurrence) ≤ family.1 occurrence ∧
                    family.1 occurrence = sourceFamily.1 (sourceEmbedding occurrence) ∧
                    family.1 occurrence ≤ targetFamily.1 (targetEmbedding occurrence) + etaC ∧
                    family.2 occurrence = targetFamily.2 (targetEmbedding occurrence) ∧
                    family.2 occurrence ≤ sourceFamily.2 (sourceEmbedding occurrence) ∧
                    WithTop.map (fun endpoint : ℝ => endpoint - etaK)
                      (sourceFamily.2 (sourceEmbedding occurrence)) ≤ family.2 occurrence) ∧
                  (∀ occurrence (sourceDeath imageDeath : ℝ),
                    sourceFamily.2 (sourceEmbedding occurrence) = (sourceDeath : WithTop ℝ) →
                    family.2 occurrence = (imageDeath : WithTop ℝ) →
                    sourceDeath ≤ imageDeath + etaK) ∧
                  (∀ occurrence, ((sourceFamily.1 occurrence + etaK : ℝ) : WithTop ℝ) <
                    sourceFamily.2 occurrence → ∃ imageOccurrence,
                      sourceEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, ((targetFamily.1 occurrence + etaC : ℝ) : WithTop ℝ) <
                    targetFamily.2 occurrence → ∃ imageOccurrence,
                      targetEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, sourceFamily.2 (sourceEmbedding occurrence) = ⊤ ↔
                    family.2 occurrence = ⊤) ∧
                  (∀ occurrence, sourceFamily.2 occurrence = ⊤ →
                    ∃ imageOccurrence, sourceEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, targetFamily.2 occurrence = ⊤ →
                    ∃ imageOccurrence, targetEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence (death : ℝ), sourceFamily.2 occurrence = (death : WithTop ℝ) →
                    (¬ ∃ imageOccurrence, sourceEmbedding imageOccurrence = occurrence) →
                      death - sourceFamily.1 occurrence ≤ etaK) ∧
                  (∀ occurrence (death : ℝ), targetFamily.2 occurrence = (death : WithTop ℝ) →
                    (¬ ∃ imageOccurrence, targetEmbedding imageOccurrence = occurrence) →
                      death - targetFamily.1 occurrence ≤ etaC) ∧
                  (etaK = 0 → Function.Surjective sourceEmbedding ∧
                    ∀ occurrence, sourceFamily.2 (sourceEmbedding occurrence) = family.2 occurrence) ∧
                  (etaC = 0 → Function.Surjective targetEmbedding ∧
                    ∀ occurrence, family.1 occurrence = targetFamily.1 (targetEmbedding occurrence)) := by
  classical
  let intervalSpace := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
    Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
      (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
  let intervalArrow := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
      (ordered : source ≤ target) =>
    (((LinearMap.pi fun occurrence : Index =>
        if (target : WithTop ℝ) < family.2 occurrence then
          (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
        (intervalSpace family source)).codRestrict (intervalSpace family target) (by
      classical
      intro coordinates occurrence unsupported
      by_cases survives : (target : WithTop ℝ) < family.2 occurrence
      · have not_born : ¬ family.1 occurrence ≤ source := by
          intro born
          exact unsupported ⟨born.trans ordered, survives⟩
        simpa [survives] using coordinates.property occurrence (by tauto)
      · simp [survives]));
  let intervalSum := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
    ({ obj time := ModuleCat.of K (intervalSpace family time)
       map {source target} arrow :=
         ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
       map_id time := by
         classical
         ext coordinates occurrence
         by_cases survives : (time : WithTop ℝ) < family.2 occurrence
         · simp [intervalArrow, survives]
         · have zero : coordinates.val occurrence = 0 :=
             coordinates.property occurrence (by tauto)
           simp [intervalArrow, survives, zero]
       map_comp {source middle target} first second := by
         classical
         ext coordinates occurrence
         by_cases survives : (target : WithTop ℝ) < family.2 occurrence
         · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
             lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
           simp [intervalArrow, survives, middle_survives]
         · simp [intervalArrow, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
  let intervalSpaceLarge := fun {Index : Type (max u v)}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (time : ℝ) =>
    Submodule.pi {occurrence | ¬ (family.1 occurrence ≤ time ∧
      (time : WithTop ℝ) < family.2 occurrence)} (fun _ => (⊥ : Submodule K K));
  let intervalArrowLarge := fun {Index : Type (max u v)}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) (source target : ℝ)
      (ordered : source ≤ target) =>
    (((LinearMap.pi fun occurrence : Index =>
        if (target : WithTop ℝ) < family.2 occurrence then
          (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0).domRestrict
        (intervalSpaceLarge family source)).codRestrict (intervalSpaceLarge family target) (by
      classical
      intro coordinates occurrence unsupported
      by_cases survives : (target : WithTop ℝ) < family.2 occurrence
      · have not_born : ¬ family.1 occurrence ≤ source := by
          intro born
          exact unsupported ⟨born.trans ordered, survives⟩
        simpa [survives] using coordinates.property occurrence (by tauto)
      · simp [survives]));
  let intervalSumLarge := fun {Index : Type (max u v)}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
    ({ obj time := ModuleCat.of K (intervalSpaceLarge family time)
       map {source target} arrow :=
         ModuleCat.ofHom (intervalArrowLarge family source target (leOfHom arrow))
       map_id time := by
         classical
         ext coordinates occurrence
         by_cases survives : (time : WithTop ℝ) < family.2 occurrence
         · simp [intervalArrowLarge, survives]
         · have zero : coordinates.val occurrence = 0 :=
             coordinates.property occurrence (by tauto)
           simp [intervalArrowLarge, survives, zero]
       map_comp {source middle target} first second := by
         classical
         ext coordinates occurrence
         by_cases survives : (target : WithTop ℝ) < family.2 occurrence
         · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
             lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
           simp [intervalArrowLarge, survives, middle_survives]
         · simp [intervalArrowLarge, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
  change ∀ morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily,
        ∃ (Occurrence : Type v) (finite : Fintype Occurrence),
          letI := finite;
          ∃ family : (Occurrence → ℝ) × (Occurrence → WithTop ℝ),
            (∀ occurrence, (family.1 occurrence : WithTop ℝ) < family.2 occurrence) ∧
            ∃ imageIso : Abelian.image morphism ≅ intervalSum family,
              (∀ time, Function.Surjective
                ((Abelian.factorThruImage morphism ≫ imageIso.hom).app time).hom) ∧
              (∀ time, Function.Injective
                ((imageIso.inv ≫ Abelian.image.ι morphism).app time).hom) ∧
              (Abelian.factorThruImage morphism ≫ imageIso.hom) ≫
                (imageIso.inv ≫ Abelian.image.ι morphism) = morphism ∧
            ∃ (sourceBirthEnumeration : ∀ birth, Fin (Fintype.card
                {occurrence // sourceFamily.1 occurrence = birth}) ≃
                  {occurrence // sourceFamily.1 occurrence = birth})
              (imageBirthEnumeration : ∀ birth, Fin (Fintype.card
                {occurrence // family.1 occurrence = birth}) ≃
                  {occurrence // family.1 occurrence = birth})
              (imageDeathEnumeration : ∀ death, Fin (Fintype.card
                {occurrence // family.2 occurrence = death}) ≃
                  {occurrence // family.2 occurrence = death})
              (targetDeathEnumeration : ∀ death, Fin (Fintype.card
                {occurrence // targetFamily.2 occurrence = death}) ≃
                  {occurrence // targetFamily.2 occurrence = death}),
              (∀ birth, Antitone fun ordinal =>
                sourceFamily.2 (sourceBirthEnumeration birth ordinal).val) ∧
              (∀ birth, Antitone fun ordinal =>
                family.2 (imageBirthEnumeration birth ordinal).val) ∧
              (∀ death, Monotone fun ordinal =>
                family.1 (imageDeathEnumeration death ordinal).val) ∧
              (∀ death, Monotone fun ordinal =>
                targetFamily.1 (targetDeathEnumeration death ordinal).val) ∧
              ∃ (sourceEmbedding : Occurrence ↪ Source) (targetEmbedding : Occurrence ↪ Target),
                (∀ occurrence, family.2 occurrence ≤ sourceFamily.2 (sourceEmbedding occurrence) ∧
                  ∃ sameBirth : sourceFamily.1 (sourceEmbedding occurrence) = family.1 occurrence,
                    ((sourceBirthEnumeration (family.1 occurrence)).symm
                      ⟨sourceEmbedding occurrence, sameBirth⟩).val =
                    ((imageBirthEnumeration (family.1 occurrence)).symm ⟨occurrence, rfl⟩).val) ∧
                (∀ occurrence, targetFamily.1 (targetEmbedding occurrence) ≤ family.1 occurrence ∧
                  ∃ sameDeath : targetFamily.2 (targetEmbedding occurrence) = family.2 occurrence,
                    ((targetDeathEnumeration (family.2 occurrence)).symm
                      ⟨targetEmbedding occurrence, sameDeath⟩).val =
                    ((imageDeathEnumeration (family.2 occurrence)).symm ⟨occurrence, rfl⟩).val) ∧
                ∀ (etaK etaC : ℝ) (kernel_nonnegative : 0 ≤ etaK)
                  (cokernel_nonnegative : 0 ≤ etaC)
                  (kernel_trivial : ∀ time, LinearMap.ker (morphism.app time).hom ≤
                    LinearMap.ker (intervalArrow sourceFamily time (time + etaK) (by linarith)))
                  (cokernel_trivial : ∀ time,
                    LinearMap.range (intervalArrow targetFamily time (time + etaC) (by linarith)) ≤
                      LinearMap.range (morphism.app (time + etaC)).hom),
                  (∀ occurrence,
                    targetFamily.1 (targetEmbedding occurrence) ≤ family.1 occurrence ∧
                    family.1 occurrence = sourceFamily.1 (sourceEmbedding occurrence) ∧
                    family.1 occurrence ≤ targetFamily.1 (targetEmbedding occurrence) + etaC ∧
                    family.2 occurrence = targetFamily.2 (targetEmbedding occurrence) ∧
                    family.2 occurrence ≤ sourceFamily.2 (sourceEmbedding occurrence) ∧
                    WithTop.map (fun endpoint : ℝ => endpoint - etaK)
                      (sourceFamily.2 (sourceEmbedding occurrence)) ≤ family.2 occurrence) ∧
                  (∀ occurrence (sourceDeath imageDeath : ℝ),
                    sourceFamily.2 (sourceEmbedding occurrence) = (sourceDeath : WithTop ℝ) →
                    family.2 occurrence = (imageDeath : WithTop ℝ) →
                    sourceDeath ≤ imageDeath + etaK) ∧
                  (∀ occurrence, ((sourceFamily.1 occurrence + etaK : ℝ) : WithTop ℝ) <
                    sourceFamily.2 occurrence → ∃ imageOccurrence,
                      sourceEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, ((targetFamily.1 occurrence + etaC : ℝ) : WithTop ℝ) <
                    targetFamily.2 occurrence → ∃ imageOccurrence,
                      targetEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, sourceFamily.2 (sourceEmbedding occurrence) = ⊤ ↔
                    family.2 occurrence = ⊤) ∧
                  (∀ occurrence, sourceFamily.2 occurrence = ⊤ →
                    ∃ imageOccurrence, sourceEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence, targetFamily.2 occurrence = ⊤ →
                    ∃ imageOccurrence, targetEmbedding imageOccurrence = occurrence) ∧
                  (∀ occurrence (death : ℝ), sourceFamily.2 occurrence = (death : WithTop ℝ) →
                    (¬ ∃ imageOccurrence, sourceEmbedding imageOccurrence = occurrence) →
                      death - sourceFamily.1 occurrence ≤ etaK) ∧
                  (∀ occurrence (death : ℝ), targetFamily.2 occurrence = (death : WithTop ℝ) →
                    (¬ ∃ imageOccurrence, targetEmbedding imageOccurrence = occurrence) →
                      death - targetFamily.1 occurrence ≤ etaC) ∧
                  (etaK = 0 → Function.Surjective sourceEmbedding ∧
                    ∀ occurrence, sourceFamily.2 (sourceEmbedding occurrence) = family.2 occurrence) ∧
                  (etaC = 0 → Function.Surjective targetEmbedding ∧
                    ∀ occurrence, family.1 occurrence = targetFamily.1 (targetEmbedding occurrence))
  intro morphism
  let critical := Finset.univ.image sourceFamily.1 ∪ Finset.univ.image targetFamily.1 ∪
    (Finset.univ.filter fun occurrence => sourceFamily.2 occurrence ≠ ⊤).image
      (fun occurrence => (sourceFamily.2 occurrence).untopD 0) ∪
    (Finset.univ.filter fun occurrence => targetFamily.2 occurrence ≠ ⊤).image
      (fun occurrence => (targetFamily.2 occurrence).untopD 0)
  let n := critical.card
  let grid : Fin n ↪o ℝ := critical.orderEmbOfFin rfl
  let selectedCell : ℝ → WithBot (Fin n) := fun time =>
    Finset.univ.sup fun index => if grid index ≤ time then
      (index : WithBot (Fin n)) else ⊥
  have selected_monotone : Monotone selectedCell := by
    intro source target ordered
    apply Finset.sup_mono_fun
    intro index _
    by_cases born : grid index ≤ source
    · simp [born, born.trans ordered]
    · simp [born]
  have born_test : ∀ (index : Fin n) (time : ℝ),
      (index : WithBot (Fin n)) ≤ selectedCell time ↔ grid index ≤ time := by
    intro index time
    change (index : WithBot (Fin n)) ≤ Finset.univ.sup _ ↔ _
    rw [Finset.le_sup_iff (WithBot.bot_lt_coe index)]
    constructor
    · rintro ⟨other, _, below⟩
      by_cases born : grid other ≤ time
      · have ordered : index ≤ other := by simpa [born] using below
        exact (grid.monotone ordered).trans born
      · simp [born] at below
    · intro born
      exact ⟨index, Finset.mem_univ _, by simp [born]⟩
  have endpoint_index : ∀ endpoint ∈ critical, ∃ index, grid index = endpoint := by
    intro endpoint member
    have in_range : endpoint ∈ Set.range grid := by
      rw [Finset.range_orderEmbOfFin]
      exact member
    exact in_range
  have endpoint_cell : ∀ (time : ℝ) (index : Fin n), selectedCell time = (index : WithBot (Fin n)) →
      ∀ endpoint ∈ critical, endpoint ≤ time ↔ endpoint ≤ grid index := by
    intro time index selected endpoint member
    obtain ⟨other, rfl⟩ := endpoint_index endpoint member
    constructor
    · intro before
      have below := (born_test other time).mpr before
      rw [selected] at below
      exact grid.monotone (WithBot.coe_le_coe.mp below)
    · intro before
      have sampled_before := (born_test index time).mp (by rw [selected])
      exact before.trans sampled_before
  have source_birth_member : ∀ occurrence, sourceFamily.1 occurrence ∈ critical := by
    intro occurrence
    simp [critical]
  have target_birth_member : ∀ occurrence, targetFamily.1 occurrence ∈ critical := by
    intro occurrence
    simp [critical]
  have source_death_member : ∀ occurrence (endpoint : ℝ),
      sourceFamily.2 occurrence = (endpoint : WithTop ℝ) → endpoint ∈ critical := by
    intro occurrence endpoint died
    have finite : sourceFamily.2 occurrence ≠ ⊤ := by simp [died]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨occurrence,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, finite⟩, by simp [died]⟩
  have target_death_member : ∀ occurrence (endpoint : ℝ),
      targetFamily.2 occurrence = (endpoint : WithTop ℝ) → endpoint ∈ critical := by
    intro occurrence endpoint died
    have finite : targetFamily.2 occurrence ≠ ⊤ := by simp [died]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨occurrence,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, finite⟩, by simp [died]⟩
  have cell_support : ∀ {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)),
      (∀ occurrence, family.1 occurrence ∈ critical) →
      (∀ occurrence (endpoint : ℝ), family.2 occurrence = (endpoint : WithTop ℝ) →
        endpoint ∈ critical) →
      ∀ (time : ℝ) (index : Fin n), selectedCell time = (index : WithBot (Fin n)) →
        ∀ occurrence,
          (family.1 occurrence ≤ grid index ∧ (grid index : WithTop ℝ) <
            family.2 occurrence) ↔
          (family.1 occurrence ≤ time ∧ (time : WithTop ℝ) < family.2 occurrence) := by
    intro Index family births deaths time index selected occurrence
    have birth := endpoint_cell time index selected _ (births occurrence)
    have death : (grid index : WithTop ℝ) < family.2 occurrence ↔
        (time : WithTop ℝ) < family.2 occurrence := by
      cases died : family.2 occurrence with
      | top => simp
      | coe endpoint =>
        have cutoff := endpoint_cell time index selected endpoint
          (deaths occurrence endpoint died)
        simpa only [WithTop.coe_lt_coe, not_le] using (not_congr cutoff).symm
    exact and_congr birth.symm death
  have cell_arrow_bijective : ∀ {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) source target
      (ordered : source ≤ target),
      (∀ occurrence, (family.1 occurrence ≤ source ∧
          (source : WithTop ℝ) < family.2 occurrence) ↔
        (family.1 occurrence ≤ target ∧ (target : WithTop ℝ) < family.2 occurrence)) →
      Function.Bijective (intervalArrow family source target ordered) := by
    intro Index family source target ordered supported
    have spaces : intervalSpace family source = intervalSpace family target := by
      ext coordinates
      simp only [intervalSpace, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
      simp_rw [supported]
    let equivalence := LinearEquiv.ofEq (intervalSpace family source)
      (intervalSpace family target) spaces
    have actual : intervalArrow family source target ordered = equivalence.toLinearMap := by
      ext coordinates occurrence
      by_cases survives : (target : WithTop ℝ) < family.2 occurrence
      · simp [intervalArrow, equivalence, survives]
      · have absent : ¬ (family.1 occurrence ≤ source ∧
            (source : WithTop ℝ) < family.2 occurrence) := by
          rw [supported]
          exact fun active => survives active.2
        have zero : coordinates.val occurrence = 0 := coordinates.property occurrence absent
        simp [intervalArrow, equivalence, survives, zero]
    rw [actual]
    exact equivalence.bijective
  let image := Abelian.image morphism
  let epi := Abelian.factorThruImage morphism
  let mono := Abelian.image.ι morphism
  have epi_surjective : ∀ time, Function.Surjective (epi.app time).hom := by
    intro time
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have mono_injective : ∀ time, Function.Injective (mono.app time).hom := by
    intro time
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  letI : ∀ time, FiniteDimensional K (image.obj time) := fun time =>
    FiniteDimensional.of_injective (mono.app time).hom (mono_injective time)
  have image_transport : ∀ (time : ℝ) (index : Fin n), selectedCell time = (index : WithBot (Fin n)) →
      ∀ ordered : grid index ≤ time,
        Function.Bijective (image.map (homOfLE ordered)).hom := by
    intro time index selected ordered
    have source_bijective := cell_arrow_bijective sourceFamily _ _ ordered
      (cell_support sourceFamily source_birth_member source_death_member time index selected)
    have target_bijective := cell_arrow_bijective targetFamily _ _ ordered
      (cell_support targetFamily target_birth_member target_death_member time index selected)
    have point_fac (sample : ℝ) :
        (Abelian.FunctorCategory.imageObjIso morphism sample).hom ≫
          Abelian.image.ι (morphism.app sample) = mono.app sample := by
      dsimp [Abelian.FunctorCategory.imageObjIso, Limits.kernel.mapIso, Limits.kernel.map]
      simp only [Category.assoc, Limits.kernel.lift_ι, Category.comp_id,
        Limits.PreservesKernel.iso_hom]
      exact Limits.kernelComparison_comp_ι (Limits.cokernel.π morphism)
        ((evaluation ℝ (ModuleCat.{max u v} K)).obj sample)
    let sourceIso := (LinearEquiv.ofBijective
      (intervalArrow sourceFamily (grid index) time ordered) source_bijective).toModuleIso
    let targetIso := (LinearEquiv.ofBijective
      (intervalArrow targetFamily (grid index) time ordered) target_bijective).toModuleIso
    let squareIso : Arrow.mk (morphism.app (grid index)) ≅ Arrow.mk (morphism.app time) :=
      Arrow.isoMk sourceIso targetIso (morphism.naturality (homOfLE ordered))
    let transported : image.obj (grid index) ≅ image.obj time :=
      Abelian.FunctorCategory.imageObjIso morphism (grid index) ≪≫
        Abelian.im.mapIso squareIso ≪≫
        (Abelian.FunctorCategory.imageObjIso morphism time).symm
    have transported_fac : transported.hom ≫ mono.app time =
        mono.app (grid index) ≫ (intervalSum targetFamily).map (homOfLE ordered) := by
      dsimp only [transported, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc]
      rw [← point_fac time, Iso.inv_hom_id_assoc]
      rw [Functor.mapIso_hom, Abelian.im_map]
      erw [Limits.kernel.lift_ι]
      simp only [squareIso, Arrow.isoMk_hom_right]
      rw [← Category.assoc]
      change ((Abelian.FunctorCategory.imageObjIso morphism (grid index)).hom ≫
        Abelian.image.ι (morphism.app (grid index))) ≫ targetIso.hom = _
      rw [point_fac]
      rfl
    have actual : image.map (homOfLE ordered) = transported.hom := by
      apply (cancel_mono (mono.app time)).1
      rw [transported_fac]
      exact mono.naturality (homOfLE ordered)
    rw [actual]
    exact transported.toLinearEquiv.bijective
  have image_prefix_zero : ∀ time, selectedCell time = ⊥ →
      ∀ vector : image.obj time, vector = 0 := by
    intro time selected vector
    apply mono_injective time
    rw [map_zero]
    apply Subtype.ext
    funext occurrence
    have not_born : ¬ targetFamily.1 occurrence ≤ time := by
      intro born
      obtain ⟨index, endpoint⟩ := endpoint_index _ (target_birth_member occurrence)
      have below := (born_test index time).mpr (endpoint ▸ born)
      rw [selected] at below
      exact WithBot.not_coe_le_bot index below
    exact ((mono.app time).hom vector).property occurrence (by tauto)
  let diagram : Fin n ⥤ ModuleCat.{max u v} K := grid.monotone.functor ⋙ image
  let V := fun index => diagram.obj index
  let maps := fun source target (ordered : source ≤ target) =>
    (diagram.map (homOfLE ordered)).hom
  let prefixedDiagram : WithBot (Fin n) ⥤ ModuleCat.{max u v} K := {
    obj slot := match slot with
      | ⊥ => ModuleCat.of K (ULift.{max u v} PUnit.{1})
      | (index : Fin n) => ModuleCat.of K (V index)
    map {source target} arrow := by
      cases source with
      | bot => exact ModuleCat.ofHom 0
      | coe source =>
        cases target with
        | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom arrow))
        | coe target =>
          exact ModuleCat.ofHom
            (maps source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
    map_id index := by
      cases index with
      | bot => ext vector
      | coe index => exact diagram.map_id index
    map_comp {source middle target} first second := by
      cases source with
      | bot =>
        ext vector
        have zero : vector = 0 := Subsingleton.elim _ _
        subst vector
        simp
      | coe source =>
        cases middle with
        | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom first))
        | coe middle =>
          cases target with
          | bot => exact False.elim (WithBot.not_coe_le_bot middle (leOfHom second))
          | coe target => exact diagram.map_comp _ _ }
  let selector := selected_monotone.functor
  let extension := selector ⋙ prefixedDiagram
  let component_slot : ∀ slot time, selectedCell time = slot →
      prefixedDiagram.obj slot →ₗ[K] image.obj time := fun slot time selected => by
    cases slot with
    | bot => exact 0
    | coe index =>
      have ordered : grid index ≤ time := (born_test index time).mp (by rw [selected])
      exact (image.map (homOfLE ordered)).hom
  have component_slot_bijective : ∀ slot time (selected : selectedCell time = slot),
      Function.Bijective (component_slot slot time selected) := by
    intro slot time selected
    cases slot with
    | bot =>
      haveI : Subsingleton (image.obj time) :=
        ⟨fun first second => (image_prefix_zero time selected first).trans
          (image_prefix_zero time selected second).symm⟩
      exact ⟨fun first second _ => Subsingleton.elim _ _,
        fun vector => ⟨0, Subsingleton.elim _ _⟩⟩
    | coe index =>
      exact image_transport time index selected
        ((born_test index time).mp (by rw [selected]))
  let component := fun time => component_slot (selectedCell time) time rfl
  have component_bijective : ∀ time, Function.Bijective (component time) :=
    fun time => component_slot_bijective (selectedCell time) time rfl
  have square : ∀ source target (ordered : source ≤ target)
      (source_slot target_slot : WithBot (Fin n))
      (source_cell : selectedCell source = source_slot)
      (target_cell : selectedCell target = target_slot)
      (slot_ordered : source_slot ≤ target_slot),
      (component_slot target_slot target target_cell).comp
          (prefixedDiagram.map (homOfLE slot_ordered)).hom =
        (image.map (homOfLE ordered)).hom.comp
          (component_slot source_slot source source_cell) := by
    intro source target ordered source_slot target_slot source_cell target_cell slot_ordered
    cases source_slot with
    | bot =>
      ext vector
      have zero : vector = 0 := Subsingleton.elim _ _
      subst vector
      simp
    | coe source_index =>
      cases target_slot with
      | bot => exact False.elim (WithBot.not_coe_le_bot _ slot_ordered)
      | coe target_index =>
        have between : source_index ≤ target_index := WithBot.coe_le_coe.mp slot_ordered
        have source_before : grid source_index ≤ source :=
          (born_test source_index source).mp (by rw [source_cell])
        have target_before : grid target_index ≤ target :=
          (born_test target_index target).mp (by rw [target_cell])
        change (image.map (homOfLE target_before)).hom.comp
            (image.map (homOfLE (grid.monotone between))).hom =
          (image.map (homOfLE ordered)).hom.comp
            (image.map (homOfLE source_before)).hom
        rw [← ModuleCat.hom_comp, ← image.map_comp,
          ← ModuleCat.hom_comp, ← image.map_comp]
        rfl
  have component_naturality : ∀ source target (ordered : source ≤ target),
      (component target).comp (extension.map (homOfLE ordered)).hom =
        (image.map (homOfLE ordered)).hom.comp (component source) := by
    intro source target ordered
    exact square source target ordered (selectedCell source) (selectedCell target)
      rfl rfl (selected_monotone ordered)
  let comparison : extension ≅ image := NatIso.ofComponents
    (fun time => (LinearEquiv.ofBijective (component time)
      (component_bijective time)).toModuleIso) (by
      intro source target arrow
      apply ModuleCat.hom_ext
      exact component_naturality source target (leOfHom arrow))
  letI : ∀ index, FiniteDimensional K (diagram.obj index) := fun index => by
    change FiniteDimensional K (image.obj (grid index))
    infer_instance
  obtain ⟨Occurrence, finite, family, positive, decomposition, unique⟩ :=
    exists_unique_decomposition diagram grid
  letI := finite
  let unlift : image ⋙ ModuleCat.uliftFunctor.{u} K ≅ image :=
    NatIso.ofComponents (fun time => (ULift.moduleEquiv (R := K)).toModuleIso) (by
      intro source target arrow
      apply ModuleCat.hom_ext
      ext vector
      rfl)
  let imageIso : image ≅ intervalSumLarge family := unlift.symm ≪≫
    (Functor.isoWhiskerRight comparison (ModuleCat.uliftFunctor.{u} K)).symm ≪≫ decomposition
  let SmallOccurrence := ULift.{v} (Fin (Fintype.card Occurrence))
  let reindex : SmallOccurrence ≃ Occurrence :=
    Equiv.ulift.trans (Fintype.equivFin Occurrence).symm
  let smallFamily : (SmallOccurrence → ℝ) × (SmallOccurrence → WithTop ℝ) :=
    ⟨fun occurrence => family.1 (reindex occurrence),
      fun occurrence => family.2 (reindex occurrence)⟩
  have small_positive : ∀ occurrence, (smallFamily.1 occurrence : WithTop ℝ) <
      smallFamily.2 occurrence := fun occurrence => positive (reindex occurrence)
  let coordinate_equivalence : ∀ time,
      intervalSpaceLarge family time ≃ₗ[K] intervalSpace smallFamily time := fun time => {
    toFun coordinates := ⟨fun occurrence => coordinates.val (reindex occurrence), by
      intro occurrence unsupported
      exact coordinates.property (reindex occurrence) unsupported⟩
    invFun coordinates := ⟨fun occurrence => coordinates.val (reindex.symm occurrence), by
      intro occurrence unsupported
      apply coordinates.property
      change ¬ (family.1 (reindex (reindex.symm occurrence)) ≤ time ∧
        (time : WithTop ℝ) < family.2 (reindex (reindex.symm occurrence)))
      rw [reindex.apply_symm_apply]
      exact unsupported⟩
    left_inv := by intro coordinates; ext occurrence; simp
    right_inv := by intro coordinates; ext occurrence; simp
    map_add' := by intro first second; rfl
    map_smul' := by intro scalar coordinates; rfl }
  let reindexed : intervalSumLarge family ≅ intervalSum smallFamily :=
    NatIso.ofComponents (fun time => (coordinate_equivalence time).toModuleIso) (by
      intro source target arrow
      apply ModuleCat.hom_ext
      ext coordinates occurrence
      by_cases survives : (target : WithTop ℝ) < family.2 (reindex occurrence) <;>
      simp [coordinate_equivalence, intervalSum, intervalSumLarge,
        intervalArrow, intervalArrowLarge, smallFamily,
        apply_ite, ite_apply, survives])
  let smallIso : image ≅ intervalSum smallFamily := imageIso ≪≫ reindexed
  let image_epi := epi ≫ smallIso.hom
  let image_mono := smallIso.inv ≫ mono
  have image_epi_surjective : ∀ time, Function.Surjective (image_epi.app time).hom := by
    intro time
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have image_mono_injective : ∀ time, Function.Injective (image_mono.app time).hom := by
    intro time
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have sorted : ∀ {Key : Type} [LinearOrder Key] {Index : Type v} [Fintype Index]
      (key : Index → Key), ∃ enumeration : Fin (Fintype.card Index) ≃ Index,
        Monotone fun ordinal => key (enumeration ordinal) := by
    intro Key order Index finite key
    let ranking : Index → Key ×ₗ Fin (Fintype.card Index) := fun occurrence =>
      toLex (key occurrence, Fintype.equivFin Index occurrence)
    have ranking_injective : Function.Injective ranking := by
      intro first second equal
      exact (Fintype.equivFin Index).injective
        (congrArg (fun pair => (ofLex pair).2) equal)
    letI : LinearOrder Index := LinearOrder.lift' ranking ranking_injective
    let enumeration := (monoEquivOfFin Index rfl).toEquiv
    refine ⟨enumeration, ?_⟩
    intro first second ordered
    exact Prod.Lex.monotone_fst _ _ ((monoEquivOfFin Index rfl).monotone ordered)
  let sourceBirthEnumeration := fun birth => Classical.choose
    (sorted (fun occurrence : {occurrence // sourceFamily.1 occurrence = birth} =>
      OrderDual.toDual (sourceFamily.2 occurrence.val)))
  let imageBirthEnumeration := fun birth => Classical.choose
    (sorted (fun occurrence : {occurrence // smallFamily.1 occurrence = birth} =>
      OrderDual.toDual (smallFamily.2 occurrence.val)))
  let imageDeathEnumeration := fun death => Classical.choose
    (sorted (fun occurrence : {occurrence // smallFamily.2 occurrence = death} =>
      smallFamily.1 occurrence.val))
  let targetDeathEnumeration := fun death => Classical.choose
    (sorted (fun occurrence : {occurrence // targetFamily.2 occurrence = death} =>
      targetFamily.1 occurrence.val))
  obtain ⟨sourceEmbedding, source_bounds⟩ := epi_ordered_occurrence_injection
    sourceFamily smallFamily source_positive small_positive image_epi image_epi_surjective
    sourceBirthEnumeration imageBirthEnumeration
    (fun birth => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // sourceFamily.1 occurrence = birth} =>
        OrderDual.toDual (sourceFamily.2 occurrence.val))))
    (fun birth => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // smallFamily.1 occurrence = birth} =>
        OrderDual.toDual (smallFamily.2 occurrence.val))))
  obtain ⟨targetEmbedding, target_bounds⟩ := mono_ordered_occurrence_injection
    smallFamily targetFamily small_positive target_positive image_mono image_mono_injective
    imageDeathEnumeration targetDeathEnumeration
    (fun death => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // smallFamily.2 occurrence = death} => smallFamily.1 occurrence.val)))
    (fun death => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // targetFamily.2 occurrence = death} => targetFamily.1 occurrence.val)))
  have image_factorization : image_epi ≫ image_mono = morphism := by
    simp only [image_epi, image_mono, Category.assoc, smallIso.hom_inv_id_assoc]
    exact Abelian.image.fac morphism
  have source_sorted : ∀ birth, Antitone fun ordinal =>
      sourceFamily.2 (sourceBirthEnumeration birth ordinal).val := fun birth =>
    Classical.choose_spec (sorted (fun occurrence :
      {occurrence // sourceFamily.1 occurrence = birth} =>
        OrderDual.toDual (sourceFamily.2 occurrence.val)))
  have image_birth_sorted : ∀ birth, Antitone fun ordinal =>
      smallFamily.2 (imageBirthEnumeration birth ordinal).val := fun birth =>
    Classical.choose_spec (sorted (fun occurrence :
      {occurrence // smallFamily.1 occurrence = birth} =>
        OrderDual.toDual (smallFamily.2 occurrence.val)))
  have image_death_sorted : ∀ death, Monotone fun ordinal =>
      smallFamily.1 (imageDeathEnumeration death ordinal).val := fun death =>
    Classical.choose_spec (sorted (fun occurrence :
      {occurrence // smallFamily.2 occurrence = death} => smallFamily.1 occurrence.val))
  have target_sorted : ∀ death, Monotone fun ordinal =>
      targetFamily.1 (targetDeathEnumeration death ordinal).val := fun death =>
    Classical.choose_spec (sorted (fun occurrence :
      {occurrence // targetFamily.2 occurrence = death} => targetFamily.1 occurrence.val))
  refine ⟨SmallOccurrence, inferInstance, smallFamily, small_positive, smallIso,
    image_epi_surjective, image_mono_injective, image_factorization,
    sourceBirthEnumeration, imageBirthEnumeration, imageDeathEnumeration, targetDeathEnumeration,
    source_sorted, image_birth_sorted, image_death_sorted, target_sorted,
    sourceEmbedding, targetEmbedding, source_bounds, target_bounds, ?_⟩
  intro etaK etaC kernel_nonnegative cokernel_nonnegative kernel_trivial cokernel_trivial
  have component_factorization : ∀ time coordinates,
      (image_mono.app time).hom ((image_epi.app time).hom coordinates) =
        (morphism.app time).hom coordinates := by
    intro time coordinates
    exact congrArg (fun natural => (natural.app time).hom coordinates) image_factorization
  have kernel_epi : ∀ time, LinearMap.ker (image_epi.app time).hom ≤
      LinearMap.ker (intervalArrow sourceFamily time (time + etaK) (by linarith)) := by
    intro time coordinates killed
    apply kernel_trivial time
    rw [LinearMap.mem_ker] at killed ⊢
    rw [← component_factorization, killed, map_zero]
  have cokernel_mono : ∀ time,
      LinearMap.range (intervalArrow targetFamily time (time + etaC) (by linarith)) ≤
        LinearMap.range (image_mono.app (time + etaC)).hom := by
    intro time coordinates member
    obtain ⟨original, equation⟩ := cokernel_trivial time member
    exact ⟨(image_epi.app (time + etaC)).hom original,
      (component_factorization (time + etaC) original).trans equation⟩
  obtain ⟨death_bounds, finite_death_bounds, source_coverage, essential_equivalence,
      source_essential, kernel_zero⟩ := epi_kernel_trim_estimates
    sourceFamily smallFamily source_positive small_positive image_epi image_epi_surjective
    sourceBirthEnumeration imageBirthEnumeration source_sorted image_birth_sorted
    sourceEmbedding source_bounds etaK kernel_nonnegative kernel_epi
  obtain ⟨birth_bounds, target_coverage, target_essential, cokernel_zero⟩ :=
    mono_cokernel_trim_estimates smallFamily targetFamily small_positive target_positive
      image_mono image_mono_injective imageDeathEnumeration targetDeathEnumeration
      image_death_sorted target_sorted targetEmbedding target_bounds etaC
      cokernel_nonnegative cokernel_mono
  refine ⟨?_, finite_death_bounds, source_coverage, target_coverage, essential_equivalence,
    source_essential, target_essential, ?_, ?_, kernel_zero, cokernel_zero⟩
  · intro occurrence
    exact ⟨(target_bounds occurrence).1, (source_bounds occurrence).2.choose.symm,
      birth_bounds occurrence, (target_bounds occurrence).2.choose.symm,
      (source_bounds occurrence).1, death_bounds occurrence⟩
  · intro occurrence death finite unmatched
    have short : ¬ ((sourceFamily.1 occurrence + etaK : ℝ) : WithTop ℝ) <
        sourceFamily.2 occurrence := fun long => unmatched (source_coverage occurrence long)
    rw [finite, WithTop.coe_lt_coe] at short
    linarith
  · intro occurrence death finite unmatched
    have short : ¬ ((targetFamily.1 occurrence + etaC : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence := fun long => unmatched (target_coverage occurrence long)
    rw [finite, WithTop.coe_lt_coe] at short
    linarith



end D5.S3.HomologicalAlgebra.Persistence.RealDecomposition
