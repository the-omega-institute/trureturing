/- GID: D5/S3/HomologicalAlgebra/Persistence/RealDecomposition
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition,
     D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness]
   utility: none
   digest: Actual natural real interval classification against arbitrary finite competitors. -/

import D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition
import D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Category.ModuleCat.Ulift

namespace D5.S3.HomologicalAlgebra.Persistence.RealDecomposition

open CategoryTheory Module FiniteIntervalSplit FiniteIntervalDecomposition
  RealIntervalUniqueness

universe u v

variable {K : Type u} [Field K] {n : ℕ} {V : Fin n → Type v}
  [∀ index, AddCommGroup (V index)] [∀ index, Module K (V index)]

structure Decomposition (representation : ℝ ⥤ ModuleCat.{v} K) where
  Occurrence : Type v
  finite : Fintype Occurrence
  family : IntervalFamily Occurrence
  isomorphism : representation ⋙ ModuleCat.uliftFunctor.{u} K ≅
    intervalSum (K := K) family

attribute [instance] Decomposition.finite

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_unique_decomposition [∀ index, FiniteDimensional K (V index)]
    (diagram : Diagram K V) (grid : Fin n ↪o ℝ) :
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
              (diagram.map source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
      map_id index := by
        cases index with
        | bot =>
          ext vector
        | coe index =>
          change ModuleCat.ofHom (diagram.map index index le_rfl) = _
          rw [diagram.identity]
          rfl
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
              rw [← ModuleCat.ofHom_comp, diagram.composition]
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
    ∃ decomposition : Decomposition (selector ⋙ prefixedDiagram),
      ∀ {Second : Type v} [Fintype Second] (second : IntervalFamily Second),
        ((selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K ≅
          intervalSum (K := K) second) →
        ∀ birth death,
          Fintype.card {occurrence // decomposition.family.birth occurrence = birth ∧
            decomposition.family.death occurrence = death} =
          Fintype.card {occurrence // second.birth occurrence = birth ∧
            second.death occurrence = death} := by
  classical
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
            (diagram.map source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
    map_id index := by
      cases index with
      | bot =>
        ext vector
      | coe index =>
        change ModuleCat.ofHom (diagram.map index index le_rfl) = _
        rw [diagram.identity]
        rfl
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
            rw [← ModuleCat.ofHom_comp, diagram.composition]
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
  let construction : Decomposition (selector ⋙ prefixedDiagram) := by
    let basis := Classical.choice (exists_interval_basis diagram)
    let family : IntervalFamily (ULift.{v} basis.Occurrence) := {
      birth occurrence := grid (basis.birth occurrence.down)
      death occurrence := if next : (basis.last occurrence.down).val + 1 < n then
        (grid ⟨(basis.last occurrence.down).val + 1, next⟩ : WithTop ℝ) else ⊤
      positive occurrence := by
        split_ifs with next
        · apply WithTop.coe_lt_coe.mpr
          apply grid.strictMono
          have ordered := basis.ordered occurrence.down
          change (basis.birth occurrence.down).val < (basis.last occurrence.down).val + 1
          omega
        · exact WithTop.coe_lt_top _ }
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
        selectedCell time ≤ (basis.last occurrence.down : WithBot (Fin n)) ↔
          (time : WithTop ℝ) < family.death occurrence := by
      intro occurrence time
      by_cases next : (basis.last occurrence.down).val + 1 < n
      · simp only [family, dif_pos next]
        rw [WithTop.coe_lt_coe]
        constructor
        · intro below
          by_contra not_before
          have next_born := (born_test ⟨(basis.last occurrence.down).val + 1, next⟩ time).mpr
            (le_of_not_gt not_before)
          have impossible := WithBot.coe_le_coe.mp (next_born.trans below)
          change (basis.last occurrence.down).val + 1 ≤ (basis.last occurrence.down).val at impossible
          omega
        · intro before
          apply Finset.sup_le
          intro index _
          by_cases born : grid index ≤ time
          · have ordered := grid.strictMono.lt_iff_lt.mp (born.trans_lt before)
            have below : index ≤ basis.last occurrence.down := by
              change index.val ≤ (basis.last occurrence.down).val
              change index.val < (basis.last occurrence.down).val + 1 at ordered
              omega
            simpa [born] using (WithBot.coe_le_coe.mpr below)
          · simp [born]
      · have bounded : selectedCell time ≤ (basis.last occurrence.down : WithBot (Fin n)) := by
          apply Finset.sup_le
          intro index _
          by_cases born : grid index ≤ time
          · have below : index ≤ basis.last occurrence.down := by
              have range := index.isLt
              change index.val ≤ (basis.last occurrence.down).val
              omega
            simpa [born] using (WithBot.coe_le_coe.mpr below)
          · simp [born]
        simp [family, next, bounded]
    have support_test : ∀ occurrence time,
        family.birth occurrence ≤ time ∧ (time : WithTop ℝ) < family.death occurrence ↔
          (basis.birth occurrence.down : WithBot (Fin n)) ≤ selectedCell time ∧
            selectedCell time ≤ (basis.last occurrence.down : WithBot (Fin n)) := by
      intro occurrence time
      change grid (basis.birth occurrence.down) ≤ time ∧ _ ↔ _
      rw [← born_test, ← death_test]
    have zero_coordinates : ∀ time, selectedCell time = ⊥ →
        Subsingleton (intervalSpace (K := K) family time) := by
      intro time selected
      refine ⟨fun first second => ?_⟩
      ext occurrence
      have unsupported : ¬ (family.birth occurrence ≤ time ∧
          (time : WithTop ℝ) < family.death occurrence) := by
        intro supported
        have impossible := (support_test occurrence time).mp supported
        rw [selected] at impossible
        exact WithBot.not_coe_le_bot _ impossible.1
      rw [first.property occurrence unsupported, second.property occurrence unsupported]
    let vector_map : ∀ slot time, intervalSpace (K := K) family time →ₗ[K]
        ULift.{u} (prefixedDiagram.obj slot) := fun slot time => by
      cases slot with
      | bot => exact 0
      | coe index =>
        change intervalSpace (K := K) family time →ₗ[K] ULift.{u} (V index)
        exact ULift.moduleEquiv.symm.toLinearMap.comp
          (∑ occurrence : basis.Occurrence,
            LinearMap.smulRight
              ((LinearMap.proj (ULift.up occurrence)).comp (intervalSpace family time).subtype)
              (basis.vectors occurrence index))
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
        let restriction : intervalSpace (K := K) family time ≃ₗ[K]
            ({occurrence // basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence} → K) := {
          toFun := fun coordinates occurrence => coordinates.val (ULift.up occurrence.val)
          invFun := fun coordinates => ⟨fun occurrence =>
            if supported : basis.birth occurrence.down ≤ index ∧ index ≤ basis.last occurrence.down
            then coordinates ⟨occurrence.down, supported⟩ else 0, by
              intro occurrence unsupported
              have absent : ¬ (basis.birth occurrence.down ≤ index ∧
                  index ≤ basis.last occurrence.down) := by
                simpa [selected] using (support_test occurrence time).not.mp unsupported
              simp [absent]⟩
          left_inv := by
            intro coordinates
            ext occurrence
            by_cases supported : basis.birth occurrence.down ≤ index ∧
                index ≤ basis.last occurrence.down
            · simp [supported]
            · have absent : ¬ (family.birth occurrence ≤ time ∧
                  (time : WithTop ℝ) < family.death occurrence) := by
                apply (support_test occurrence time).not.mpr
                simpa [selected] using supported
              simp [supported, coordinates.property occurrence absent]
          right_inv := by intro coordinates; funext occurrence; simp [occurrence.property]
          map_add' := by intro left right; rfl
          map_smul' := by intro scalar coordinates; rfl }
        have reconstruction : ∀ coordinates : intervalSpace (K := K) family time,
            (∑ occurrence : basis.Occurrence,
              coordinates.val (ULift.up occurrence) • basis.vectors occurrence index) =
            (basis.basis index).equivFun.symm (restriction coordinates) := by
          intro coordinates
          rw [Basis.equivFun_symm_apply]
          simp only [restriction, basis.basis_vectors]
          have complement : (∑ occurrence : {occurrence //
              ¬ (basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence)},
              coordinates.val (ULift.up occurrence.val) •
                basis.vectors occurrence.val index) = 0 := by
            apply Finset.sum_eq_zero
            intro occurrence _
            simp [basis.unsupported occurrence.val index occurrence.property]
          have total := Fintype.sum_subtype_add_sum_subtype
            (fun occurrence => basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence)
            (fun occurrence =>
              coordinates.val (ULift.up occurrence) • basis.vectors occurrence index)
          rw [complement, add_zero] at total
          exact total.symm
        have equality : vector_map (index : WithBot (Fin n)) time =
            (restriction.trans ((basis.basis index).equivFun.symm.trans
              ULift.moduleEquiv.symm)).toLinearMap := by
          apply LinearMap.ext
          intro coordinates
          let lifting : V index ≃ₗ[K] ULift.{u} (V index) :=
            (ULift.moduleEquiv (R := K)).symm
          have lifted := congrArg lifting (reconstruction coordinates)
          simpa only [vector_map, prefixedDiagram, WithBot.recBotCoe_coe, id_eq,
            LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
            LinearMap.proj_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
            LinearEquiv.trans_apply, lifting, map_sum, map_smul] using lifted
        rw [equality]
        exact (restriction.trans ((basis.basis index).equivFun.symm.trans
          ULift.moduleEquiv.symm)).bijective
    let components : ∀ time, (intervalSum (K := K) family).obj time ≅
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
            simp [prefixedDiagram, vector_map,
              map_sum, map_smul, basis.naturality]
            apply Finset.sum_congr rfl
            intro occurrence _
            by_cases born : basis.birth occurrence ≤ source_index
            · have survival : (target : WithTop ℝ) < family.death (ULift.up occurrence) ↔
                  target_index ≤ basis.last occurrence := by
                simpa [target_cell] using (death_test (ULift.up occurrence) target).symm
              by_cases survives : target_index ≤ basis.last occurrence <;>
                simp [intervalArrow, born, survives, survival] <;> rfl
            · have absent : ¬ (family.birth (ULift.up occurrence) ≤ source ∧
                  (source : WithTop ℝ) < family.death (ULift.up occurrence)) := by
                rw [support_test, source_cell]
                intro supported
                exact born (WithBot.coe_le_coe.mp supported.1)
              simp [intervalArrow, born, coordinates.property (ULift.up occurrence) absent]
              rfl
    let isomorphism : intervalSum (K := K) family ≅
        (selector ⋙ prefixedDiagram) ⋙ ModuleCat.uliftFunctor.{u} K :=
      NatIso.ofComponents components (by
        intro source target arrow
        apply ModuleCat.hom_ext
        exact square source target (leOfHom arrow) (selectedCell source) (selectedCell target)
          rfl rfl (leOfHom (selector.map arrow)))
    exact {
      Occurrence := ULift.{v} basis.Occurrence
      finite := inferInstance
      family := family
      isomorphism := isomorphism.symm }
  clear_value construction
  refine ⟨construction, ?_⟩
  intro Second _ second competing
  let first := construction.family
  let isomorphism : intervalSum (K := K) first ≅ intervalSum (K := K) second :=
    construction.isomorphism.symm ≪≫ competing
  have equal_ranks : ∀ source target (ordered : source ≤ target),
      finrank K (LinearMap.range (intervalArrow first source target ordered (K := K))) =
        finrank K (LinearMap.range (intervalArrow second source target ordered (K := K))) := by
    intro source target ordered
    let source_equivalence : intervalSpace (K := K) first source ≃ₗ[K]
        intervalSpace (K := K) second source := (isomorphism.app source).toLinearEquiv
    let target_equivalence : intervalSpace (K := K) first target ≃ₗ[K]
        intervalSpace (K := K) second target := (isomorphism.app target).toLinearEquiv
    have square := congrArg ModuleCat.Hom.hom (isomorphism.hom.naturality (homOfLE ordered))
    change target_equivalence.toLinearMap.comp (intervalArrow first source target ordered) =
      (intervalArrow second source target ordered).comp source_equivalence.toLinearMap at square
    have transported := congrArg LinearMap.range square
    rw [LinearMap.range_comp, LinearEquiv.range_comp] at transported
    rw [← transported]
    exact (target_equivalence.finrank_map_eq _).symm
  classical
  have image_rank : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index)
      source target (ordered : source ≤ target),
      (finrank K (LinearMap.range (intervalArrow family source target ordered (K := K))) : ℤ) =
        ∑ occurrence, if family.birth occurrence ≤ source ∧
          (target : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0 := by
    intro Index _ family source target ordered
    let Live := {occurrence : Index // family.birth occurrence ≤ source ∧
      (target : WithTop ℝ) < family.death occurrence}
    let lift_coordinates : (Live → K) →ₗ[K] intervalSpace (K := K) family source := {
      toFun := fun coordinates => ⟨fun occurrence =>
        if supported : family.birth occurrence ≤ source ∧
            (target : WithTop ℝ) < family.death occurrence then coordinates ⟨occurrence, supported⟩
        else 0, by
          intro occurrence unsupported
          change (if supported : family.birth occurrence ≤ source ∧
            (target : WithTop ℝ) < family.death occurrence then coordinates ⟨occurrence, supported⟩
            else 0) = 0
          split_ifs with supported
          · exact False.elim (unsupported ⟨supported.1,
              lt_of_le_of_lt (WithTop.coe_le_coe.mpr ordered) supported.2⟩)
          · rfl⟩
      map_add' := by
        intro left right
        ext occurrence
        by_cases supported : family.birth occurrence ≤ source ∧
            (target : WithTop ℝ) < family.death occurrence <;> simp [supported]
      map_smul' := by intro scalar coordinates; ext occurrence; simp }
    let equivalence : (Live → K) ≃ₗ[K]
        LinearMap.range (intervalArrow family source target ordered (K := K)) := {
      toFun := fun coordinates =>
        ⟨intervalArrow family source target ordered (lift_coordinates coordinates),
          ⟨lift_coordinates coordinates, rfl⟩⟩
      invFun := fun image occurrence => image.val.val occurrence.val
      left_inv := by
        intro coordinates
        funext occurrence
        simp [intervalArrow, lift_coordinates, occurrence.property]
      right_inv := by
        rintro ⟨image, preimage, rfl⟩
        ext occurrence
        by_cases survives : (target : WithTop ℝ) < family.death occurrence
        · by_cases born : family.birth occurrence ≤ source
          · simp [intervalArrow, lift_coordinates, survives, born]
          · simp [intervalArrow, lift_coordinates, survives, born,
              preimage.property occurrence (by tauto)]
        · simp [intervalArrow, lift_coordinates, survives]
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
      (∑ occurrence, if first.birth occurrence ≤ source ∧
        (target : WithTop ℝ) < first.death occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if second.birth occurrence ≤ source ∧
        (target : WithTop ℝ) < second.death occurrence then (1 : ℤ) else 0 := by
    intro source target ordered
    rw [← image_rank construction.Occurrence first source target ordered,
      ← image_rank Second second source target ordered, equal_ranks source target ordered]
  intro birth death
  let births := Finset.univ.image first.birth ∪ Finset.univ.image second.birth
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
  have birth_difference : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index),
      (∀ occurrence, family.birth occurrence ∈ births) → ∀ time : ℝ,
      (∑ occurrence, if family.birth occurrence ≤ birth ∧
        (time : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0) -
      (∑ occurrence, if family.birth occurrence ≤ before ∧
        (time : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if family.birth occurrence = birth ∧
        (time : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0 := by
    intro Index _ family members time
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro occurrence _
    have cutoff := birth_cut (family.birth occurrence) (members occurrence)
    have monotone : family.birth occurrence ≤ before → family.birth occurrence ≤ birth :=
      fun below => below.trans before_lt.le
    by_cases survives : (time : WithTop ℝ) < family.death occurrence
    · by_cases below : family.birth occurrence ≤ before
      · have not_equal : family.birth occurrence ≠ birth := by
          intro equal
          exact (cutoff.mpr equal).2 below
        simp [survives, below, monotone below, not_equal]
      · by_cases born : family.birth occurrence ≤ birth
        · have equal := cutoff.mp ⟨born, below⟩
          simp [survives, equal, not_le_of_gt before_lt]
        · have not_equal : family.birth occurrence ≠ birth := fun equal => born (equal ▸ le_rfl)
          simp [survives, below, born, not_equal]
    · simp [survives]
  have equal_birth_counts : ∀ time, birth ≤ time →
      (∑ occurrence, if first.birth occurrence = birth ∧
        (time : WithTop ℝ) < first.death occurrence then (1 : ℤ) else 0) =
      ∑ occurrence, if second.birth occurrence = birth ∧
        (time : WithTop ℝ) < second.death occurrence then (1 : ℤ) else 0 := by
    intro time ordered
    rw [← birth_difference construction.Occurrence first (fun occurrence =>
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩)),
      ← birth_difference Second second (fun occurrence =>
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩)),
      equal_counts birth time ordered, equal_counts before time (before_lt.le.trans ordered)]
  let deaths := (Finset.univ.filter fun occurrence => first.death occurrence ≠ ⊤).image
      (fun occurrence => (first.death occurrence).untopD 0) ∪
    (Finset.univ.filter fun occurrence => second.death occurrence ≠ ⊤).image
      (fun occurrence => (second.death occurrence).untopD 0)
  have first_death_member : ∀ occurrence (endpoint : ℝ),
      first.death occurrence = (endpoint : WithTop ℝ) →
      endpoint ∈ deaths := by
    intro occurrence endpoint equal
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨occurrence, by simp [equal], by simp [equal]⟩
  have second_death_member : ∀ occurrence (endpoint : ℝ),
      second.death occurrence = (endpoint : WithTop ℝ) →
      endpoint ∈ deaths := by
    intro occurrence endpoint equal
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨occurrence, by simp [equal], by simp [equal]⟩
  have multiplicity_sum : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index),
      (Fintype.card {occurrence //
        family.birth occurrence = birth ∧ family.death occurrence = death} : ℤ) =
      ∑ occurrence, if family.birth occurrence = birth ∧ family.death occurrence = death
        then (1 : ℤ) else 0 := by
    intro Index _ family
    simp [Fintype.card_subtype]
  apply Int.ofNat_inj.mp
  rw [multiplicity_sum construction.Occurrence first, multiplicity_sum Second second]
  induction death using WithTop.recTopCoe with
  | top =>
    let endpoints := deaths ∪ {birth}
    have inhabited : endpoints.Nonempty := ⟨birth, by simp [endpoints]⟩
    let time := endpoints.max' inhabited
    have birth_le : birth ≤ time := Finset.le_max' _ _ (by simp [endpoints])
    have tail : ∀ endpoint ∈ deaths, endpoint ≤ time := fun endpoint member =>
      Finset.le_max' _ _ (Finset.mem_union_left _ member)
    have essential : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index),
        (∀ occurrence (endpoint : ℝ),
          family.death occurrence = (endpoint : WithTop ℝ) → endpoint ∈ deaths) →
        (∑ occurrence, if family.birth occurrence = birth ∧
          (time : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0) =
        ∑ occurrence, if family.birth occurrence = birth ∧ family.death occurrence = ⊤
          then (1 : ℤ) else 0 := by
      intro Index _ family members
      apply Finset.sum_congr rfl
      intro occurrence _
      rcases eq_or_ne (family.death occurrence) ⊤ with infinite | finite
      · simp [infinite]
      · obtain ⟨endpoint, equal⟩ := WithTop.ne_top_iff_exists.mp finite
        have below := tail endpoint (members occurrence endpoint equal.symm)
        simp [← equal, not_lt_of_ge below]
    rw [← essential construction.Occurrence first first_death_member, ← essential Second second second_death_member]
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
      have death_difference : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index),
          (∀ occurrence (value : ℝ),
            family.death occurrence = (value : WithTop ℝ) → value ∈ deaths) →
          (∑ occurrence, if family.birth occurrence = birth ∧
            (time : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0) -
          (∑ occurrence, if family.birth occurrence = birth ∧
            (endpoint : WithTop ℝ) < family.death occurrence then (1 : ℤ) else 0) =
          ∑ occurrence, if family.birth occurrence = birth ∧
            family.death occurrence = (endpoint : WithTop ℝ) then (1 : ℤ) else 0 := by
        intro Index _ family members
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro occurrence _
        rcases eq_or_ne (family.death occurrence) ⊤ with infinite | finite
        · simp [infinite]
        · obtain ⟨value, equal⟩ := WithTop.ne_top_iff_exists.mp finite
          have cutoff := death_cut value (members occurrence value equal.symm)
          have monotone : endpoint < value → time < value := fun above => time_lt.trans above
          simp only [← equal, WithTop.coe_lt_coe, WithTop.coe_inj]
          split_ifs <;> simp_all
      rw [← death_difference construction.Occurrence first first_death_member,
        ← death_difference Second second second_death_member,
        equal_birth_counts time birth_le, equal_birth_counts endpoint positive.le]
    · have empty : ∀ (Index : Type v) [Fintype Index] (family : IntervalFamily Index),
          (∑ occurrence, if family.birth occurrence = birth ∧
            family.death occurrence = (endpoint : WithTop ℝ) then (1 : ℤ) else 0) = 0 := by
        intro Index _ family
        apply Finset.sum_eq_zero
        intro occurrence _
        have invalid : ¬ (family.birth occurrence = birth ∧
            family.death occurrence = (endpoint : WithTop ℝ)) := by
          rintro ⟨born, died⟩
          have length := family.positive occurrence
          rw [born, died, WithTop.coe_lt_coe] at length
          exact positive length
        simp [invalid]
      rw [empty construction.Occurrence first, empty Second second]

end D5.S3.HomologicalAlgebra.Persistence.RealDecomposition
