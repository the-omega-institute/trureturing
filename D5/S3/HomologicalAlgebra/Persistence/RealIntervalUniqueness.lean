/- GID: D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual morphism window counts, ordered injections and quantitative trim estimates. -/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

namespace D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness

open CategoryTheory Module

universe u v

variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false in
theorem mono_death_window_count {Source Target : Type v} [Fintype Source] [Fintype Target]
    (sourceFamily : (Source → ℝ) × (Source → WithTop ℝ)) (targetFamily : (Target → ℝ) × (Target → WithTop ℝ))
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
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
    (injective : ∀ time, Function.Injective (morphism.app time).hom)
    (birthCut sample : ℝ) (deathCut : WithTop ℝ) (birth_before : birthCut ≤ sample)
    (sample_before : (sample : WithTop ℝ) ≤ deathCut),
    Fintype.card {occurrence // sourceFamily.1 occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
      sourceFamily.2 occurrence ≤ deathCut} ≤
    Fintype.card {occurrence // targetFamily.1 occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
      targetFamily.2 occurrence ≤ deathCut} := by
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
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (injective : ∀ time, Function.Injective (morphism.app time).hom)
      (birthCut sample : ℝ) (deathCut : WithTop ℝ) (birth_before : birthCut ≤ sample)
      (sample_before : (sample : WithTop ℝ) ≤ deathCut),
      Fintype.card {occurrence // sourceFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
        sourceFamily.2 occurrence ≤ deathCut} ≤
      Fintype.card {occurrence // targetFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
        targetFamily.2 occurrence ≤ deathCut}
  intro morphism injective birthCut sample deathCut birth_before sample_before
  let SourceWindow := {occurrence // sourceFamily.1 occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
    sourceFamily.2 occurrence ≤ deathCut}
  let TargetWindow := {occurrence // targetFamily.1 occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
    targetFamily.2 occurrence ≤ deathCut}
  let extend : ∀ time, birthCut ≤ time → time ≤ sample →
      (SourceWindow → K) →ₗ[K] intervalSpace sourceFamily time :=
    fun time after_birth before_sample => {
      toFun := fun coordinates => ⟨fun occurrence =>
        if supported : sourceFamily.1 occurrence ≤ birthCut ∧
            (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
            sourceFamily.2 occurrence ≤ deathCut
        then coordinates ⟨occurrence, supported⟩ else 0, by
          intro occurrence unsupported
          have absent : ¬ (sourceFamily.1 occurrence ≤ birthCut ∧
              (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
              sourceFamily.2 occurrence ≤ deathCut) := by
            intro supported
            exact unsupported ⟨supported.1.trans after_birth,
              lt_of_le_of_lt (WithTop.coe_le_coe.mpr before_sample) supported.2.1⟩
          simp [absent]⟩
      map_add' := by
        intro first second
        ext occurrence
        dsimp
        split_ifs <;> simp
      map_smul' := by
        intro scalar coordinates
        ext occurrence
        dsimp
        split_ifs <;> simp }
  have birth_image : ∀ coordinates,
      intervalArrow sourceFamily birthCut sample birth_before
        (extend birthCut le_rfl birth_before coordinates) =
      extend sample birth_before le_rfl coordinates := by
    intro coordinates
    ext occurrence
    by_cases supported : sourceFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
        sourceFamily.2 occurrence ≤ deathCut
    · simp [intervalArrow, apply_ite, ite_apply, extend, supported]
    · simp [intervalArrow, apply_ite, ite_apply, extend, supported]
  have death_kernel : ∀ (cut : ℝ) (after_sample : sample ≤ cut),
      deathCut ≤ (cut : WithTop ℝ) → ∀ coordinates,
      intervalArrow sourceFamily sample cut after_sample
        (extend sample birth_before le_rfl coordinates) = 0 := by
    intro cut after_sample above coordinates
    ext occurrence
    by_cases supported : sourceFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
        sourceFamily.2 occurrence ≤ deathCut
    · simp [intervalArrow, apply_ite, ite_apply, extend, not_lt_of_ge (supported.2.2.trans above)]
    · simp [intervalArrow, apply_ite, ite_apply, extend, supported]
  have target_supported : ∀ coordinates occurrence,
      ¬ (targetFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
        targetFamily.2 occurrence ≤ deathCut) →
      ((morphism.app sample).hom (extend sample birth_before le_rfl coordinates)).val
        occurrence = 0 := by
    intro coordinates occurrence unsupported
    by_cases born : targetFamily.1 occurrence ≤ birthCut
    · by_cases survives : (sample : WithTop ℝ) < targetFamily.2 occurrence
      · cases deathCut with
        | top => exact False.elim (unsupported ⟨born, survives, le_top⟩)
        | coe finiteCut =>
          have after_sample : sample ≤ finiteCut := WithTop.coe_le_coe.mp sample_before
          have survives_cut : (finiteCut : WithTop ℝ) < targetFamily.2 occurrence := by
            apply lt_of_not_ge
            intro dies
            exact unsupported ⟨born, survives, dies⟩
          have square := congrArg (fun arrow => arrow.hom
            (extend sample birth_before le_rfl coordinates))
            (morphism.naturality (homOfLE after_sample))
          change (morphism.app finiteCut).hom
              (intervalArrow sourceFamily sample finiteCut after_sample
                (extend sample birth_before le_rfl coordinates)) =
            intervalArrow targetFamily sample finiteCut after_sample
              ((morphism.app sample).hom
                (extend sample birth_before le_rfl coordinates)) at square
          rw [death_kernel finiteCut after_sample le_rfl, map_zero] at square
          have coordinate := congrArg
            (fun vector : intervalSpace targetFamily finiteCut => vector.val occurrence)
            square
          simpa [intervalArrow, apply_ite, ite_apply, survives_cut] using coordinate.symm
      · exact ((morphism.app sample).hom
          (extend sample birth_before le_rfl coordinates)).property occurrence (by tauto)
    · have square := congrArg (fun arrow => arrow.hom
          (extend birthCut le_rfl birth_before coordinates))
          (morphism.naturality (homOfLE birth_before))
      change (morphism.app sample).hom
          (intervalArrow sourceFamily birthCut sample birth_before
            (extend birthCut le_rfl birth_before coordinates)) =
        intervalArrow targetFamily birthCut sample birth_before
          ((morphism.app birthCut).hom (extend birthCut le_rfl birth_before coordinates)) at square
      rw [birth_image] at square
      have coordinate := congrArg
        (fun vector : intervalSpace targetFamily sample => vector.val occurrence) square
      have absent := ((morphism.app birthCut).hom
        (extend birthCut le_rfl birth_before coordinates)).property occurrence (by tauto)
      change _ = (0 : K) at absent
      simpa [intervalArrow, apply_ite, ite_apply, absent] using coordinate
  let restricted : (SourceWindow → K) →ₗ[K] (TargetWindow → K) :=
    LinearMap.pi fun occurrence => (LinearMap.proj occurrence.val).comp
      ((intervalSpace targetFamily sample).subtype.comp
        ((morphism.app sample).hom.comp (extend sample birth_before le_rfl)))
  have restricted_injective : Function.Injective restricted := by
    intro first second equal
    have equal_images : (morphism.app sample).hom (extend sample birth_before le_rfl first) =
        (morphism.app sample).hom (extend sample birth_before le_rfl second) := by
      apply Subtype.ext
      funext occurrence
      by_cases supported : targetFamily.1 occurrence ≤ birthCut ∧
          (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
          targetFamily.2 occurrence ≤ deathCut
      · exact congrFun equal ⟨occurrence, supported⟩
      · rw [target_supported first occurrence supported,
          target_supported second occurrence supported]
    have equal_sources := injective sample equal_images
    funext occurrence
    have coordinate := congrArg
      (fun vector : intervalSpace sourceFamily sample => vector.val occurrence.val)
      equal_sources
    simpa [extend, occurrence.property] using coordinate
  have dimensions := LinearMap.finrank_le_finrank_of_injective
    (f := restricted) restricted_injective
  simpa [SourceWindow, TargetWindow, Module.finrank_fintype_fun_eq_card] using dimensions

set_option backward.isDefEq.respectTransparency false in
theorem epi_birth_window_count {Source Target : Type v} [Fintype Source] [Fintype Target]
    (sourceFamily : (Source → ℝ) × (Source → WithTop ℝ)) (targetFamily : (Target → ℝ) × (Target → WithTop ℝ))
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
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
    (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
    (earlier birthCut sample : ℝ) (earlier_before : earlier ≤ birthCut)
    (birth_before : birthCut ≤ sample),
    Fintype.card {occurrence // earlier < targetFamily.1 occurrence ∧
      targetFamily.1 occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < targetFamily.2 occurrence} ≤
    Fintype.card {occurrence // earlier < sourceFamily.1 occurrence ∧
      sourceFamily.1 occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < sourceFamily.2 occurrence} := by
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
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
      (earlier birthCut sample : ℝ) (earlier_before : earlier ≤ birthCut)
      (birth_before : birthCut ≤ sample),
      Fintype.card {occurrence // earlier < targetFamily.1 occurrence ∧
        targetFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < targetFamily.2 occurrence} ≤
      Fintype.card {occurrence // earlier < sourceFamily.1 occurrence ∧
        sourceFamily.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.2 occurrence}
  intro morphism surjective earlier birthCut sample earlier_before birth_before
  let SourceWindow := {occurrence // earlier < sourceFamily.1 occurrence ∧
    sourceFamily.1 occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < sourceFamily.2 occurrence}
  let TargetWindow := {occurrence // earlier < targetFamily.1 occurrence ∧
    targetFamily.1 occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < targetFamily.2 occurrence}
  let extend : ∀ {Index : Type v} (family : (Index → ℝ) × (Index → WithTop ℝ)),
      ({occurrence // earlier < family.1 occurrence ∧
        family.1 occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < family.2 occurrence} → K) →ₗ[K]
      intervalSpace family birthCut := fun family => {
    toFun := fun coordinates => ⟨fun occurrence =>
      if supported : earlier < family.1 occurrence ∧
          family.1 occurrence ≤ birthCut ∧
          (sample : WithTop ℝ) < family.2 occurrence
      then coordinates ⟨occurrence, supported⟩ else 0, by
        intro occurrence unsupported
        have absent : ¬ (earlier < family.1 occurrence ∧
            family.1 occurrence ≤ birthCut ∧
            (sample : WithTop ℝ) < family.2 occurrence) := by
          intro supported
          exact unsupported ⟨supported.2.1,
            lt_of_le_of_lt (WithTop.coe_le_coe.mpr birth_before) supported.2.2⟩
        simp [absent]⟩
    map_add' := by
      intro first second
      ext occurrence
      dsimp
      split_ifs <;> simp
    map_smul' := by
      intro scalar coordinates
      ext occurrence
      dsimp
      split_ifs <;> simp }
  let restricted : (SourceWindow → K) →ₗ[K] (TargetWindow → K) :=
    LinearMap.pi fun occurrence => (LinearMap.proj occurrence.val).comp
      ((intervalSpace targetFamily sample).subtype.comp
        ((morphism.app sample).hom.comp
          ((intervalArrow sourceFamily birthCut sample birth_before).comp
            (extend sourceFamily))))
  have restricted_surjective : Function.Surjective restricted := by
    intro coordinates
    obtain ⟨preimage, image_eq⟩ := surjective birthCut (extend targetFamily coordinates)
    let source_coordinates : SourceWindow → K := fun occurrence => preimage.val occurrence.val
    let early : intervalSpace sourceFamily earlier := ⟨fun occurrence =>
      if sourceFamily.1 occurrence ≤ earlier ∧
          (sample : WithTop ℝ) < sourceFamily.2 occurrence
      then preimage.val occurrence else 0, by
        intro occurrence unsupported
        have absent : ¬ (sourceFamily.1 occurrence ≤ earlier ∧
            (sample : WithTop ℝ) < sourceFamily.2 occurrence) := by
          intro supported
          exact unsupported ⟨supported.1,
            lt_of_le_of_lt
              (WithTop.coe_le_coe.mpr (earlier_before.trans birth_before)) supported.2⟩
        simp [absent]⟩
    have splitting : intervalArrow sourceFamily birthCut sample birth_before preimage =
        intervalArrow sourceFamily birthCut sample birth_before
          (extend sourceFamily source_coordinates) +
        intervalArrow sourceFamily earlier sample (earlier_before.trans birth_before) early := by
      ext occurrence
      by_cases survives : (sample : WithTop ℝ) < sourceFamily.2 occurrence
      · by_cases old : sourceFamily.1 occurrence ≤ earlier
        · simp [intervalArrow, apply_ite, ite_apply, extend, early, survives, old, not_lt_of_ge old]
        · have recent : earlier < sourceFamily.1 occurrence := lt_of_not_ge old
          by_cases born : sourceFamily.1 occurrence ≤ birthCut
          · simp [intervalArrow, apply_ite, ite_apply, extend, early, source_coordinates, survives, old, recent, born]
          · have absent := preimage.property occurrence (by tauto)
            change _ = (0 : K) at absent
            simp [intervalArrow, apply_ite, ite_apply, extend, early, survives, old, born, absent]
      · simp [intervalArrow, apply_ite, ite_apply, survives]
    have early_zero : ∀ occurrence : TargetWindow,
        ((morphism.app sample).hom
          (intervalArrow sourceFamily earlier sample (earlier_before.trans birth_before) early)).val
          occurrence.val = 0 := by
      intro occurrence
      have square := congrArg (fun arrow => arrow.hom early)
        (morphism.naturality (homOfLE (earlier_before.trans birth_before)))
      change (morphism.app sample).hom
          (intervalArrow sourceFamily earlier sample (earlier_before.trans birth_before) early) =
        intervalArrow targetFamily earlier sample (earlier_before.trans birth_before)
          ((morphism.app earlier).hom early) at square
      have coordinate := congrArg
        (fun vector : intervalSpace targetFamily sample => vector.val occurrence.val)
        square
      have absent := ((morphism.app earlier).hom early).property occurrence.val
        (by exact fun supported => (not_le_of_gt occurrence.property.1) supported.1)
      change _ = (0 : K) at absent
      simpa [intervalArrow, apply_ite, ite_apply, absent] using coordinate
    have square := congrArg (fun arrow => arrow.hom preimage)
      (morphism.naturality (homOfLE birth_before))
    change (morphism.app sample).hom
        (intervalArrow sourceFamily birthCut sample birth_before preimage) =
      intervalArrow targetFamily birthCut sample birth_before
        ((morphism.app birthCut).hom preimage) at square
    rw [image_eq] at square
    refine ⟨source_coordinates, ?_⟩
    funext occurrence
    have coordinate := congrArg
      (fun vector : intervalSpace targetFamily sample => vector.val occurrence.val) square
    have transported := congrArg
      (fun vector : intervalSpace sourceFamily sample =>
        ((morphism.app sample).hom vector).val occurrence.val) splitting
    simp only [map_add] at transported
    change ((morphism.app sample).hom
        (intervalArrow sourceFamily birthCut sample birth_before preimage)).val occurrence.val =
      ((morphism.app sample).hom (intervalArrow sourceFamily birthCut sample birth_before
        (extend sourceFamily source_coordinates))).val occurrence.val +
      ((morphism.app sample).hom (intervalArrow sourceFamily earlier sample
        (earlier_before.trans birth_before) early)).val occurrence.val at transported
    rw [early_zero, add_zero] at transported
    have reconstruction : ((morphism.app sample).hom
        (intervalArrow sourceFamily birthCut sample birth_before preimage)).val occurrence.val =
        coordinates occurrence := by
      simpa [intervalArrow, apply_ite, ite_apply, extend, occurrence.property.1, occurrence.property.2.1,
        occurrence.property.2.2] using coordinate
    exact transported.symm.trans reconstruction
  have dimensions := LinearMap.finrank_le_finrank_of_surjective
    (f := restricted) restricted_surjective
  simpa [SourceWindow, TargetWindow, Module.finrank_fintype_fun_eq_card] using dimensions

set_option backward.isDefEq.respectTransparency false in
theorem mono_ordered_occurrence_injection {Source Target : Type v}
    [Fintype Source] [Fintype Target]
    (sourceFamily : (Source → ℝ) × (Source → WithTop ℝ)) (targetFamily : (Target → ℝ) × (Target → WithTop ℝ))
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
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
    (injective : ∀ time, Function.Injective (morphism.app time).hom)
    (sourceEnumeration : ∀ death, Fin (Fintype.card
      {occurrence // sourceFamily.2 occurrence = death}) ≃
        {occurrence // sourceFamily.2 occurrence = death})
    (targetEnumeration : ∀ death, Fin (Fintype.card
      {occurrence // targetFamily.2 occurrence = death}) ≃
        {occurrence // targetFamily.2 occurrence = death})
    (source_sorted : ∀ death, Monotone fun ordinal =>
      sourceFamily.1 (sourceEnumeration death ordinal).val)
    (target_sorted : ∀ death, Monotone fun ordinal =>
      targetFamily.1 (targetEnumeration death ordinal).val),
    ∃ embedding : Source ↪ Target, ∀ occurrence,
      targetFamily.1 (embedding occurrence) ≤ sourceFamily.1 occurrence ∧
      ∃ sameDeath : targetFamily.2 (embedding occurrence) = sourceFamily.2 occurrence,
        ((targetEnumeration (sourceFamily.2 occurrence)).symm
          ⟨embedding occurrence, sameDeath⟩).val =
        ((sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val := by
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
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (injective : ∀ time, Function.Injective (morphism.app time).hom)
      (sourceEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // sourceFamily.2 occurrence = death}) ≃
          {occurrence // sourceFamily.2 occurrence = death})
      (targetEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // targetFamily.2 occurrence = death}) ≃
          {occurrence // targetFamily.2 occurrence = death})
      (source_sorted : ∀ death, Monotone fun ordinal =>
        sourceFamily.1 (sourceEnumeration death ordinal).val)
      (target_sorted : ∀ death, Monotone fun ordinal =>
        targetFamily.1 (targetEnumeration death ordinal).val),
      ∃ embedding : Source ↪ Target, ∀ occurrence,
        targetFamily.1 (embedding occurrence) ≤ sourceFamily.1 occurrence ∧
        ∃ sameDeath : targetFamily.2 (embedding occurrence) = sourceFamily.2 occurrence,
          ((targetEnumeration (sourceFamily.2 occurrence)).symm
            ⟨embedding occurrence, sameDeath⟩).val =
          ((sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val
  intro morphism injective sourceEnumeration targetEnumeration source_sorted target_sorted
  have counts (birth : ℝ) (death : WithTop ℝ) (positive : (birth : WithTop ℝ) < death) :
      Fintype.card {occurrence // sourceFamily.1 occurrence ≤ birth ∧
        sourceFamily.2 occurrence = death} ≤
      Fintype.card {occurrence // targetFamily.1 occurrence ≤ birth ∧
        targetFamily.2 occurrence = death} := by
    let endpoints := (insert (birth : WithTop ℝ)
      (Finset.univ.image sourceFamily.2 ∪ Finset.univ.image targetFamily.2)).filter
        (fun endpoint => endpoint < death)
    have birth_mem : (birth : WithTop ℝ) ∈ endpoints := by simp [endpoints, positive]
    let maximum := endpoints.sup' ⟨_, birth_mem⟩ id
    have maximum_before : maximum < death := by
      apply (Finset.sup'_lt_iff _).mpr
      intro endpoint member
      exact (Finset.mem_filter.mp member).2
    have finite_maximum : maximum ≠ ⊤ := ne_top_of_lt maximum_before
    let sample := maximum.untop finite_maximum
    have sample_eq : (sample : WithTop ℝ) = maximum := WithTop.coe_untop _ _
    have birth_before : birth ≤ sample := by
      apply WithTop.coe_le_coe.mp
      rw [sample_eq]
      exact Finset.le_sup' id birth_mem
    have before : (sample : WithTop ℝ) < death := by rwa [sample_eq]
    have source_lower : ∀ occurrence, sourceFamily.2 occurrence < death →
        sourceFamily.2 occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [endpoints, less]
    have target_lower : ∀ occurrence, targetFamily.2 occurrence < death →
        targetFamily.2 occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [endpoints, less]
    have window := mono_death_window_count sourceFamily targetFamily source_positive target_positive morphism injective
      birth sample death birth_before before.le
    have source_predicate : (fun occurrence => sourceFamily.1 occurrence ≤ birth ∧
        (sample : WithTop ℝ) < sourceFamily.2 occurrence ∧
        sourceFamily.2 occurrence ≤ death) =
        (fun occurrence => sourceFamily.1 occurrence ≤ birth ∧
          sourceFamily.2 occurrence = death) := by
      funext occurrence
      apply propext
      constructor
      · intro supported
        exact ⟨supported.1, le_antisymm supported.2.2 (le_of_not_gt fun less =>
          (not_lt_of_ge (source_lower occurrence less)) supported.2.1)⟩
      · rintro ⟨born, rfl⟩
        exact ⟨born, before, le_rfl⟩
    have target_predicate : (fun occurrence => targetFamily.1 occurrence ≤ birth ∧
        (sample : WithTop ℝ) < targetFamily.2 occurrence ∧
        targetFamily.2 occurrence ≤ death) =
        (fun occurrence => targetFamily.1 occurrence ≤ birth ∧
          targetFamily.2 occurrence = death) := by
      funext occurrence
      apply propext
      constructor
      · intro supported
        exact ⟨supported.1, le_antisymm supported.2.2 (le_of_not_gt fun less =>
          (not_lt_of_ge (target_lower occurrence less)) supported.2.1)⟩
      · rintro ⟨born, rfl⟩
        exact ⟨born, before, le_rfl⟩
    have source_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (fun occurrence => Iff.of_eq (congrFun source_predicate occurrence)))
    have target_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (fun occurrence => Iff.of_eq (congrFun target_predicate occurrence)))
    exact source_card ▸ target_card ▸ window
  have ordinal_bound (occurrence : Source) :
      let ordinal := (sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩
      ordinal.val < Fintype.card {other // targetFamily.1 other ≤
        sourceFamily.1 occurrence ∧ targetFamily.2 other = sourceFamily.2 occurrence} := by
    let death := sourceFamily.2 occurrence
    let ordinal := (sourceEnumeration death).symm ⟨occurrence, rfl⟩
    let initial : Fin (ordinal.val + 1) → {other // sourceFamily.1 other ≤
        sourceFamily.1 occurrence ∧ sourceFamily.2 other = death} := fun index =>
      ⟨(sourceEnumeration death ⟨index.val, by omega⟩).val,
        by
          constructor
          · have ordered : (⟨index.val, by omega⟩ : Fin (Fintype.card
                {other // sourceFamily.2 other = death})) ≤ ordinal := by
              exact Nat.le_of_lt_succ index.isLt
            simpa [ordinal] using source_sorted death ordered
          · exact (sourceEnumeration death _).property⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have equal_values := congrArg Subtype.val equal
      have equal_indices := (sourceEnumeration death).injective (Subtype.ext equal_values)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // sourceFamily.2 other = death}) => index.val) equal_indices)
    have initial_count := Fintype.card_le_of_injective initial initial_injective
    have comparison := counts (sourceFamily.1 occurrence) death (source_positive occurrence)
    simp only [Fintype.card_fin] at initial_count
    exact lt_of_lt_of_le (Nat.lt_of_succ_le initial_count) comparison
  have class_bound (occurrence : Source) :
      ((sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {other // targetFamily.2 other = sourceFamily.2 occurrence} := by
    have eligible := ordinal_bound occurrence
    have total := Fintype.card_le_of_injective
      (fun other : {other // targetFamily.1 other ≤ sourceFamily.1 occurrence ∧
          targetFamily.2 other = sourceFamily.2 occurrence} =>
        (⟨other.val, other.property.2⟩ : {other //
          targetFamily.2 other = sourceFamily.2 occurrence}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {other // targetFamily.2 other = sourceFamily.2 occurrence} =>
          other.val) equal))
    exact eligible.trans_le total
  have class_bound' : ∀ death (occurrence : {other // sourceFamily.2 other = death}),
      ((sourceEnumeration death).symm occurrence).val <
        Fintype.card {other // targetFamily.2 other = death} := by
    intro death ⟨occurrence, sameDeath⟩
    subst death
    exact class_bound occurrence
  let classMap : ∀ death, {other // sourceFamily.2 other = death} ↪
      {other // targetFamily.2 other = death} := fun death => {
    toFun := fun occurrence => targetEnumeration death
      ⟨((sourceEnumeration death).symm occurrence).val, class_bound' death occurrence⟩
    inj' := by
      intro first second equal
      have sameOrdinal := (targetEnumeration death).injective equal
      apply (sourceEnumeration death).symm.injective
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // targetFamily.2 other = death}) => index.val) sameOrdinal) }
  let embedding := (Equiv.sigmaFiberEquiv sourceFamily.2).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _) classMap).trans
      (Equiv.sigmaFiberEquiv targetFamily.2).toEmbedding)
  let selected := fun occurrence => classMap (sourceFamily.2 occurrence) ⟨occurrence, rfl⟩
  have birth_bound (occurrence : Source) :
      targetFamily.1 (selected occurrence).val ≤ sourceFamily.1 occurrence := by
    by_contra not_before
    let ordinal := (sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩
    let below : {other // targetFamily.1 other ≤ sourceFamily.1 occurrence ∧
        targetFamily.2 other = sourceFamily.2 occurrence} → Fin ordinal.val := fun other =>
      ⟨((targetEnumeration (sourceFamily.2 occurrence)).symm
          ⟨other.val, other.property.2⟩).val, by
        by_contra not_less
        have ordered : (⟨ordinal.val, class_bound occurrence⟩ : Fin (Fintype.card
            {other // targetFamily.2 other = sourceFamily.2 occurrence})) ≤
          (targetEnumeration (sourceFamily.2 occurrence)).symm
            ⟨other.val, other.property.2⟩ := Nat.le_of_not_gt not_less
        have comparison := target_sorted (sourceFamily.2 occurrence) ordered
        have comparison' : targetFamily.1 (selected occurrence).val ≤
            targetFamily.1 other.val := by simpa [selected, classMap] using comparison
        exact not_before (comparison'.trans other.property.1)⟩
    have below_injective : Function.Injective below := by
      intro first second equal
      have equal_indices : (targetEnumeration (sourceFamily.2 occurrence)).symm
          ⟨first.val, first.property.2⟩ =
        (targetEnumeration (sourceFamily.2 occurrence)).symm
          ⟨second.val, second.property.2⟩ :=
        Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
      have equal_values := (targetEnumeration (sourceFamily.2 occurrence)).symm.injective
        equal_indices
      exact Subtype.ext (congrArg (fun other : {other //
        targetFamily.2 other = sourceFamily.2 occurrence} => other.val) equal_values)
    have bound := Fintype.card_le_of_injective below below_injective
    simp only [Fintype.card_fin] at bound
    exact (not_lt_of_ge bound) (ordinal_bound occurrence)
  refine ⟨embedding, ?_⟩
  intro occurrence
  rw [show embedding occurrence = (selected occurrence).val from rfl]
  exact ⟨birth_bound occurrence, (selected occurrence).property, by simp [selected, classMap]⟩

set_option backward.isDefEq.respectTransparency false in
theorem epi_ordered_occurrence_injection {Source Target : Type v}
    [Fintype Source] [Fintype Target]
    (sourceFamily : (Source → ℝ) × (Source → WithTop ℝ)) (targetFamily : (Target → ℝ) × (Target → WithTop ℝ))
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
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
    (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
    (sourceEnumeration : ∀ birth, Fin (Fintype.card
      {occurrence // sourceFamily.1 occurrence = birth}) ≃
        {occurrence // sourceFamily.1 occurrence = birth})
    (targetEnumeration : ∀ birth, Fin (Fintype.card
      {occurrence // targetFamily.1 occurrence = birth}) ≃
        {occurrence // targetFamily.1 occurrence = birth})
    (source_sorted : ∀ birth, Antitone fun ordinal =>
      sourceFamily.2 (sourceEnumeration birth ordinal).val)
    (target_sorted : ∀ birth, Antitone fun ordinal =>
      targetFamily.2 (targetEnumeration birth ordinal).val),
    ∃ embedding : Target ↪ Source, ∀ occurrence,
      targetFamily.2 occurrence ≤ sourceFamily.2 (embedding occurrence) ∧
      ∃ sameBirth : sourceFamily.1 (embedding occurrence) = targetFamily.1 occurrence,
        ((sourceEnumeration (targetFamily.1 occurrence)).symm
          ⟨embedding occurrence, sameBirth⟩).val =
        ((targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val := by
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
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
      (sourceEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // sourceFamily.1 occurrence = birth}) ≃
          {occurrence // sourceFamily.1 occurrence = birth})
      (targetEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // targetFamily.1 occurrence = birth}) ≃
          {occurrence // targetFamily.1 occurrence = birth})
      (source_sorted : ∀ birth, Antitone fun ordinal =>
        sourceFamily.2 (sourceEnumeration birth ordinal).val)
      (target_sorted : ∀ birth, Antitone fun ordinal =>
        targetFamily.2 (targetEnumeration birth ordinal).val),
      ∃ embedding : Target ↪ Source, ∀ occurrence,
        targetFamily.2 occurrence ≤ sourceFamily.2 (embedding occurrence) ∧
        ∃ sameBirth : sourceFamily.1 (embedding occurrence) = targetFamily.1 occurrence,
          ((sourceEnumeration (targetFamily.1 occurrence)).symm
            ⟨embedding occurrence, sameBirth⟩).val =
          ((targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val
  intro morphism surjective sourceEnumeration targetEnumeration source_sorted target_sorted
  have counts (birth : ℝ) (death : WithTop ℝ) (positive : (birth : WithTop ℝ) < death) :
      Fintype.card {occurrence // targetFamily.1 occurrence = birth ∧
        death ≤ targetFamily.2 occurrence} ≤
      Fintype.card {occurrence // sourceFamily.1 occurrence = birth ∧
        death ≤ sourceFamily.2 occurrence} := by
    let births := (insert (birth - 1)
      (Finset.univ.image sourceFamily.1 ∪ Finset.univ.image targetFamily.1)).filter
        (fun endpoint => endpoint < birth)
    have earlier_mem : birth - 1 ∈ births := by simp [births]
    let earlier := births.sup' ⟨_, earlier_mem⟩ id
    have earlier_before : earlier < birth := by
      apply (Finset.sup'_lt_iff _).mpr
      intro endpoint member
      exact (Finset.mem_filter.mp member).2
    have source_birth_lower : ∀ occurrence, sourceFamily.1 occurrence < birth →
        sourceFamily.1 occurrence ≤ earlier := by
      intro occurrence less
      apply Finset.le_sup' id
      simp [births, less]
    have target_birth_lower : ∀ occurrence, targetFamily.1 occurrence < birth →
        targetFamily.1 occurrence ≤ earlier := by
      intro occurrence less
      apply Finset.le_sup' id
      simp [births, less]
    let deaths := (insert (birth : WithTop ℝ)
      (Finset.univ.image sourceFamily.2 ∪ Finset.univ.image targetFamily.2)).filter
        (fun endpoint => endpoint < death)
    have birth_mem : (birth : WithTop ℝ) ∈ deaths := by simp [deaths, positive]
    let maximum := deaths.sup' ⟨_, birth_mem⟩ id
    have maximum_before : maximum < death := by
      apply (Finset.sup'_lt_iff _).mpr
      intro endpoint member
      exact (Finset.mem_filter.mp member).2
    have finite_maximum : maximum ≠ ⊤ := ne_top_of_lt maximum_before
    let sample := maximum.untop finite_maximum
    have sample_eq : (sample : WithTop ℝ) = maximum := WithTop.coe_untop _ _
    have birth_before : birth ≤ sample := by
      apply WithTop.coe_le_coe.mp
      rw [sample_eq]
      exact Finset.le_sup' id birth_mem
    have before : (sample : WithTop ℝ) < death := by rwa [sample_eq]
    have source_death_lower : ∀ occurrence, sourceFamily.2 occurrence < death →
        sourceFamily.2 occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [deaths, less]
    have target_death_lower : ∀ occurrence, targetFamily.2 occurrence < death →
        targetFamily.2 occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [deaths, less]
    have predicate {Index : Type v} (family : (Index → ℝ) × (Index → WithTop ℝ))
        (birth_lower : ∀ occurrence, family.1 occurrence < birth →
          family.1 occurrence ≤ earlier)
        (death_lower : ∀ occurrence, family.2 occurrence < death →
          family.2 occurrence ≤ (sample : WithTop ℝ)) :
        ∀ occurrence, (earlier < family.1 occurrence ∧ family.1 occurrence ≤ birth ∧
          (sample : WithTop ℝ) < family.2 occurrence) ↔
          (family.1 occurrence = birth ∧ death ≤ family.2 occurrence) := by
      intro occurrence
      constructor
      · intro supported
        exact ⟨le_antisymm supported.2.1 (le_of_not_gt fun less =>
          (not_lt_of_ge (birth_lower occurrence less)) supported.1),
          le_of_not_gt fun less => (not_lt_of_ge (death_lower occurrence less)) supported.2.2⟩
      · rintro ⟨sameBirth, survives⟩
        exact ⟨by simpa [sameBirth] using earlier_before, sameBirth.le, before.trans_le survives⟩
    have window := epi_birth_window_count sourceFamily targetFamily source_positive target_positive morphism surjective
      earlier birth sample earlier_before.le birth_before
    have source_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (predicate sourceFamily source_birth_lower source_death_lower))
    have target_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (predicate targetFamily target_birth_lower target_death_lower))
    exact source_card ▸ target_card ▸ window
  have ordinal_bound (occurrence : Target) :
      let ordinal := (targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩
      ordinal.val < Fintype.card {other // sourceFamily.1 other =
        targetFamily.1 occurrence ∧ targetFamily.2 occurrence ≤ sourceFamily.2 other} := by
    let birth := targetFamily.1 occurrence
    let ordinal := (targetEnumeration birth).symm ⟨occurrence, rfl⟩
    let initial : Fin (ordinal.val + 1) → {other // targetFamily.1 other = birth ∧
        targetFamily.2 occurrence ≤ targetFamily.2 other} := fun index =>
      ⟨(targetEnumeration birth ⟨index.val, by omega⟩).val,
        by
          constructor
          · exact (targetEnumeration birth _).property
          · have ordered : (⟨index.val, by omega⟩ : Fin (Fintype.card
                {other // targetFamily.1 other = birth})) ≤ ordinal := by
              exact Nat.le_of_lt_succ index.isLt
            simpa [ordinal] using target_sorted birth ordered⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have equal_values := congrArg Subtype.val equal
      have equal_indices := (targetEnumeration birth).injective (Subtype.ext equal_values)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // targetFamily.1 other = birth}) => index.val) equal_indices)
    have initial_count := Fintype.card_le_of_injective initial initial_injective
    have comparison := counts birth (targetFamily.2 occurrence) (target_positive occurrence)
    simp only [Fintype.card_fin] at initial_count
    exact lt_of_lt_of_le (Nat.lt_of_succ_le initial_count) comparison
  have class_bound (occurrence : Target) :
      ((targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {other // sourceFamily.1 other = targetFamily.1 occurrence} := by
    have eligible := ordinal_bound occurrence
    have total := Fintype.card_le_of_injective
      (fun other : {other // sourceFamily.1 other = targetFamily.1 occurrence ∧
          targetFamily.2 occurrence ≤ sourceFamily.2 other} =>
        (⟨other.val, other.property.1⟩ : {other //
          sourceFamily.1 other = targetFamily.1 occurrence}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {other // sourceFamily.1 other = targetFamily.1 occurrence} =>
          other.val) equal))
    exact eligible.trans_le total
  have class_bound' : ∀ birth (occurrence : {other // targetFamily.1 other = birth}),
      ((targetEnumeration birth).symm occurrence).val <
        Fintype.card {other // sourceFamily.1 other = birth} := by
    intro birth ⟨occurrence, sameBirth⟩
    subst birth
    exact class_bound occurrence
  let classMap : ∀ birth, {other // targetFamily.1 other = birth} ↪
      {other // sourceFamily.1 other = birth} := fun birth => {
    toFun := fun occurrence => sourceEnumeration birth
      ⟨((targetEnumeration birth).symm occurrence).val, class_bound' birth occurrence⟩
    inj' := by
      intro first second equal
      have sameOrdinal := (sourceEnumeration birth).injective equal
      apply (targetEnumeration birth).symm.injective
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // sourceFamily.1 other = birth}) => index.val) sameOrdinal) }
  let embedding := (Equiv.sigmaFiberEquiv targetFamily.1).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _) classMap).trans
      (Equiv.sigmaFiberEquiv sourceFamily.1).toEmbedding)
  let selected := fun occurrence => classMap (targetFamily.1 occurrence) ⟨occurrence, rfl⟩
  have death_bound (occurrence : Target) :
      targetFamily.2 occurrence ≤ sourceFamily.2 (selected occurrence).val := by
    by_contra not_after
    let ordinal := (targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩
    let below : {other // sourceFamily.1 other = targetFamily.1 occurrence ∧
        targetFamily.2 occurrence ≤ sourceFamily.2 other} → Fin ordinal.val := fun other =>
      ⟨((sourceEnumeration (targetFamily.1 occurrence)).symm
          ⟨other.val, other.property.1⟩).val, by
        by_contra not_less
        have ordered : (⟨ordinal.val, class_bound occurrence⟩ : Fin (Fintype.card
            {other // sourceFamily.1 other = targetFamily.1 occurrence})) ≤
          (sourceEnumeration (targetFamily.1 occurrence)).symm
            ⟨other.val, other.property.1⟩ := Nat.le_of_not_gt not_less
        have comparison := source_sorted (targetFamily.1 occurrence) ordered
        have comparison' : sourceFamily.2 other.val ≤
            sourceFamily.2 (selected occurrence).val := by
          simpa [selected, classMap] using comparison
        exact not_after (other.property.2.trans comparison')⟩
    have below_injective : Function.Injective below := by
      intro first second equal
      have equal_indices : (sourceEnumeration (targetFamily.1 occurrence)).symm
          ⟨first.val, first.property.1⟩ =
        (sourceEnumeration (targetFamily.1 occurrence)).symm
          ⟨second.val, second.property.1⟩ :=
        Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
      have equal_values := (sourceEnumeration (targetFamily.1 occurrence)).symm.injective
        equal_indices
      exact Subtype.ext (congrArg (fun other : {other //
        sourceFamily.1 other = targetFamily.1 occurrence} => other.val) equal_values)
    have bound := Fintype.card_le_of_injective below below_injective
    simp only [Fintype.card_fin] at bound
    exact (not_lt_of_ge bound) (ordinal_bound occurrence)
  refine ⟨embedding, ?_⟩
  intro occurrence
  rw [show embedding occurrence = (selected occurrence).val from rfl]
  exact ⟨death_bound occurrence, (selected occurrence).property, by simp [selected, classMap]⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem mono_cokernel_trim_estimates {Source Target : Type v}
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
           · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives]
           · have zero : coordinates.val occurrence = 0 :=
               coordinates.property occurrence (by tauto)
             simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives, zero]
         map_comp {source middle target} first second := by
           classical
           ext coordinates occurrence
           change (if (target : WithTop ℝ) < family.2 occurrence then
             (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0) coordinates.val =
             (if (target : WithTop ℝ) < family.2 occurrence then
               (LinearMap.proj occurrence : (Index → K) →ₗ[K] K) else 0)
               (fun middleOccurrence => (if (middle : WithTop ℝ) <
                 family.2 middleOccurrence then
                   (LinearMap.proj middleOccurrence : (Index → K) →ₗ[K] K) else 0)
                 coordinates.val)
           by_cases survives : (target : WithTop ℝ) < family.2 occurrence
           · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
               lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
             simp only [if_pos survives, LinearMap.proj_apply, if_pos middle_survives]
           · simp only [if_neg survives, LinearMap.zero_apply] } : ℝ ⥤ ModuleCat.{max u v} K);
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (injective : ∀ time, Function.Injective (morphism.app time).hom)
      (sourceEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // sourceFamily.2 occurrence = death}) ≃
          {occurrence // sourceFamily.2 occurrence = death})
      (targetEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // targetFamily.2 occurrence = death}) ≃
          {occurrence // targetFamily.2 occurrence = death})
      (source_sorted : ∀ death, Monotone fun ordinal =>
        sourceFamily.1 (sourceEnumeration death ordinal).val)
      (target_sorted : ∀ death, Monotone fun ordinal =>
        targetFamily.1 (targetEnumeration death ordinal).val)
      (embedding : Source ↪ Target)
      (ordered : ∀ occurrence,
        targetFamily.1 (embedding occurrence) ≤ sourceFamily.1 occurrence ∧
        ∃ sameDeath : targetFamily.2 (embedding occurrence) = sourceFamily.2 occurrence,
          ((targetEnumeration (sourceFamily.2 occurrence)).symm
            ⟨embedding occurrence, sameDeath⟩).val =
          ((sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val)
      (eta : ℝ) (nonnegative : 0 ≤ eta)
      (cokernel_trivial : ∀ time,
        LinearMap.range (intervalArrow targetFamily time (time + eta) (by linarith)) ≤
          LinearMap.range (morphism.app (time + eta)).hom),
      (∀ occurrence, sourceFamily.1 occurrence ≤ targetFamily.1 (embedding occurrence) + eta) ∧
      (∀ occurrence, ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence → ∃ original, embedding original = occurrence) ∧
      (∀ occurrence, targetFamily.2 occurrence = ⊤ →
        ∃ original, embedding original = occurrence) ∧
      (eta = 0 → Function.Surjective embedding ∧
        ∀ occurrence, sourceFamily.1 occurrence = targetFamily.1 (embedding occurrence)) := by
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
        simpa [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, survives] using coordinates.property occurrence (by tauto)
      · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, survives]));
  let intervalSum := fun {Index : Type v}
      (family : (Index → ℝ) × (Index → WithTop ℝ)) =>
    ({ obj time := ModuleCat.of K (intervalSpace family time)
       map {source target} arrow :=
         ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
       map_id time := by
         classical
         ext coordinates occurrence
         by_cases survives : (time : WithTop ℝ) < family.2 occurrence
         · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives]
         · have zero : coordinates.val occurrence = 0 :=
             coordinates.property occurrence (by tauto)
           simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives, zero]
       map_comp {source middle target} first second := by
         classical
         ext coordinates occurrence
         by_cases survives : (target : WithTop ℝ) < family.2 occurrence
         · have middle_survives : (middle : WithTop ℝ) < family.2 occurrence :=
             lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
           simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives, middle_survives]
         · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, apply_ite, ite_apply, survives] } : ℝ ⥤ ModuleCat.{max u v} K);
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (injective : ∀ time, Function.Injective (morphism.app time).hom)
      (sourceEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // sourceFamily.2 occurrence = death}) ≃
          {occurrence // sourceFamily.2 occurrence = death})
      (targetEnumeration : ∀ death, Fin (Fintype.card
        {occurrence // targetFamily.2 occurrence = death}) ≃
          {occurrence // targetFamily.2 occurrence = death})
      (source_sorted : ∀ death, Monotone fun ordinal =>
        sourceFamily.1 (sourceEnumeration death ordinal).val)
      (target_sorted : ∀ death, Monotone fun ordinal =>
        targetFamily.1 (targetEnumeration death ordinal).val)
      (embedding : Source ↪ Target)
      (ordered : ∀ occurrence,
        targetFamily.1 (embedding occurrence) ≤ sourceFamily.1 occurrence ∧
        ∃ sameDeath : targetFamily.2 (embedding occurrence) = sourceFamily.2 occurrence,
          ((targetEnumeration (sourceFamily.2 occurrence)).symm
            ⟨embedding occurrence, sameDeath⟩).val =
          ((sourceEnumeration (sourceFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val)
      (eta : ℝ) (nonnegative : 0 ≤ eta)
      (cokernel_trivial : ∀ time,
        LinearMap.range (intervalArrow targetFamily time (time + eta) (by linarith)) ≤
          LinearMap.range (morphism.app (time + eta)).hom),
      (∀ occurrence, sourceFamily.1 occurrence ≤ targetFamily.1 (embedding occurrence) + eta) ∧
      (∀ occurrence, ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence → ∃ original, embedding original = occurrence) ∧
      (∀ occurrence, targetFamily.2 occurrence = ⊤ →
        ∃ original, embedding original = occurrence) ∧
      (eta = 0 → Function.Surjective embedding ∧
        ∀ occurrence, sourceFamily.1 occurrence = targetFamily.1 (embedding occurrence))
  intro morphism injective sourceEnumeration targetEnumeration source_sorted target_sorted
    embedding ordered eta nonnegative cokernel_trivial
  let Trim := {occurrence : Target //
    ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) < targetFamily.2 occurrence}
  let trimFamily : (Trim → ℝ) × (Trim → WithTop ℝ) :=
    ⟨fun occurrence => targetFamily.1 occurrence.val + eta,
      fun occurrence => targetFamily.2 occurrence.val⟩
  have trim_positive : ∀ occurrence, (trimFamily.1 occurrence : WithTop ℝ) <
      trimFamily.2 occurrence := fun occurrence => occurrence.property
  let inclusion : ∀ time, intervalSpace trimFamily time →ₗ[K]
      intervalSpace targetFamily time := fun time =>
    (((LinearMap.pi fun occurrence : Target =>
        if long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            targetFamily.2 occurrence then LinearMap.proj (⟨occurrence, long⟩ : Trim)
        else 0).domRestrict (intervalSpace trimFamily time)).codRestrict
      (intervalSpace targetFamily time) (by
        intro coordinates occurrence unsupported
        by_cases long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            targetFamily.2 occurrence
        · have zero : coordinates.val ⟨occurrence, long⟩ = 0 := by
            apply coordinates.property
            intro supported
            exact unsupported ⟨by dsimp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, trimFamily] at supported; linarith [supported.1],
              supported.2⟩
          simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, ← WithTop.coe_add, long, zero]
        · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, ← WithTop.coe_add, long]))
  have inclusion_injective : ∀ time, Function.Injective (inclusion time) := by
    intro time first second equal
    apply Subtype.ext
    funext occurrence
    have coordinate := congrArg (fun vector => vector.val occurrence.val) equal
    simpa [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, inclusion, ← WithTop.coe_add, occurrence.property] using coordinate
  let before : ∀ time, intervalSpace trimFamily time →ₗ[K]
      intervalSpace targetFamily (time - eta) := fun time =>
    (((LinearMap.pi fun occurrence : Target =>
        if long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            targetFamily.2 occurrence then LinearMap.proj (⟨occurrence, long⟩ : Trim)
        else 0).domRestrict (intervalSpace trimFamily time)).codRestrict
      (intervalSpace targetFamily (time - eta)) (by
        intro coordinates occurrence unsupported
        by_cases long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            targetFamily.2 occurrence
        · have zero : coordinates.val ⟨occurrence, long⟩ = 0 := by
            apply coordinates.property
            intro supported
            exact unsupported ⟨by dsimp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, trimFamily] at supported; linarith [supported.1],
              lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by linarith)) supported.2⟩
          simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, ← WithTop.coe_add, long, zero]
        · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, ← WithTop.coe_add, long]))
  have inclusion_shift : ∀ time,
      (intervalArrow targetFamily (time - eta) time (by linarith)).comp (before time) =
        inclusion time := by
    intro time
    ext coordinates occurrence
    by_cases long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence
    · by_cases survives : (time : WithTop ℝ) < targetFamily.2 occurrence
      · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, before, inclusion, ← WithTop.coe_add, long, survives]
      · have zero : coordinates.val ⟨occurrence, long⟩ = 0 :=
          coordinates.property _ (by intro supported; exact survives supported.2)
        simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, before, inclusion, ← WithTop.coe_add, long, survives, zero]
    · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, intervalArrow, before, inclusion, ← WithTop.coe_add, long]
  have inclusion_range_eq (time : ℝ) : LinearMap.range (inclusion time) =
      LinearMap.range (intervalArrow targetFamily (time - eta) time (by linarith)) := by
    apply le_antisymm
    · intro vector member
      obtain ⟨coordinates, rfl⟩ := member
      exact ⟨before time coordinates,
        congrArg (fun linear => linear coordinates) (inclusion_shift time)⟩
    · intro vector member
      obtain ⟨coordinates, rfl⟩ := member
      let restricted : intervalSpace trimFamily time := ⟨fun occurrence =>
        if (time : WithTop ℝ) < targetFamily.2 occurrence.val then
          coordinates.val occurrence.val else 0, by
        intro occurrence unsupported
        by_cases survives : (time : WithTop ℝ) < targetFamily.2 occurrence.val
        · have not_born : ¬ targetFamily.1 occurrence.val ≤ time - eta := by
            intro born
            exact unsupported ⟨by dsimp [trimFamily]; linarith, survives⟩
          have zero : coordinates.val occurrence.val = 0 :=
            coordinates.property occurrence.val (by tauto)
          simp [survives, zero]
        · simp [survives]⟩
      refine ⟨restricted, ?_⟩
      apply Subtype.ext
      funext occurrence
      by_cases long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
          targetFamily.2 occurrence
      · by_cases survives : (time : WithTop ℝ) < targetFamily.2 occurrence <;>
          simp [inclusion, intervalArrow, restricted, LinearMap.proj, LinearMap.pi,
            apply_ite, ite_apply, ← WithTop.coe_add, long, survives]
      · by_cases survives : (time : WithTop ℝ) < targetFamily.2 occurrence
        · have not_born : ¬ targetFamily.1 occurrence ≤ time - eta := by
            intro born
            exact long (lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by linarith)) survives)
          have zero : coordinates.val occurrence = 0 :=
            coordinates.property occurrence (by tauto)
          simp [inclusion, intervalArrow, LinearMap.proj, LinearMap.pi,
            ← WithTop.coe_add, long, survives, zero]
        · simp [inclusion, intervalArrow, LinearMap.proj, LinearMap.pi,
            ← WithTop.coe_add, long, survives]
  have reindexed (earlier later : ℝ) (sum : earlier + eta = later) :
      LinearMap.range (intervalArrow targetFamily earlier later (by linarith)) ≤
        LinearMap.range (morphism.app later).hom := by
    subst later
    exact cokernel_trivial earlier
  have inclusion_range : ∀ time, LinearMap.range (inclusion time) ≤
      LinearMap.range (morphism.app time).hom := by
    intro time vector member
    rw [inclusion_range_eq time] at member
    exact reindexed (time - eta) time (sub_add_cancel time eta) member
  let lift : ∀ time, intervalSpace trimFamily time →ₗ[K]
      intervalSpace sourceFamily time := fun time =>
    (LinearEquiv.ofInjective (morphism.app time).hom (injective time)).symm.toLinearMap.comp
      ((inclusion time).codRestrict (LinearMap.range (morphism.app time).hom)
        (fun coordinates => inclusion_range time ⟨coordinates, rfl⟩))
  have lift_equation : ∀ time coordinates,
      (morphism.app time).hom (lift time coordinates) = inclusion time coordinates := by
    intro time coordinates
    exact LinearEquiv.ofInjective_symm_apply (h := injective time) (morphism.app time).hom
      ⟨inclusion time coordinates, inclusion_range time ⟨coordinates, rfl⟩⟩
  have lift_injective : ∀ time, Function.Injective (lift time) := by
    intro time first second equal
    apply inclusion_injective time
    rw [← lift_equation time first, ← lift_equation time second, equal]
  have inclusion_natural : ∀ source target (comparison : source ≤ target),
      (inclusion target).comp (intervalArrow trimFamily source target comparison) =
        (intervalArrow targetFamily source target comparison).comp (inclusion source) := by
    intro source target comparison
    ext coordinates occurrence
    by_cases long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence
    · by_cases survives : (target : WithTop ℝ) < targetFamily.2 occurrence <;>
        simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, inclusion, intervalArrow, trimFamily, ← WithTop.coe_add, long, survives]
    · simp [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, inclusion, intervalArrow, ← WithTop.coe_add, long]
  let lifted : intervalSum trimFamily ⟶ intervalSum sourceFamily := {
    app time := ModuleCat.ofHom (lift time)
    naturality := by
      intro source target arrow
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro coordinates
      apply injective target
      change (morphism.app target).hom
          (lift target (intervalArrow trimFamily source target (leOfHom arrow) coordinates)) =
        (morphism.app target).hom
          (intervalArrow sourceFamily source target (leOfHom arrow) (lift source coordinates))
      rw [lift_equation]
      have square' : (morphism.app target).hom
          (intervalArrow sourceFamily source target (leOfHom arrow) (lift source coordinates)) =
        intervalArrow targetFamily source target (leOfHom arrow)
          ((morphism.app source).hom (lift source coordinates)) := by
        exact (congrArg (fun map => map.hom (lift source coordinates))
          (morphism.naturality arrow))
      rw [square', lift_equation]
      exact congrArg (fun linear => linear coordinates)
        (inclusion_natural source target (leOfHom arrow)) }
  have sorted : ∀ {Index : Type v} [Fintype Index] (key : Index → ℝ),
      ∃ enumeration : Fin (Fintype.card Index) ≃ Index,
        Monotone fun ordinal => key (enumeration ordinal) := by
    intro Index finite key
    let ranking : Index → ℝ ×ₗ Fin (Fintype.card Index) := fun occurrence =>
      toLex (key occurrence, Fintype.equivFin Index occurrence)
    have ranking_injective : Function.Injective ranking := by
      intro first second equal
      exact (Fintype.equivFin Index).injective
        (congrArg (fun pair => (ofLex pair).2) equal)
    letI : LinearOrder Index := LinearOrder.lift' ranking ranking_injective
    refine ⟨(monoEquivOfFin Index rfl).toEquiv, ?_⟩
    intro first second comparison
    exact Prod.Lex.monotone_fst _ _ ((monoEquivOfFin Index rfl).monotone comparison)
  let trimEnumeration := fun death => Classical.choose
    (sorted (fun occurrence : {occurrence // trimFamily.2 occurrence = death} =>
      trimFamily.1 occurrence.val))
  obtain ⟨trimEmbedding, trim_ordered⟩ := mono_ordered_occurrence_injection
    trimFamily sourceFamily trim_positive source_positive lifted lift_injective
    trimEnumeration sourceEnumeration
    (fun death => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // trimFamily.2 occurrence = death} => trimFamily.1 occurrence.val)))
    source_sorted
  have prefix_bound (occurrence : Target)
      (long : ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 occurrence) :
      ((targetEnumeration (targetFamily.2 occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {original // sourceFamily.1 original ≤ targetFamily.1 occurrence + eta ∧
          sourceFamily.2 original = targetFamily.2 occurrence} := by
    let death := targetFamily.2 occurrence
    let ordinal := (targetEnumeration death).symm ⟨occurrence, rfl⟩
    let initialOccurrence : Fin (ordinal.val + 1) → Target := fun index =>
      (targetEnumeration death ⟨index.val, by omega⟩).val
    have initial_birth : ∀ index, targetFamily.1 (initialOccurrence index) ≤
        targetFamily.1 occurrence := by
      intro index
      have comparison : (⟨index.val, by omega⟩ : Fin (Fintype.card
          {other // targetFamily.2 other = death})) ≤ ordinal := by
        exact Nat.le_of_lt_succ index.isLt
      simpa [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, initialOccurrence, ordinal] using target_sorted death comparison
    have initial_death : ∀ index, targetFamily.2 (initialOccurrence index) = death :=
      fun index => (targetEnumeration death _).property
    let initialTrim : Fin (ordinal.val + 1) → Trim := fun index =>
      ⟨initialOccurrence index, by
        rw [initial_death]
        exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by linarith [initial_birth index])) long⟩
    let initial : Fin (ordinal.val + 1) → {original // sourceFamily.1 original ≤
        targetFamily.1 occurrence + eta ∧ sourceFamily.2 original = death} := fun index =>
      ⟨trimEmbedding (initialTrim index),
        (trim_ordered (initialTrim index)).1.trans (by
          change targetFamily.1 (initialOccurrence index) + eta ≤ _
          linarith [initial_birth index]),
        (trim_ordered (initialTrim index)).2.choose.trans (initial_death index)⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have sameTrim := trimEmbedding.injective (congrArg Subtype.val equal)
      have sameOccurrence := congrArg (fun other : Trim => other.val) sameTrim
      have sameOrdinal := (targetEnumeration death).injective (Subtype.ext sameOccurrence)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // targetFamily.2 other = death}) => index.val) sameOrdinal)
    have count := Fintype.card_le_of_injective initial initial_injective
    simp only [Fintype.card_fin] at count
    exact Nat.lt_of_succ_le count
  have ordered_fiber (death : WithTop ℝ)
      (occurrence : {other // sourceFamily.2 other = death}) :
      ∃ sameDeath : targetFamily.2 (embedding occurrence.val) = death,
        ((targetEnumeration death).symm ⟨embedding occurrence.val, sameDeath⟩).val =
          ((sourceEnumeration death).symm occurrence).val := by
    rcases occurrence with ⟨occurrence, rfl⟩
    exact (ordered occurrence).2
  have prefix_bound_fiber (death : WithTop ℝ)
      (occurrence : {other // targetFamily.2 other = death})
      (long : ((targetFamily.1 occurrence.val + eta : ℝ) : WithTop ℝ) < death) :
      ((targetEnumeration death).symm occurrence).val <
        Fintype.card {original // sourceFamily.1 original ≤ targetFamily.1 occurrence.val + eta ∧
          sourceFamily.2 original = death} := by
    rcases occurrence with ⟨occurrence, rfl⟩
    exact prefix_bound occurrence long
  have coverage : ∀ occurrence, ((targetFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
      targetFamily.2 occurrence → ∃ original, embedding original = occurrence := by
    intro occurrence long
    let death := targetFamily.2 occurrence
    let ordinal := (targetEnumeration death).symm ⟨occurrence, rfl⟩
    have total := Fintype.card_le_of_injective
      (fun other : {original // sourceFamily.1 original ≤ targetFamily.1 occurrence + eta ∧
          sourceFamily.2 original = death} =>
        (⟨other.val, other.property.2⟩ : {original // sourceFamily.2 original = death}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {original // sourceFamily.2 original = death} => other.val) equal))
    have within : ordinal.val < Fintype.card {original // sourceFamily.2 original = death} :=
      (prefix_bound occurrence long).trans_le total
    let original := sourceEnumeration death ⟨ordinal.val, within⟩
    refine ⟨original.val, ?_⟩
    obtain ⟨sameDeath, sameOrdinal⟩ := ordered_fiber death original
    have equality : ((targetEnumeration death).symm
        ⟨embedding original.val, sameDeath⟩).val = ordinal.val := by
      simpa only [original, Equiv.symm_apply_apply] using sameOrdinal
    have equalIndex : (targetEnumeration death).symm
        ⟨embedding original.val, sameDeath⟩ = ordinal := Fin.ext equality
    have equalOccurrence := (targetEnumeration death).symm.injective equalIndex
    exact congrArg (fun other : {original // targetFamily.2 original = death} =>
      other.val) equalOccurrence
  have bounds : ∀ occurrence, sourceFamily.1 occurrence ≤
      targetFamily.1 (embedding occurrence) + eta := by
    intro occurrence
    obtain ⟨sameDeath, sameOrdinal⟩ := (ordered occurrence).2
    by_cases long : ((targetFamily.1 (embedding occurrence) + eta : ℝ) : WithTop ℝ) <
        targetFamily.2 (embedding occurrence)
    · by_contra not_before
      let death := sourceFamily.2 occurrence
      let ordinal := (sourceEnumeration death).symm ⟨occurrence, rfl⟩
      let below : {original // sourceFamily.1 original ≤
          targetFamily.1 (embedding occurrence) + eta ∧ sourceFamily.2 original = death} →
          Fin ordinal.val := fun original =>
        ⟨((sourceEnumeration death).symm ⟨original.val, original.property.2⟩).val, by
          by_contra not_less
          have comparison : ordinal ≤ (sourceEnumeration death).symm
              ⟨original.val, original.property.2⟩ := Nat.le_of_not_gt not_less
          have births := source_sorted death comparison
          have born : sourceFamily.1 occurrence ≤ sourceFamily.1 original.val := by
            simpa [LinearMap.proj, LinearMap.pi, LinearMap.proj_apply, LinearMap.pi_apply, apply_ite, ite_apply, ordinal] using births
          exact not_before (born.trans original.property.1)⟩
      have below_injective : Function.Injective below := by
        intro first second equal
        have equalIndex : (sourceEnumeration death).symm ⟨first.val, first.property.2⟩ =
            (sourceEnumeration death).symm ⟨second.val, second.property.2⟩ :=
          Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
        exact Subtype.ext (congrArg
          (fun other : {original // sourceFamily.2 original = death} => other.val)
          ((sourceEnumeration death).symm.injective equalIndex))
      have count := Fintype.card_le_of_injective below below_injective
      simp only [Fintype.card_fin] at count
      have lower := prefix_bound_fiber death ⟨embedding occurrence, sameDeath⟩ (by
        simpa only [sameDeath] using long)
      rw [sameOrdinal] at lower
      exact (not_lt_of_ge count) lower
    · have positive := source_positive occurrence
      have death_bound := le_of_not_gt long
      rw [sameDeath] at death_bound
      exact WithTop.coe_le_coe.mp (le_of_lt (positive.trans_le death_bound))
  refine ⟨bounds, coverage, ?_, ?_⟩
  · intro occurrence essential
    apply coverage occurrence
    rw [essential]
    exact WithTop.coe_lt_top _
  · intro zero
    subst eta
    refine ⟨fun occurrence => coverage occurrence (by simpa using target_positive occurrence), ?_⟩
    intro occurrence
    exact le_antisymm (by simpa using bounds occurrence) (ordered occurrence).1

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem epi_kernel_trim_estimates {Source Target : Type v}
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
    ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
      (sourceEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // sourceFamily.1 occurrence = birth}) ≃
          {occurrence // sourceFamily.1 occurrence = birth})
      (targetEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // targetFamily.1 occurrence = birth}) ≃
          {occurrence // targetFamily.1 occurrence = birth})
      (source_sorted : ∀ birth, Antitone fun ordinal =>
        sourceFamily.2 (sourceEnumeration birth ordinal).val)
      (target_sorted : ∀ birth, Antitone fun ordinal =>
        targetFamily.2 (targetEnumeration birth ordinal).val)
      (embedding : Target ↪ Source)
      (ordered : ∀ occurrence,
        targetFamily.2 occurrence ≤ sourceFamily.2 (embedding occurrence) ∧
        ∃ sameBirth : sourceFamily.1 (embedding occurrence) = targetFamily.1 occurrence,
          ((sourceEnumeration (targetFamily.1 occurrence)).symm
            ⟨embedding occurrence, sameBirth⟩).val =
          ((targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val)
      (eta : ℝ) (nonnegative : 0 ≤ eta)
      (kernel_trivial : ∀ time, LinearMap.ker (morphism.app time).hom ≤
        LinearMap.ker (intervalArrow sourceFamily time (time + eta) (by linarith))),
      (∀ occurrence, WithTop.map (fun endpoint : ℝ => endpoint - eta)
        (sourceFamily.2 (embedding occurrence)) ≤ targetFamily.2 occurrence) ∧
      (∀ occurrence (sourceDeath targetDeath : ℝ),
        sourceFamily.2 (embedding occurrence) = (sourceDeath : WithTop ℝ) →
        targetFamily.2 occurrence = (targetDeath : WithTop ℝ) →
        sourceDeath ≤ targetDeath + eta) ∧
      (∀ occurrence, ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        sourceFamily.2 occurrence → ∃ original, embedding original = occurrence) ∧
      (∀ occurrence, sourceFamily.2 (embedding occurrence) = ⊤ ↔
        targetFamily.2 occurrence = ⊤) ∧
      (∀ occurrence, sourceFamily.2 occurrence = ⊤ →
        ∃ original, embedding original = occurrence) ∧
      (eta = 0 → Function.Surjective embedding ∧
        ∀ occurrence, sourceFamily.2 (embedding occurrence) = targetFamily.2 occurrence) := by
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
  change ∀ (morphism : intervalSum sourceFamily ⟶ intervalSum targetFamily)
      (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
      (sourceEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // sourceFamily.1 occurrence = birth}) ≃
          {occurrence // sourceFamily.1 occurrence = birth})
      (targetEnumeration : ∀ birth, Fin (Fintype.card
        {occurrence // targetFamily.1 occurrence = birth}) ≃
          {occurrence // targetFamily.1 occurrence = birth})
      (source_sorted : ∀ birth, Antitone fun ordinal =>
        sourceFamily.2 (sourceEnumeration birth ordinal).val)
      (target_sorted : ∀ birth, Antitone fun ordinal =>
        targetFamily.2 (targetEnumeration birth ordinal).val)
      (embedding : Target ↪ Source)
      (ordered : ∀ occurrence,
        targetFamily.2 occurrence ≤ sourceFamily.2 (embedding occurrence) ∧
        ∃ sameBirth : sourceFamily.1 (embedding occurrence) = targetFamily.1 occurrence,
          ((sourceEnumeration (targetFamily.1 occurrence)).symm
            ⟨embedding occurrence, sameBirth⟩).val =
          ((targetEnumeration (targetFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val)
      (eta : ℝ) (nonnegative : 0 ≤ eta)
      (kernel_trivial : ∀ time, LinearMap.ker (morphism.app time).hom ≤
        LinearMap.ker (intervalArrow sourceFamily time (time + eta) (by linarith))),
      (∀ occurrence, WithTop.map (fun endpoint : ℝ => endpoint - eta)
        (sourceFamily.2 (embedding occurrence)) ≤ targetFamily.2 occurrence) ∧
      (∀ occurrence (sourceDeath targetDeath : ℝ),
        sourceFamily.2 (embedding occurrence) = (sourceDeath : WithTop ℝ) →
        targetFamily.2 occurrence = (targetDeath : WithTop ℝ) →
        sourceDeath ≤ targetDeath + eta) ∧
      (∀ occurrence, ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        sourceFamily.2 occurrence → ∃ original, embedding original = occurrence) ∧
      (∀ occurrence, sourceFamily.2 (embedding occurrence) = ⊤ ↔
        targetFamily.2 occurrence = ⊤) ∧
      (∀ occurrence, sourceFamily.2 occurrence = ⊤ →
        ∃ original, embedding original = occurrence) ∧
      (eta = 0 → Function.Surjective embedding ∧
        ∀ occurrence, sourceFamily.2 (embedding occurrence) = targetFamily.2 occurrence)
  intro morphism surjective sourceEnumeration targetEnumeration source_sorted target_sorted
    embedding ordered eta nonnegative kernel_trivial
  let Trim := {occurrence : Source //
    ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence}
  let trimFamily : (Trim → ℝ) × (Trim → WithTop ℝ) :=
    ⟨fun occurrence => sourceFamily.1 occurrence.val,
      fun occurrence => WithTop.map (fun endpoint : ℝ => endpoint - eta)
        (sourceFamily.2 occurrence.val)⟩
  have shift_test (occurrence : Source) (time : ℝ) :
      (time : WithTop ℝ) < WithTop.map (fun endpoint : ℝ => endpoint - eta)
        (sourceFamily.2 occurrence) ↔
        ((time + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence := by
    cases sourceFamily.2 occurrence using WithTop.recTopCoe <;>
      simp only [WithTop.map_top, WithTop.map_coe, WithTop.coe_lt_top, WithTop.coe_lt_coe] <;>
      constructor <;> intro comparison <;> linarith
  have shift_monotone : Monotone (WithTop.map (fun endpoint : ℝ => endpoint - eta)) := by
    intro first second comparison
    cases first using WithTop.recTopCoe <;> cases second using WithTop.recTopCoe <;>
      simp_all only [WithTop.map_top, WithTop.map_coe, le_top, WithTop.top_le_iff,
        WithTop.coe_ne_top, WithTop.coe_le_coe] <;> linarith
  have shift_below (death : WithTop ℝ) (birth : ℝ) :
      WithTop.map (fun endpoint : ℝ => endpoint - eta) death ≤ (birth : WithTop ℝ) ↔
        death ≤ ((birth + eta : ℝ) : WithTop ℝ) := by
    cases death using WithTop.recTopCoe <;>
      simp only [WithTop.map_top, WithTop.map_coe, WithTop.not_top_le_coe,
        WithTop.coe_le_coe] <;> constructor <;> intro comparison <;> linarith
  have trim_positive : ∀ occurrence, (trimFamily.1 occurrence : WithTop ℝ) <
      trimFamily.2 occurrence := fun occurrence =>
    (shift_test occurrence.val (sourceFamily.1 occurrence.val)).mpr occurrence.property
  let quotient : ∀ time, intervalSpace sourceFamily time →ₗ[K]
      intervalSpace trimFamily time := fun time =>
    (((LinearMap.pi fun occurrence : Trim =>
        if ((time + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence.val then
          (LinearMap.proj occurrence.val : (Source → K) →ₗ[K] K) else 0).domRestrict
      (intervalSpace sourceFamily time)).codRestrict (intervalSpace trimFamily time) (by
        intro coordinates occurrence unsupported
        by_cases survives : ((time + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence.val
        · have not_born : ¬ sourceFamily.1 occurrence.val ≤ time := by
            intro born
            exact unsupported ⟨born, (shift_test occurrence.val time).mpr survives⟩
          have zero : coordinates.val occurrence.val = 0 :=
            coordinates.property occurrence.val (by tauto)
          simp [LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives, zero]
        · simp [LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives]))
  have quotient_surjective : ∀ time, Function.Surjective (quotient time) := by
    intro time coordinates
    let extended : intervalSpace sourceFamily time := ⟨fun occurrence =>
      if long : ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
          sourceFamily.2 occurrence then coordinates.val ⟨occurrence, long⟩ else 0, by
      intro occurrence unsupported
      by_cases long : ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
          sourceFamily.2 occurrence
      · have zero : coordinates.val ⟨occurrence, long⟩ = 0 := by
          apply coordinates.property
          intro supported
          exact unsupported ⟨supported.1, lt_of_le_of_lt
            (WithTop.coe_le_coe.mpr (by linarith))
            ((shift_test occurrence time).mp supported.2)⟩
        change (if long : ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            sourceFamily.2 occurrence then coordinates.val ⟨occurrence, long⟩ else 0) = 0
        simpa only [dif_pos long] using zero
      · simp [← WithTop.coe_add, long]⟩
    refine ⟨extended, ?_⟩
    apply Subtype.ext
    funext occurrence
    by_cases survives : ((time + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence.val
    · simp [quotient, extended, LinearMap.proj, LinearMap.pi,
        ← WithTop.coe_add, survives, occurrence.property]
    · have zero : coordinates.val occurrence = 0 := coordinates.property occurrence (by
        intro supported
        exact survives ((shift_test occurrence.val time).mp supported.2))
      simp [quotient, extended, LinearMap.proj, LinearMap.pi,
        ← WithTop.coe_add, survives, zero]
  have quotient_kernel : ∀ time, LinearMap.ker (quotient time) =
      LinearMap.ker (intervalArrow sourceFamily time (time + eta) (by linarith)) := by
    intro time
    ext coordinates
    simp only [LinearMap.mem_ker]
    constructor
    · intro killed
      apply Subtype.ext
      funext occurrence
      by_cases survives : ((time + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence
      · by_cases long : ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
            sourceFamily.2 occurrence
        · have zero := congrArg (fun vector => vector.val (⟨occurrence, long⟩ : Trim)) killed
          have zero' : coordinates.val occurrence = 0 := by
            simpa [quotient, LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives] using zero
          simp [intervalArrow, LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives, zero']
        · have not_born : ¬ sourceFamily.1 occurrence ≤ time := by
            intro born
            exact long (lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by linarith)) survives)
          have zero : coordinates.val occurrence = 0 :=
            coordinates.property occurrence (by tauto)
          simp [intervalArrow, LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives, zero]
      · simp [intervalArrow, LinearMap.proj, LinearMap.pi, ← WithTop.coe_add, survives]
    · intro killed
      apply Subtype.ext
      funext occurrence
      have zero := congrArg (fun vector => vector.val occurrence.val) killed
      simpa [quotient, intervalArrow, LinearMap.proj, LinearMap.pi] using zero
  have quotient_natural : ∀ source target (comparison : source ≤ target),
      (quotient target).comp (intervalArrow sourceFamily source target comparison) =
        (intervalArrow trimFamily source target comparison).comp (quotient source) := by
    intro source target comparison
    ext coordinates occurrence
    by_cases survives : ((target + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence.val
    · have source_survives : ((source + eta : ℝ) : WithTop ℝ) <
          sourceFamily.2 occurrence.val := lt_of_le_of_lt
        (WithTop.coe_le_coe.mpr (by linarith)) survives
      have target_survives : (target : WithTop ℝ) < sourceFamily.2 occurrence.val :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by linarith)) survives
      have trimmed_survives := (shift_test occurrence.val target).mpr survives
      simp [quotient, intervalArrow, trimFamily, LinearMap.proj, LinearMap.pi,
        ← WithTop.coe_add, survives, source_survives, target_survives, trimmed_survives]
    · have trimmed_dies : ¬ (target : WithTop ℝ) < trimFamily.2 occurrence := by
        exact fun supported => survives ((shift_test occurrence.val target).mp supported)
      simp [quotient, intervalArrow, LinearMap.proj, LinearMap.pi,
        ← WithTop.coe_add, survives, trimmed_dies]
  have quotient_vanishes : ∀ time, LinearMap.ker (morphism.app time).hom ≤
      LinearMap.ker (quotient time) := by
    intro time
    rw [quotient_kernel]
    exact kernel_trivial time
  let factor : ∀ time, intervalSpace targetFamily time →ₗ[K]
      intervalSpace trimFamily time := fun time =>
    ((LinearMap.ker (morphism.app time).hom).liftQ (quotient time)
      (quotient_vanishes time)).comp
        ((morphism.app time).hom.quotKerEquivOfSurjective (surjective time)).symm.toLinearMap
  have factor_equation : ∀ time coordinates,
      factor time ((morphism.app time).hom coordinates) = quotient time coordinates := by
    intro time coordinates
    dsimp only [factor, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    have inverse := LinearMap.quotKerEquivOfSurjective_symm_apply
      (f := (morphism.app time).hom) (surjective time) coordinates
    rw [inverse]
    rfl
  have factor_surjective : ∀ time, Function.Surjective (factor time) := by
    intro time coordinates
    obtain ⟨original, equation⟩ := quotient_surjective time coordinates
    exact ⟨(morphism.app time).hom original, (factor_equation time original).trans equation⟩
  let factored : intervalSum targetFamily ⟶ intervalSum trimFamily := {
    app time := ModuleCat.ofHom (factor time)
    naturality := by
      intro source target arrow
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro coordinates
      obtain ⟨original, rfl⟩ := surjective source coordinates
      change factor target (intervalArrow targetFamily source target (leOfHom arrow)
          ((morphism.app source).hom original)) =
        intervalArrow trimFamily source target (leOfHom arrow)
          (factor source ((morphism.app source).hom original))
      have natural := congrArg (fun map => map.hom original) (morphism.naturality arrow)
      change (morphism.app target).hom (intervalArrow sourceFamily source target
          (leOfHom arrow) original) = intervalArrow targetFamily source target
          (leOfHom arrow) ((morphism.app source).hom original) at natural
      rw [← natural, factor_equation, factor_equation]
      exact congrArg (fun linear => linear original) (quotient_natural source target (leOfHom arrow)) }
  have sorted : ∀ {Index : Type v} [Fintype Index] (key : Index → WithTop ℝ),
      ∃ enumeration : Fin (Fintype.card Index) ≃ Index,
        Antitone fun ordinal => key (enumeration ordinal) := by
    intro Index finite key
    let ranking : Index → (WithTop ℝ)ᵒᵈ ×ₗ Fin (Fintype.card Index) := fun occurrence =>
      toLex (OrderDual.toDual (key occurrence), Fintype.equivFin Index occurrence)
    have ranking_injective : Function.Injective ranking := by
      intro first second equal
      exact (Fintype.equivFin Index).injective
        (congrArg (fun pair => (ofLex pair).2) equal)
    letI : LinearOrder Index := LinearOrder.lift' ranking ranking_injective
    refine ⟨(monoEquivOfFin Index rfl).toEquiv, ?_⟩
    intro first second comparison
    exact Prod.Lex.monotone_fst _ _ ((monoEquivOfFin Index rfl).monotone comparison)
  let trimEnumeration := fun birth => Classical.choose
    (sorted (fun occurrence : {occurrence // trimFamily.1 occurrence = birth} =>
      trimFamily.2 occurrence.val))
  obtain ⟨trimEmbedding, trim_ordered⟩ := epi_ordered_occurrence_injection
    targetFamily trimFamily target_positive trim_positive factored factor_surjective
    targetEnumeration trimEnumeration target_sorted
    (fun birth => Classical.choose_spec (sorted (fun occurrence :
      {occurrence // trimFamily.1 occurrence = birth} => trimFamily.2 occurrence.val)))
  have prefix_bound (occurrence : Source)
      (long : ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
        sourceFamily.2 occurrence) :
      ((sourceEnumeration (sourceFamily.1 occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {original // targetFamily.1 original = sourceFamily.1 occurrence ∧
          WithTop.map (fun endpoint : ℝ => endpoint - eta) (sourceFamily.2 occurrence) ≤
            targetFamily.2 original} := by
    let birth := sourceFamily.1 occurrence
    let ordinal := (sourceEnumeration birth).symm ⟨occurrence, rfl⟩
    let initialOccurrence : Fin (ordinal.val + 1) → Source := fun index =>
      (sourceEnumeration birth ⟨index.val, by omega⟩).val
    have initial_death : ∀ index, sourceFamily.2 occurrence ≤
        sourceFamily.2 (initialOccurrence index) := by
      intro index
      have comparison : (⟨index.val, by omega⟩ : Fin (Fintype.card
          {other // sourceFamily.1 other = birth})) ≤ ordinal := by
        exact Nat.le_of_lt_succ index.isLt
      simpa [initialOccurrence, ordinal] using source_sorted birth comparison
    have initial_birth : ∀ index, sourceFamily.1 (initialOccurrence index) = birth :=
      fun index => (sourceEnumeration birth _).property
    let initialTrim : Fin (ordinal.val + 1) → Trim := fun index =>
      ⟨initialOccurrence index, by rw [initial_birth]; exact long.trans_le (initial_death index)⟩
    let initial : Fin (ordinal.val + 1) → {original // targetFamily.1 original = birth ∧
        WithTop.map (fun endpoint : ℝ => endpoint - eta) (sourceFamily.2 occurrence) ≤
          targetFamily.2 original} := fun index =>
      ⟨trimEmbedding (initialTrim index),
        (trim_ordered (initialTrim index)).2.choose.trans (initial_birth index),
        (shift_monotone (initial_death index)).trans (trim_ordered (initialTrim index)).1⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have sameTrim := trimEmbedding.injective (congrArg Subtype.val equal)
      have sameOccurrence := congrArg (fun other : Trim => other.val) sameTrim
      have sameOrdinal := (sourceEnumeration birth).injective (Subtype.ext sameOccurrence)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // sourceFamily.1 other = birth}) => index.val) sameOrdinal)
    have count := Fintype.card_le_of_injective initial initial_injective
    simp only [Fintype.card_fin] at count
    exact Nat.lt_of_succ_le count
  have ordered_fiber (birth : ℝ)
      (occurrence : {other // targetFamily.1 other = birth}) :
      ∃ sameBirth : sourceFamily.1 (embedding occurrence.val) = birth,
        ((sourceEnumeration birth).symm ⟨embedding occurrence.val, sameBirth⟩).val =
          ((targetEnumeration birth).symm occurrence).val := by
    rcases occurrence with ⟨occurrence, rfl⟩
    exact (ordered occurrence).2
  have prefix_bound_fiber (birth : ℝ)
      (occurrence : {other // sourceFamily.1 other = birth})
      (long : ((birth + eta : ℝ) : WithTop ℝ) < sourceFamily.2 occurrence.val) :
      ((sourceEnumeration birth).symm occurrence).val <
        Fintype.card {original // targetFamily.1 original = birth ∧
          WithTop.map (fun endpoint : ℝ => endpoint - eta) (sourceFamily.2 occurrence.val) ≤
            targetFamily.2 original} := by
    rcases occurrence with ⟨occurrence, rfl⟩
    exact prefix_bound occurrence long
  have coverage : ∀ occurrence, ((sourceFamily.1 occurrence + eta : ℝ) : WithTop ℝ) <
      sourceFamily.2 occurrence → ∃ original, embedding original = occurrence := by
    intro occurrence long
    let birth := sourceFamily.1 occurrence
    let ordinal := (sourceEnumeration birth).symm ⟨occurrence, rfl⟩
    have total := Fintype.card_le_of_injective
      (fun other : {original // targetFamily.1 original = birth ∧
          WithTop.map (fun endpoint : ℝ => endpoint - eta) (sourceFamily.2 occurrence) ≤
            targetFamily.2 original} =>
        (⟨other.val, other.property.1⟩ : {original // targetFamily.1 original = birth}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {original // targetFamily.1 original = birth} => other.val) equal))
    have within : ordinal.val < Fintype.card {original // targetFamily.1 original = birth} :=
      (prefix_bound occurrence long).trans_le total
    let original := targetEnumeration birth ⟨ordinal.val, within⟩
    refine ⟨original.val, ?_⟩
    obtain ⟨sameBirth, sameOrdinal⟩ := ordered_fiber birth original
    have equality : ((sourceEnumeration birth).symm
        ⟨embedding original.val, sameBirth⟩).val = ordinal.val := by
      simpa only [original, Equiv.symm_apply_apply] using sameOrdinal
    have equalIndex : (sourceEnumeration birth).symm
        ⟨embedding original.val, sameBirth⟩ = ordinal := Fin.ext equality
    have equalOccurrence := (sourceEnumeration birth).symm.injective equalIndex
    exact congrArg (fun other : {original // sourceFamily.1 original = birth} =>
      other.val) equalOccurrence
  have bounds : ∀ occurrence, WithTop.map (fun endpoint : ℝ => endpoint - eta)
      (sourceFamily.2 (embedding occurrence)) ≤ targetFamily.2 occurrence := by
    intro occurrence
    obtain ⟨sameBirth, sameOrdinal⟩ := (ordered occurrence).2
    by_cases long : ((sourceFamily.1 (embedding occurrence) + eta : ℝ) : WithTop ℝ) <
        sourceFamily.2 (embedding occurrence)
    · by_contra not_after
      let birth := targetFamily.1 occurrence
      let ordinal := (targetEnumeration birth).symm ⟨occurrence, rfl⟩
      let below : {original // targetFamily.1 original = birth ∧
          WithTop.map (fun endpoint : ℝ => endpoint - eta)
            (sourceFamily.2 (embedding occurrence)) ≤ targetFamily.2 original} →
          Fin ordinal.val := fun original =>
        ⟨((targetEnumeration birth).symm ⟨original.val, original.property.1⟩).val, by
          by_contra not_less
          have comparison : ordinal ≤ (targetEnumeration birth).symm
              ⟨original.val, original.property.1⟩ := Nat.le_of_not_gt not_less
          have deaths := target_sorted birth comparison
          have survives : targetFamily.2 original.val ≤ targetFamily.2 occurrence := by
            simpa [ordinal] using deaths
          exact not_after (original.property.2.trans survives)⟩
      have below_injective : Function.Injective below := by
        intro first second equal
        have equalIndex : (targetEnumeration birth).symm ⟨first.val, first.property.1⟩ =
            (targetEnumeration birth).symm ⟨second.val, second.property.1⟩ :=
          Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
        exact Subtype.ext (congrArg
          (fun other : {original // targetFamily.1 original = birth} => other.val)
          ((targetEnumeration birth).symm.injective equalIndex))
      have count := Fintype.card_le_of_injective below below_injective
      simp only [Fintype.card_fin] at count
      have lower := prefix_bound_fiber birth ⟨embedding occurrence, sameBirth⟩ (by
        simpa only [sameBirth] using long)
      rw [sameOrdinal] at lower
      exact (not_lt_of_ge count) lower
    · have before := (shift_below (sourceFamily.2 (embedding occurrence))
        (sourceFamily.1 (embedding occurrence))).mpr (le_of_not_gt long)
      rw [sameBirth] at before
      exact before.trans (target_positive occurrence).le
  refine ⟨bounds, ?_, coverage, ?_, ?_, ?_⟩
  · intro occurrence sourceDeath targetDeath source_finite target_finite
    have comparison := bounds occurrence
    rw [source_finite, target_finite] at comparison
    simp only [WithTop.map_coe, WithTop.coe_le_coe] at comparison
    linarith
  · intro occurrence
    constructor
    · intro essential
      have comparison := bounds occurrence
      rw [essential, WithTop.map_top] at comparison
      exact top_le_iff.mp comparison
    · intro essential
      have comparison := (ordered occurrence).1
      rw [essential] at comparison
      exact top_le_iff.mp comparison
  · intro occurrence essential
    apply coverage occurrence
    rw [essential]
    exact WithTop.coe_lt_top _
  · intro zero
    subst eta
    refine ⟨fun occurrence => coverage occurrence (by simpa using source_positive occurrence), ?_⟩
    intro occurrence
    have comparison := bounds occurrence
    have comparison' : sourceFamily.2 (embedding occurrence) ≤ targetFamily.2 occurrence := by
      simp only [sub_zero] at comparison
      change WithTop.map (id : ℝ → ℝ) (sourceFamily.2 (embedding occurrence)) ≤
        targetFamily.2 occurrence at comparison
      rw [WithTop.map_id] at comparison
      exact comparison
    exact le_antisymm comparison' (ordered occurrence).1

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
