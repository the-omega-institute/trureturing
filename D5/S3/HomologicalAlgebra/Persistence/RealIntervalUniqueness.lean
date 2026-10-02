/- GID: D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual morphism window counts and ordered occurrence injections. -/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Pi

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

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
