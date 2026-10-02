/- GID: D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supported real interval-sum spaces and structure maps. -/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Max

namespace D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness

open CategoryTheory Module

universe u v

structure IntervalFamily (Occurrence : Type v) where
  birth : Occurrence → ℝ
  death : Occurrence → WithTop ℝ
  positive : ∀ occurrence, (birth occurrence : WithTop ℝ) < death occurrence

variable {K : Type u} [Field K] {Occurrence : Type v}

def intervalSpace (family : IntervalFamily Occurrence) (time : ℝ) :
    Submodule K (Occurrence → K) where
  carrier := {coordinates | ∀ occurrence,
    ¬ (family.birth occurrence ≤ time ∧ (time : WithTop ℝ) < family.death occurrence) →
      coordinates occurrence = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second first_supported second_supported occurrence unsupported
    simp [first_supported occurrence unsupported, second_supported occurrence unsupported]
  smul_mem' := by
    intro scalar coordinates supported occurrence unsupported
    simp [supported occurrence unsupported]

noncomputable def intervalArrow (family : IntervalFamily Occurrence) (source target : ℝ)
    (ordered : source ≤ target) :
    intervalSpace (K := K) family source →ₗ[K] intervalSpace (K := K) family target := by
  classical
  refine {
    toFun := fun coordinates => ⟨fun occurrence =>
      if (target : WithTop ℝ) < family.death occurrence then coordinates.val occurrence else 0, ?_⟩
    map_add' := ?_
    map_smul' := ?_ }
  · intro occurrence unsupported
    by_cases survives : (target : WithTop ℝ) < family.death occurrence
    · have not_born : ¬ family.birth occurrence ≤ source := by
        intro born
        exact unsupported ⟨born.trans ordered, survives⟩
      simp [survives, coordinates.property occurrence (by tauto)]
    · simp [survives]
  · intro first second
    ext occurrence
    by_cases survives : (target : WithTop ℝ) < family.death occurrence <;> simp [survives]
  · intro scalar coordinates
    ext occurrence
    by_cases survives : (target : WithTop ℝ) < family.death occurrence <;> simp [survives]

noncomputable def intervalSum (family : IntervalFamily Occurrence) :
    ℝ ⥤ ModuleCat.{max u v} K where
  obj time := ModuleCat.of K (intervalSpace (K := K) family time)
  map {source target} arrow := ModuleCat.ofHom (intervalArrow family source target (leOfHom arrow))
  map_id time := by
    classical
    ext coordinates occurrence
    by_cases survives : (time : WithTop ℝ) < family.death occurrence
    · simp [intervalArrow, survives]
    · simp [intervalArrow, survives, coordinates.property occurrence (by tauto)]
  map_comp {source middle target} first second := by
    classical
    ext coordinates occurrence
    by_cases survives : (target : WithTop ℝ) < family.death occurrence
    · have middle_survives : (middle : WithTop ℝ) < family.death occurrence :=
        lt_of_le_of_lt (WithTop.coe_le_coe.mpr (leOfHom second)) survives
      simp [intervalArrow, survives, middle_survives]
    · simp [intervalArrow, survives]

set_option backward.isDefEq.respectTransparency false in
theorem mono_death_window_count {Source Target : Type v} [Fintype Source] [Fintype Target]
    (sourceFamily : IntervalFamily Source) (targetFamily : IntervalFamily Target)
    (morphism : intervalSum (K := K) sourceFamily ⟶ intervalSum (K := K) targetFamily)
    (injective : ∀ time, Function.Injective (morphism.app time).hom)
    (birthCut sample : ℝ) (deathCut : WithTop ℝ) (birth_before : birthCut ≤ sample)
    (sample_before : (sample : WithTop ℝ) ≤ deathCut) :
    Fintype.card {occurrence // sourceFamily.birth occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
      sourceFamily.death occurrence ≤ deathCut} ≤
    Fintype.card {occurrence // targetFamily.birth occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < targetFamily.death occurrence ∧
      targetFamily.death occurrence ≤ deathCut} := by
  classical
  let SourceWindow := {occurrence // sourceFamily.birth occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
    sourceFamily.death occurrence ≤ deathCut}
  let TargetWindow := {occurrence // targetFamily.birth occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < targetFamily.death occurrence ∧
    targetFamily.death occurrence ≤ deathCut}
  let extend : ∀ time, birthCut ≤ time → time ≤ sample →
      (SourceWindow → K) →ₗ[K] intervalSpace (K := K) sourceFamily time :=
    fun time after_birth before_sample => {
      toFun := fun coordinates => ⟨fun occurrence =>
        if supported : sourceFamily.birth occurrence ≤ birthCut ∧
            (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
            sourceFamily.death occurrence ≤ deathCut
        then coordinates ⟨occurrence, supported⟩ else 0, by
          intro occurrence unsupported
          have absent : ¬ (sourceFamily.birth occurrence ≤ birthCut ∧
              (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
              sourceFamily.death occurrence ≤ deathCut) := by
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
    by_cases supported : sourceFamily.birth occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
        sourceFamily.death occurrence ≤ deathCut
    · simp [intervalArrow, extend, supported]
    · simp [intervalArrow, extend, supported]
  have death_kernel : ∀ (cut : ℝ) (after_sample : sample ≤ cut),
      deathCut ≤ (cut : WithTop ℝ) → ∀ coordinates,
      intervalArrow sourceFamily sample cut after_sample
        (extend sample birth_before le_rfl coordinates) = 0 := by
    intro cut after_sample above coordinates
    ext occurrence
    by_cases supported : sourceFamily.birth occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
        sourceFamily.death occurrence ≤ deathCut
    · simp [intervalArrow, extend, not_lt_of_ge (supported.2.2.trans above)]
    · simp [intervalArrow, extend, supported]
  have target_supported : ∀ coordinates occurrence,
      ¬ (targetFamily.birth occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < targetFamily.death occurrence ∧
        targetFamily.death occurrence ≤ deathCut) →
      ((morphism.app sample).hom (extend sample birth_before le_rfl coordinates)).val
        occurrence = 0 := by
    intro coordinates occurrence unsupported
    by_cases born : targetFamily.birth occurrence ≤ birthCut
    · by_cases survives : (sample : WithTop ℝ) < targetFamily.death occurrence
      · cases deathCut with
        | top => exact False.elim (unsupported ⟨born, survives, le_top⟩)
        | coe finiteCut =>
          have after_sample : sample ≤ finiteCut := WithTop.coe_le_coe.mp sample_before
          have survives_cut : (finiteCut : WithTop ℝ) < targetFamily.death occurrence := by
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
            (fun vector : intervalSpace (K := K) targetFamily finiteCut => vector.val occurrence)
            square
          simpa [intervalArrow, survives_cut] using coordinate.symm
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
        (fun vector : intervalSpace (K := K) targetFamily sample => vector.val occurrence) square
      have absent := ((morphism.app birthCut).hom
        (extend birthCut le_rfl birth_before coordinates)).property occurrence (by tauto)
      simpa [intervalArrow, absent] using coordinate
  let restricted : (SourceWindow → K) →ₗ[K] (TargetWindow → K) :=
    LinearMap.pi fun occurrence => (LinearMap.proj occurrence.val).comp
      ((intervalSpace (K := K) targetFamily sample).subtype.comp
        ((morphism.app sample).hom.comp (extend sample birth_before le_rfl)))
  have restricted_injective : Function.Injective restricted := by
    intro first second equal
    have equal_images : (morphism.app sample).hom (extend sample birth_before le_rfl first) =
        (morphism.app sample).hom (extend sample birth_before le_rfl second) := by
      apply Subtype.ext
      funext occurrence
      by_cases supported : targetFamily.birth occurrence ≤ birthCut ∧
          (sample : WithTop ℝ) < targetFamily.death occurrence ∧
          targetFamily.death occurrence ≤ deathCut
      · exact congrFun equal ⟨occurrence, supported⟩
      · rw [target_supported first occurrence supported,
          target_supported second occurrence supported]
    have equal_sources := injective sample equal_images
    funext occurrence
    have coordinate := congrArg
      (fun vector : intervalSpace (K := K) sourceFamily sample => vector.val occurrence.val)
      equal_sources
    simpa [extend, occurrence.property] using coordinate
  have dimensions := LinearMap.finrank_le_finrank_of_injective
    (f := restricted) restricted_injective
  simpa [SourceWindow, TargetWindow, Module.finrank_fintype_fun_eq_card] using dimensions

set_option backward.isDefEq.respectTransparency false in
theorem epi_birth_window_count {Source Target : Type v} [Fintype Source] [Fintype Target]
    (sourceFamily : IntervalFamily Source) (targetFamily : IntervalFamily Target)
    (morphism : intervalSum (K := K) sourceFamily ⟶ intervalSum (K := K) targetFamily)
    (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
    (earlier birthCut sample : ℝ) (earlier_before : earlier ≤ birthCut)
    (birth_before : birthCut ≤ sample) :
    Fintype.card {occurrence // earlier < targetFamily.birth occurrence ∧
      targetFamily.birth occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < targetFamily.death occurrence} ≤
    Fintype.card {occurrence // earlier < sourceFamily.birth occurrence ∧
      sourceFamily.birth occurrence ≤ birthCut ∧
      (sample : WithTop ℝ) < sourceFamily.death occurrence} := by
  classical
  let SourceWindow := {occurrence // earlier < sourceFamily.birth occurrence ∧
    sourceFamily.birth occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < sourceFamily.death occurrence}
  let TargetWindow := {occurrence // earlier < targetFamily.birth occurrence ∧
    targetFamily.birth occurrence ≤ birthCut ∧
    (sample : WithTop ℝ) < targetFamily.death occurrence}
  let extend : ∀ {Index : Type v} (family : IntervalFamily Index),
      ({occurrence // earlier < family.birth occurrence ∧
        family.birth occurrence ≤ birthCut ∧
        (sample : WithTop ℝ) < family.death occurrence} → K) →ₗ[K]
      intervalSpace (K := K) family birthCut := fun family => {
    toFun := fun coordinates => ⟨fun occurrence =>
      if supported : earlier < family.birth occurrence ∧
          family.birth occurrence ≤ birthCut ∧
          (sample : WithTop ℝ) < family.death occurrence
      then coordinates ⟨occurrence, supported⟩ else 0, by
        intro occurrence unsupported
        have absent : ¬ (earlier < family.birth occurrence ∧
            family.birth occurrence ≤ birthCut ∧
            (sample : WithTop ℝ) < family.death occurrence) := by
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
      ((intervalSpace (K := K) targetFamily sample).subtype.comp
        ((morphism.app sample).hom.comp
          ((intervalArrow sourceFamily birthCut sample birth_before).comp
            (extend sourceFamily))))
  have restricted_surjective : Function.Surjective restricted := by
    intro coordinates
    obtain ⟨preimage, image_eq⟩ := surjective birthCut (extend targetFamily coordinates)
    let source_coordinates : SourceWindow → K := fun occurrence => preimage.val occurrence.val
    let early : intervalSpace (K := K) sourceFamily earlier := ⟨fun occurrence =>
      if sourceFamily.birth occurrence ≤ earlier ∧
          (sample : WithTop ℝ) < sourceFamily.death occurrence
      then preimage.val occurrence else 0, by
        intro occurrence unsupported
        have absent : ¬ (sourceFamily.birth occurrence ≤ earlier ∧
            (sample : WithTop ℝ) < sourceFamily.death occurrence) := by
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
      by_cases survives : (sample : WithTop ℝ) < sourceFamily.death occurrence
      · by_cases old : sourceFamily.birth occurrence ≤ earlier
        · simp [intervalArrow, extend, early, survives, old, not_lt_of_ge old]
        · have recent : earlier < sourceFamily.birth occurrence := lt_of_not_ge old
          by_cases born : sourceFamily.birth occurrence ≤ birthCut
          · simp [intervalArrow, extend, early, source_coordinates, survives, old, recent, born]
          · have absent := preimage.property occurrence (by tauto)
            simp [intervalArrow, extend, early, survives, old, born, absent]
      · simp [intervalArrow, survives]
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
        (fun vector : intervalSpace (K := K) targetFamily sample => vector.val occurrence.val)
        square
      have absent := ((morphism.app earlier).hom early).property occurrence.val
        (by exact fun supported => (not_le_of_gt occurrence.property.1) supported.1)
      simpa [intervalArrow, absent] using coordinate
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
      (fun vector : intervalSpace (K := K) targetFamily sample => vector.val occurrence.val) square
    have transported := congrArg
      (fun vector : intervalSpace (K := K) sourceFamily sample =>
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
      simpa [intervalArrow, extend, occurrence.property.1, occurrence.property.2.1,
        occurrence.property.2.2] using coordinate
    exact transported.symm.trans reconstruction
  have dimensions := LinearMap.finrank_le_finrank_of_surjective
    (f := restricted) restricted_surjective
  simpa [SourceWindow, TargetWindow, Module.finrank_fintype_fun_eq_card] using dimensions

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
