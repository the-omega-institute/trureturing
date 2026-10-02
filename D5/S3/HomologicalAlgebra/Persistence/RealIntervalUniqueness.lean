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

theorem image_range_mono {Source Target : Type v}
    (sourceFamily : IntervalFamily Source) (targetFamily : IntervalFamily Target)
    (morphism : intervalSum (K := K) sourceFamily ⟶ intervalSum (K := K) targetFamily)
    {source target : ℝ} (ordered : source ≤ target) :
    Submodule.map (intervalArrow targetFamily source target ordered)
        (LinearMap.range (morphism.app source).hom) ≤
      LinearMap.range (morphism.app target).hom := by
  rintro vector ⟨preimage, ⟨original, rfl⟩, rfl⟩
  have square := congrArg (fun arrow => arrow.hom original)
    (morphism.naturality (homOfLE ordered))
  change (morphism.app target).hom
      (intervalArrow sourceFamily source target ordered original) =
    intervalArrow targetFamily source target ordered
      ((morphism.app source).hom original) at square
  have in_range : (morphism.app target).hom
      (intervalArrow sourceFamily source target ordered original) ∈
    LinearMap.range (morphism.app target).hom :=
      ⟨intervalArrow sourceFamily source target ordered original, rfl⟩
  rw [square] at in_range
  exact in_range

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

set_option backward.isDefEq.respectTransparency false in
theorem mono_ordered_occurrence_injection {Source Target : Type v}
    [Fintype Source] [Fintype Target]
    (sourceFamily : IntervalFamily Source) (targetFamily : IntervalFamily Target)
    (morphism : intervalSum (K := K) sourceFamily ⟶ intervalSum (K := K) targetFamily)
    (injective : ∀ time, Function.Injective (morphism.app time).hom)
    (sourceEnumeration : ∀ death, Fin (Fintype.card
      {occurrence // sourceFamily.death occurrence = death}) ≃
        {occurrence // sourceFamily.death occurrence = death})
    (targetEnumeration : ∀ death, Fin (Fintype.card
      {occurrence // targetFamily.death occurrence = death}) ≃
        {occurrence // targetFamily.death occurrence = death})
    (source_sorted : ∀ death, Monotone fun ordinal =>
      sourceFamily.birth (sourceEnumeration death ordinal).val)
    (target_sorted : ∀ death, Monotone fun ordinal =>
      targetFamily.birth (targetEnumeration death ordinal).val) :
    ∃ embedding : Source ↪ Target, ∀ occurrence,
      targetFamily.birth (embedding occurrence) ≤ sourceFamily.birth occurrence ∧
      ∃ sameDeath : targetFamily.death (embedding occurrence) = sourceFamily.death occurrence,
        ((targetEnumeration (sourceFamily.death occurrence)).symm
          ⟨embedding occurrence, sameDeath⟩).val =
        ((sourceEnumeration (sourceFamily.death occurrence)).symm ⟨occurrence, rfl⟩).val := by
  classical
  have counts (birth : ℝ) (death : WithTop ℝ) (positive : (birth : WithTop ℝ) < death) :
      Fintype.card {occurrence // sourceFamily.birth occurrence ≤ birth ∧
        sourceFamily.death occurrence = death} ≤
      Fintype.card {occurrence // targetFamily.birth occurrence ≤ birth ∧
        targetFamily.death occurrence = death} := by
    let endpoints := (insert (birth : WithTop ℝ)
      (Finset.univ.image sourceFamily.death ∪ Finset.univ.image targetFamily.death)).filter
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
    have source_lower : ∀ occurrence, sourceFamily.death occurrence < death →
        sourceFamily.death occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [endpoints, less]
    have target_lower : ∀ occurrence, targetFamily.death occurrence < death →
        targetFamily.death occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [endpoints, less]
    have window := mono_death_window_count sourceFamily targetFamily morphism injective
      birth sample death birth_before before.le
    have source_predicate : (fun occurrence => sourceFamily.birth occurrence ≤ birth ∧
        (sample : WithTop ℝ) < sourceFamily.death occurrence ∧
        sourceFamily.death occurrence ≤ death) =
        (fun occurrence => sourceFamily.birth occurrence ≤ birth ∧
          sourceFamily.death occurrence = death) := by
      funext occurrence
      apply propext
      constructor
      · intro supported
        exact ⟨supported.1, le_antisymm supported.2.2 (le_of_not_gt fun less =>
          (not_lt_of_ge (source_lower occurrence less)) supported.2.1)⟩
      · rintro ⟨born, rfl⟩
        exact ⟨born, before, le_rfl⟩
    have target_predicate : (fun occurrence => targetFamily.birth occurrence ≤ birth ∧
        (sample : WithTop ℝ) < targetFamily.death occurrence ∧
        targetFamily.death occurrence ≤ death) =
        (fun occurrence => targetFamily.birth occurrence ≤ birth ∧
          targetFamily.death occurrence = death) := by
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
      let ordinal := (sourceEnumeration (sourceFamily.death occurrence)).symm ⟨occurrence, rfl⟩
      ordinal.val < Fintype.card {other // targetFamily.birth other ≤
        sourceFamily.birth occurrence ∧ targetFamily.death other = sourceFamily.death occurrence} := by
    let death := sourceFamily.death occurrence
    let ordinal := (sourceEnumeration death).symm ⟨occurrence, rfl⟩
    let initial : Fin (ordinal.val + 1) → {other // sourceFamily.birth other ≤
        sourceFamily.birth occurrence ∧ sourceFamily.death other = death} := fun index =>
      ⟨(sourceEnumeration death ⟨index.val, by omega⟩).val,
        by
          constructor
          · have ordered : (⟨index.val, by omega⟩ : Fin (Fintype.card
                {other // sourceFamily.death other = death})) ≤ ordinal := by
              exact Nat.le_of_lt_succ index.isLt
            simpa [ordinal] using source_sorted death ordered
          · exact (sourceEnumeration death _).property⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have equal_values := congrArg Subtype.val equal
      have equal_indices := (sourceEnumeration death).injective (Subtype.ext equal_values)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // sourceFamily.death other = death}) => index.val) equal_indices)
    have initial_count := Fintype.card_le_of_injective initial initial_injective
    have comparison := counts (sourceFamily.birth occurrence) death (sourceFamily.positive occurrence)
    simp only [Fintype.card_fin] at initial_count
    exact lt_of_lt_of_le (Nat.lt_of_succ_le initial_count) comparison
  have class_bound (occurrence : Source) :
      ((sourceEnumeration (sourceFamily.death occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {other // targetFamily.death other = sourceFamily.death occurrence} := by
    have eligible := ordinal_bound occurrence
    have total := Fintype.card_le_of_injective
      (fun other : {other // targetFamily.birth other ≤ sourceFamily.birth occurrence ∧
          targetFamily.death other = sourceFamily.death occurrence} =>
        (⟨other.val, other.property.2⟩ : {other //
          targetFamily.death other = sourceFamily.death occurrence}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {other // targetFamily.death other = sourceFamily.death occurrence} =>
          other.val) equal))
    exact eligible.trans_le total
  have class_bound' : ∀ death (occurrence : {other // sourceFamily.death other = death}),
      ((sourceEnumeration death).symm occurrence).val <
        Fintype.card {other // targetFamily.death other = death} := by
    intro death ⟨occurrence, sameDeath⟩
    subst death
    exact class_bound occurrence
  let classMap : ∀ death, {other // sourceFamily.death other = death} ↪
      {other // targetFamily.death other = death} := fun death => {
    toFun := fun occurrence => targetEnumeration death
      ⟨((sourceEnumeration death).symm occurrence).val, class_bound' death occurrence⟩
    inj' := by
      intro first second equal
      have sameOrdinal := (targetEnumeration death).injective equal
      apply (sourceEnumeration death).symm.injective
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // targetFamily.death other = death}) => index.val) sameOrdinal) }
  let embedding := (Equiv.sigmaFiberEquiv sourceFamily.death).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _) classMap).trans
      (Equiv.sigmaFiberEquiv targetFamily.death).toEmbedding)
  let selected := fun occurrence => classMap (sourceFamily.death occurrence) ⟨occurrence, rfl⟩
  have birth_bound (occurrence : Source) :
      targetFamily.birth (selected occurrence).val ≤ sourceFamily.birth occurrence := by
    by_contra not_before
    let ordinal := (sourceEnumeration (sourceFamily.death occurrence)).symm ⟨occurrence, rfl⟩
    let below : {other // targetFamily.birth other ≤ sourceFamily.birth occurrence ∧
        targetFamily.death other = sourceFamily.death occurrence} → Fin ordinal.val := fun other =>
      ⟨((targetEnumeration (sourceFamily.death occurrence)).symm
          ⟨other.val, other.property.2⟩).val, by
        by_contra not_less
        have ordered : (⟨ordinal.val, class_bound occurrence⟩ : Fin (Fintype.card
            {other // targetFamily.death other = sourceFamily.death occurrence})) ≤
          (targetEnumeration (sourceFamily.death occurrence)).symm
            ⟨other.val, other.property.2⟩ := Nat.le_of_not_gt not_less
        have comparison := target_sorted (sourceFamily.death occurrence) ordered
        have comparison' : targetFamily.birth (selected occurrence).val ≤
            targetFamily.birth other.val := by simpa [selected, classMap] using comparison
        exact not_before (comparison'.trans other.property.1)⟩
    have below_injective : Function.Injective below := by
      intro first second equal
      have equal_indices : (targetEnumeration (sourceFamily.death occurrence)).symm
          ⟨first.val, first.property.2⟩ =
        (targetEnumeration (sourceFamily.death occurrence)).symm
          ⟨second.val, second.property.2⟩ :=
        Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
      have equal_values := (targetEnumeration (sourceFamily.death occurrence)).symm.injective
        equal_indices
      exact Subtype.ext (congrArg (fun other : {other //
        targetFamily.death other = sourceFamily.death occurrence} => other.val) equal_values)
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
    (sourceFamily : IntervalFamily Source) (targetFamily : IntervalFamily Target)
    (morphism : intervalSum (K := K) sourceFamily ⟶ intervalSum (K := K) targetFamily)
    (surjective : ∀ time, Function.Surjective (morphism.app time).hom)
    (sourceEnumeration : ∀ birth, Fin (Fintype.card
      {occurrence // sourceFamily.birth occurrence = birth}) ≃
        {occurrence // sourceFamily.birth occurrence = birth})
    (targetEnumeration : ∀ birth, Fin (Fintype.card
      {occurrence // targetFamily.birth occurrence = birth}) ≃
        {occurrence // targetFamily.birth occurrence = birth})
    (source_sorted : ∀ birth, Antitone fun ordinal =>
      sourceFamily.death (sourceEnumeration birth ordinal).val)
    (target_sorted : ∀ birth, Antitone fun ordinal =>
      targetFamily.death (targetEnumeration birth ordinal).val) :
    ∃ embedding : Target ↪ Source, ∀ occurrence,
      targetFamily.death occurrence ≤ sourceFamily.death (embedding occurrence) ∧
      ∃ sameBirth : sourceFamily.birth (embedding occurrence) = targetFamily.birth occurrence,
        ((sourceEnumeration (targetFamily.birth occurrence)).symm
          ⟨embedding occurrence, sameBirth⟩).val =
        ((targetEnumeration (targetFamily.birth occurrence)).symm ⟨occurrence, rfl⟩).val := by
  classical
  have counts (birth : ℝ) (death : WithTop ℝ) (positive : (birth : WithTop ℝ) < death) :
      Fintype.card {occurrence // targetFamily.birth occurrence = birth ∧
        death ≤ targetFamily.death occurrence} ≤
      Fintype.card {occurrence // sourceFamily.birth occurrence = birth ∧
        death ≤ sourceFamily.death occurrence} := by
    let births := (insert (birth - 1)
      (Finset.univ.image sourceFamily.birth ∪ Finset.univ.image targetFamily.birth)).filter
        (fun endpoint => endpoint < birth)
    have earlier_mem : birth - 1 ∈ births := by simp [births]
    let earlier := births.sup' ⟨_, earlier_mem⟩ id
    have earlier_before : earlier < birth := by
      apply (Finset.sup'_lt_iff _).mpr
      intro endpoint member
      exact (Finset.mem_filter.mp member).2
    have source_birth_lower : ∀ occurrence, sourceFamily.birth occurrence < birth →
        sourceFamily.birth occurrence ≤ earlier := by
      intro occurrence less
      apply Finset.le_sup' id
      simp [births, less]
    have target_birth_lower : ∀ occurrence, targetFamily.birth occurrence < birth →
        targetFamily.birth occurrence ≤ earlier := by
      intro occurrence less
      apply Finset.le_sup' id
      simp [births, less]
    let deaths := (insert (birth : WithTop ℝ)
      (Finset.univ.image sourceFamily.death ∪ Finset.univ.image targetFamily.death)).filter
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
    have source_death_lower : ∀ occurrence, sourceFamily.death occurrence < death →
        sourceFamily.death occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [deaths, less]
    have target_death_lower : ∀ occurrence, targetFamily.death occurrence < death →
        targetFamily.death occurrence ≤ (sample : WithTop ℝ) := by
      intro occurrence less
      rw [sample_eq]
      apply Finset.le_sup' id
      simp [deaths, less]
    have predicate {Index : Type v} (family : IntervalFamily Index)
        (birth_lower : ∀ occurrence, family.birth occurrence < birth →
          family.birth occurrence ≤ earlier)
        (death_lower : ∀ occurrence, family.death occurrence < death →
          family.death occurrence ≤ (sample : WithTop ℝ)) :
        ∀ occurrence, (earlier < family.birth occurrence ∧ family.birth occurrence ≤ birth ∧
          (sample : WithTop ℝ) < family.death occurrence) ↔
          (family.birth occurrence = birth ∧ death ≤ family.death occurrence) := by
      intro occurrence
      constructor
      · intro supported
        exact ⟨le_antisymm supported.2.1 (le_of_not_gt fun less =>
          (not_lt_of_ge (birth_lower occurrence less)) supported.1),
          le_of_not_gt fun less => (not_lt_of_ge (death_lower occurrence less)) supported.2.2⟩
      · rintro ⟨sameBirth, survives⟩
        exact ⟨by simpa [sameBirth] using earlier_before, sameBirth.le, before.trans_le survives⟩
    have window := epi_birth_window_count sourceFamily targetFamily morphism surjective
      earlier birth sample earlier_before.le birth_before
    have source_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (predicate sourceFamily source_birth_lower source_death_lower))
    have target_card := Fintype.card_congr (Equiv.subtypeEquivRight
      (predicate targetFamily target_birth_lower target_death_lower))
    exact source_card ▸ target_card ▸ window
  have ordinal_bound (occurrence : Target) :
      let ordinal := (targetEnumeration (targetFamily.birth occurrence)).symm ⟨occurrence, rfl⟩
      ordinal.val < Fintype.card {other // sourceFamily.birth other =
        targetFamily.birth occurrence ∧ targetFamily.death occurrence ≤ sourceFamily.death other} := by
    let birth := targetFamily.birth occurrence
    let ordinal := (targetEnumeration birth).symm ⟨occurrence, rfl⟩
    let initial : Fin (ordinal.val + 1) → {other // targetFamily.birth other = birth ∧
        targetFamily.death occurrence ≤ targetFamily.death other} := fun index =>
      ⟨(targetEnumeration birth ⟨index.val, by omega⟩).val,
        by
          constructor
          · exact (targetEnumeration birth _).property
          · have ordered : (⟨index.val, by omega⟩ : Fin (Fintype.card
                {other // targetFamily.birth other = birth})) ≤ ordinal := by
              exact Nat.le_of_lt_succ index.isLt
            simpa [ordinal] using target_sorted birth ordered⟩
    have initial_injective : Function.Injective initial := by
      intro first second equal
      have equal_values := congrArg Subtype.val equal
      have equal_indices := (targetEnumeration birth).injective (Subtype.ext equal_values)
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // targetFamily.birth other = birth}) => index.val) equal_indices)
    have initial_count := Fintype.card_le_of_injective initial initial_injective
    have comparison := counts birth (targetFamily.death occurrence) (targetFamily.positive occurrence)
    simp only [Fintype.card_fin] at initial_count
    exact lt_of_lt_of_le (Nat.lt_of_succ_le initial_count) comparison
  have class_bound (occurrence : Target) :
      ((targetEnumeration (targetFamily.birth occurrence)).symm ⟨occurrence, rfl⟩).val <
        Fintype.card {other // sourceFamily.birth other = targetFamily.birth occurrence} := by
    have eligible := ordinal_bound occurrence
    have total := Fintype.card_le_of_injective
      (fun other : {other // sourceFamily.birth other = targetFamily.birth occurrence ∧
          targetFamily.death occurrence ≤ sourceFamily.death other} =>
        (⟨other.val, other.property.1⟩ : {other //
          sourceFamily.birth other = targetFamily.birth occurrence}))
      (by intro first second equal; exact Subtype.ext (congrArg
        (fun other : {other // sourceFamily.birth other = targetFamily.birth occurrence} =>
          other.val) equal))
    exact eligible.trans_le total
  have class_bound' : ∀ birth (occurrence : {other // targetFamily.birth other = birth}),
      ((targetEnumeration birth).symm occurrence).val <
        Fintype.card {other // sourceFamily.birth other = birth} := by
    intro birth ⟨occurrence, sameBirth⟩
    subst birth
    exact class_bound occurrence
  let classMap : ∀ birth, {other // targetFamily.birth other = birth} ↪
      {other // sourceFamily.birth other = birth} := fun birth => {
    toFun := fun occurrence => sourceEnumeration birth
      ⟨((targetEnumeration birth).symm occurrence).val, class_bound' birth occurrence⟩
    inj' := by
      intro first second equal
      have sameOrdinal := (sourceEnumeration birth).injective equal
      apply (targetEnumeration birth).symm.injective
      exact Fin.ext (congrArg (fun index : Fin (Fintype.card
        {other // sourceFamily.birth other = birth}) => index.val) sameOrdinal) }
  let embedding := (Equiv.sigmaFiberEquiv targetFamily.birth).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _) classMap).trans
      (Equiv.sigmaFiberEquiv sourceFamily.birth).toEmbedding)
  let selected := fun occurrence => classMap (targetFamily.birth occurrence) ⟨occurrence, rfl⟩
  have death_bound (occurrence : Target) :
      targetFamily.death occurrence ≤ sourceFamily.death (selected occurrence).val := by
    by_contra not_after
    let ordinal := (targetEnumeration (targetFamily.birth occurrence)).symm ⟨occurrence, rfl⟩
    let below : {other // sourceFamily.birth other = targetFamily.birth occurrence ∧
        targetFamily.death occurrence ≤ sourceFamily.death other} → Fin ordinal.val := fun other =>
      ⟨((sourceEnumeration (targetFamily.birth occurrence)).symm
          ⟨other.val, other.property.1⟩).val, by
        by_contra not_less
        have ordered : (⟨ordinal.val, class_bound occurrence⟩ : Fin (Fintype.card
            {other // sourceFamily.birth other = targetFamily.birth occurrence})) ≤
          (sourceEnumeration (targetFamily.birth occurrence)).symm
            ⟨other.val, other.property.1⟩ := Nat.le_of_not_gt not_less
        have comparison := source_sorted (targetFamily.birth occurrence) ordered
        have comparison' : sourceFamily.death other.val ≤
            sourceFamily.death (selected occurrence).val := by
          simpa [selected, classMap] using comparison
        exact not_after (other.property.2.trans comparison')⟩
    have below_injective : Function.Injective below := by
      intro first second equal
      have equal_indices : (sourceEnumeration (targetFamily.birth occurrence)).symm
          ⟨first.val, first.property.1⟩ =
        (sourceEnumeration (targetFamily.birth occurrence)).symm
          ⟨second.val, second.property.1⟩ :=
        Fin.ext (congrArg (fun index : Fin ordinal.val => index.val) equal)
      have equal_values := (sourceEnumeration (targetFamily.birth occurrence)).symm.injective
        equal_indices
      exact Subtype.ext (congrArg (fun other : {other //
        sourceFamily.birth other = targetFamily.birth occurrence} => other.val) equal_values)
    have bound := Fintype.card_le_of_injective below below_injective
    simp only [Fintype.card_fin] at bound
    exact (not_lt_of_ge bound) (ordinal_bound occurrence)
  refine ⟨embedding, ?_⟩
  intro occurrence
  rw [show embedding occurrence = (selected occurrence).val from rfl]
  exact ⟨death_bound occurrence, (selected occurrence).property, by simp [selected, classMap]⟩

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
