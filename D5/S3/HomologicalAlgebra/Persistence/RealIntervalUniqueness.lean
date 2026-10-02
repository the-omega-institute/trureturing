/- GID: D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual interval-sum image ranks determine arbitrary finite endpoint multiplicities. -/

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

theorem ranks_determine_multiplicities {First Second : Type v} [Fintype First] [Fintype Second]
    (first : IntervalFamily First) (second : IntervalFamily Second)
    (equal_ranks : ∀ source target (ordered : source ≤ target),
      finrank K (LinearMap.range (intervalArrow first source target ordered (K := K))) =
        finrank K (LinearMap.range (intervalArrow second source target ordered (K := K)))) :
    ∀ birth death,
      Fintype.card {occurrence // first.birth occurrence = birth ∧ first.death occurrence = death} =
        Fintype.card {occurrence //
          second.birth occurrence = birth ∧ second.death occurrence = death} := by
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
    rw [← image_rank First first source target ordered,
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
    rw [← birth_difference First first (fun occurrence =>
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
  rw [multiplicity_sum First first, multiplicity_sum Second second]
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
    rw [← essential First first first_death_member, ← essential Second second second_death_member]
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
      rw [← death_difference First first first_death_member,
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
      rw [empty First first, empty Second second]

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
