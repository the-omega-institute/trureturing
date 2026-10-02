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

end D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
