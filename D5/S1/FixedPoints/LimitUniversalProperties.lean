/- GID: D5/S1/FixedPoints/LimitUniversalProperties
   generality: G
   mirror-B: D5/B/S1/FixedPoints/LimitUniversalProperties
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Colimit cocones are initial and limit cones are terminal. -/

import Mathlib.CategoryTheory.Limits.ConeCategory

/- Library-search audit trail (2026-08-17):
   * D5 searches for `IsColimit`, `IsLimit`, cocones, and cones found no
     equivalent repository declaration.
   * Pinned Mathlib has exact equivalences
     `Cocone.isColimitEquivIsInitial` and `Cone.isLimitEquivIsTerminal`;
     the proof below only combines their two directions.
   * Two `smart_search.sh` natural-language queries returned no declaration
     name hit (exit 1); they are not treated as negative external results. -/

namespace D5.S1.FixedPoints.LimitUniversalProperties

open CategoryTheory CategoryTheory.Limits

universe u v w x

/-- A colimit is an initial cocone, while a limit is a terminal cone. -/
theorem colimit_initial_and_limit_terminal {J : Type u} [Category.{v} J]
    {C : Type w} [Category.{x} C] (F : J ⥤ C) (c : Cocone F) (l : Cone F) :
    (Nonempty (IsColimit c) ↔ Nonempty (IsInitial c)) ∧
      (Nonempty (IsLimit l) ↔ Nonempty (IsTerminal l)) := by
  constructor
  · constructor
    · rintro ⟨h⟩
      exact ⟨Cocone.isColimitEquivIsInitial c h⟩
    · rintro ⟨h⟩
      exact ⟨(Cocone.isColimitEquivIsInitial c).symm h⟩
  · constructor
    · rintro ⟨h⟩
      exact ⟨Cone.isLimitEquivIsTerminal l h⟩
    · rintro ⟨h⟩
      exact ⟨(Cone.isLimitEquivIsTerminal l).symm h⟩

#print axioms colimit_initial_and_limit_terminal

end D5.S1.FixedPoints.LimitUniversalProperties
