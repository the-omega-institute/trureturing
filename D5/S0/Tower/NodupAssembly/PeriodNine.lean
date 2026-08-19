/- GID: D5/S0/Tower/NodupAssembly/PeriodNine
   generality: I
   mirror-B: D5/B/S0/Tower/NodupAssembly/PeriodNine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-nine representatives have pairwise distinct state codes. -/

import D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineDistinct

/- Library-search audit trail (2026-08-18):
   * This assembly was deferred three times, at periods nine, ten and eleven,
     each time on the ground that the shape after `List.nodup_append` does not
     match a flat tuple.  That was true and not an obstacle: `nodup_append`
     wants a pairwise inequality where the components give `List.Disjoint`, and
     the gap is a three-line adapter.
   * Pinned Mathlib supplies `List.nodup_append` and
     `List.disjoint_append_left`; no assembled statement exists for these lists,
     so the fold below is written here. -/

namespace D5.S0.Tower.NodupAssembly.PeriodNine

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineDistinct

local notation "orbitStates" => tribonacciOrbitStates

/-- The adapter the three deferrals were blocked on: disjointness of two lists
is exactly pairwise inequality across them. -/
theorem disjoint_to_pairwise_ne {α : Type*} {left right : List α}
    (hdisjoint : left.Disjoint right) :
    ∀ a ∈ left, ∀ b ∈ right, a ≠ b := by
  intro a ha b hb hab
  exact hdisjoint ha (hab ▸ hb)

/-- Appending two lists with no duplicates and no shared element has no
duplicates. -/
theorem nodup_append_of_disjoint {α : Type*} {left right : List α}
    (hleft : left.Nodup) (hright : right.Nodup)
    (hdisjoint : left.Disjoint right) : (left ++ right).Nodup := by
  rw [List.nodup_append]
  exact ⟨hleft, hright, disjoint_to_pairwise_ne hdisjoint⟩

/-- The six group code lists, concatenated. -/
def nineAllCodes :
    List D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciCodedState :=
  tribonacciPeriodNineOrbitsFirst.flatMap orbitStates ++
    (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates ++
      (tribonacciPeriodNineOrbitsThird.flatMap orbitStates ++
        (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates ++
          (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates ++
            tribonacciPeriodNineOrbitsSixth.flatMap orbitStates))))

/-- No state code is shared by two of the twenty-six period-nine
representatives.  This is the statement the three earlier changes left open. -/
theorem nine_all_codes_nodup : nineAllCodes.Nodup := by
  have h56 : (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates ++
      tribonacciPeriodNineOrbitsSixth.flatMap orbitStates).Nodup :=
    nodup_append_of_disjoint tribonacci_period_nine_fifth_state_codes_nodup
      tribonacci_period_nine_sixth_state_codes_nodup
      tribonacci_period_nine_fifth_sixth_state_codes_disjoint
  have h456 : (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates ++
      (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates ++
        tribonacciPeriodNineOrbitsSixth.flatMap orbitStates)).Nodup := by
    refine nodup_append_of_disjoint tribonacci_period_nine_fourth_state_codes_nodup h56 ?_
    rw [List.disjoint_append_right]
    exact ⟨tribonacci_period_nine_fourth_fifth_state_codes_disjoint,
      tribonacci_period_nine_fourth_sixth_state_codes_disjoint⟩
  have h3456 : (tribonacciPeriodNineOrbitsThird.flatMap orbitStates ++
      (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates ++
        (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates ++
          tribonacciPeriodNineOrbitsSixth.flatMap orbitStates))).Nodup := by
    refine nodup_append_of_disjoint tribonacci_period_nine_third_state_codes_nodup h456 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨tribonacci_period_nine_third_fourth_state_codes_disjoint,
      tribonacci_period_nine_third_fifth_state_codes_disjoint,
      tribonacci_period_nine_third_sixth_state_codes_disjoint⟩
  have h23456 : (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates ++
      (tribonacciPeriodNineOrbitsThird.flatMap orbitStates ++
        (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates ++
          (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates ++
            tribonacciPeriodNineOrbitsSixth.flatMap orbitStates)))).Nodup := by
    refine nodup_append_of_disjoint tribonacci_period_nine_second_state_codes_nodup h3456 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨tribonacci_period_nine_second_third_state_codes_disjoint,
      tribonacci_period_nine_second_fourth_state_codes_disjoint,
      tribonacci_period_nine_second_fifth_state_codes_disjoint,
      tribonacci_period_nine_second_sixth_state_codes_disjoint⟩
  refine nodup_append_of_disjoint tribonacci_period_nine_first_state_codes_nodup h23456 ?_
  rw [List.disjoint_append_right, List.disjoint_append_right,
    List.disjoint_append_right, List.disjoint_append_right]
  exact ⟨tribonacci_period_nine_first_second_state_codes_disjoint,
    tribonacci_period_nine_first_third_state_codes_disjoint,
    tribonacci_period_nine_first_fourth_state_codes_disjoint,
    tribonacci_period_nine_first_fifth_state_codes_disjoint,
    tribonacci_period_nine_first_sixth_state_codes_disjoint⟩

end D5.S0.Tower.NodupAssembly.PeriodNine
