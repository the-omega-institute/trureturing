/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixed
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-eight equations equal eleven inherited and one hundred twenty new phase states. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedB

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixed

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedB

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_new_orbit_states_subset_fixed_points_eight :
    (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
      orbitStates).toFinset ⊆ (fixedPointCodes 8).toFinset := by
  change
    ((tribonacciPeriodEightOrbitsFirst.flatMap orbitStates) ++
      (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates) ++
      tribonacciPeriodEightOrbitsLast.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 8).toFinset
  rw [List.toFinset_append, List.toFinset_append,
    Finset.union_subset_iff, Finset.union_subset_iff]
  exact
    ⟨⟨tribonacci_first_new_orbit_states_subset_fixed_points_eight,
      tribonacci_middle_new_orbit_states_subset_fixed_points_eight⟩,
      tribonacci_last_new_orbit_states_subset_fixed_points_eight⟩

theorem tribonacci_expected_point_codes_subset_fixed_points_eight :
    tribonacciExpectedPointCodesEight ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacciExpectedPointCodesEight,
    tribonacciPeriodicOrbitRepresentativesAtEight, List.flatMap_append,
    List.toFinset_append, Finset.union_subset_iff]
  exact ⟨tribonacci_inherited_orbit_states_subset_fixed_points_eight,
    tribonacci_new_orbit_states_subset_fixed_points_eight⟩

theorem tribonacci_fixed_point_codes_eight_decompose :
    (fixedPointCodes 8).toFinset = tribonacciExpectedPointCodesEight := by
  symm
  apply Finset.eq_of_subset_of_card_le
    tribonacci_expected_point_codes_subset_fixed_points_eight
  calc
    (fixedPointCodes 8).toFinset.card ≤ (fixedPointCodes 8).length :=
      List.toFinset_card_le _
    _ = 131 := tribonacci_fixed_point_code_count_exactly_eight
    _ = tribonacciExpectedPointCodesEight.card :=
      tribonacci_period_eight_expected_point_code_count.symm

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixed
