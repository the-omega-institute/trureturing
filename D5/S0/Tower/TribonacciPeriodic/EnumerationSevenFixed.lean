/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixed
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-seven equations equal one inherited and seventy new phase states. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedB

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixed

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedB

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_new_orbit_states_subset_fixed_points_seven :
    (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
      orbitStates).toFinset ⊆ (fixedPointCodes 7).toFinset := by
  rw [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    show [tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
      tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
      tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
      tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
      tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ] =
        tribonacciPeriodSevenOrbitsFirst ++
          tribonacciPeriodSevenOrbitsLast by rfl,
    List.flatMap_append, List.toFinset_append, Finset.union_subset_iff]
  exact ⟨tribonacci_first_new_orbit_states_subset_fixed_points_seven,
    tribonacci_last_new_orbit_states_subset_fixed_points_seven⟩

theorem tribonacci_expected_point_codes_subset_fixed_points_seven :
    tribonacciExpectedPointCodesSeven ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacciExpectedPointCodesSeven,
    tribonacciPeriodicOrbitRepresentativesAtSeven, List.flatMap_append,
    List.toFinset_append, Finset.union_subset_iff]
  exact ⟨tribonacci_inherited_orbit_states_subset_fixed_points_seven,
    tribonacci_new_orbit_states_subset_fixed_points_seven⟩

theorem tribonacci_fixed_point_codes_seven_decompose :
    (fixedPointCodes 7).toFinset = tribonacciExpectedPointCodesSeven := by
  symm
  apply Finset.eq_of_subset_of_card_le
    tribonacci_expected_point_codes_subset_fixed_points_seven
  calc
    (fixedPointCodes 7).toFinset.card ≤ (fixedPointCodes 7).length :=
      List.toFinset_card_le _
    _ = 71 := tribonacci_fixed_point_code_count_exactly_seven
    _ = tribonacciExpectedPointCodesSeven.card :=
      tribonacci_period_seven_expected_point_code_count.symm

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixed
