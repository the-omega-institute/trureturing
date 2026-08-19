/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenAggregate
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenAggregate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-at-most-ten enumeration has maximin exactly the champion value. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC
import D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineAggregate

/- Library-search audit trail (2026-08-18):
   * Searched the level before building anything.  Unlike period nine, this level
     already carries both the representative list and the aggregate low-arm
     bound, under names that do not follow the period-eight convention
     (`tribonacciPeriodTenOrbitRepresentatives`, not `...ExactlyTen`).  Neither
     is rebuilt here; a count of matches would have missed them, since the golden
     tower uses the same statement names.
   * What is missing at this level is the same pair that was missing at nine: the
     membership of each recorded low state in its own orbit, and the cumulative
     list with its optimality statement. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenAggregate

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEight
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineAggregate
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

/-- Each period-ten certificate's recorded low state is one of its own states. -/
theorem tribonacci_new_periodic_orbit_low_states_mem_ten :
    tribonacciPeriodTenOrbitRepresentatives.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  norm_num [tribonacciPeriodTenOrbitRepresentatives,
    tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
    tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit06,
    tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08, tribonacciPeriodTenOrbit09,
    tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12,
    tribonacciPeriodTenOrbit13, tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15,
    tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
    tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit21,
    tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
    tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27,
    tribonacciPeriodTenOrbit28, tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30,
    tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
    tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35, tribonacciPeriodTenOrbit36,
    tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38, tribonacciPeriodTenOrbit39,
    tribonacciPeriodTenOrbit40, tribonacciPeriodTenOrbit41, tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode]

/-- The cumulative list through period ten. -/
def tribonacciPeriodicOrbitRepresentativesTen : List TribonacciCodedOrbit :=
  tribonacciPeriodicOrbitRepresentativesNine ++
    tribonacciPeriodTenOrbitRepresentatives

theorem tribonacci_periodic_orbit_low_states_mem_ten :
    tribonacciPeriodicOrbitRepresentativesTen.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesTen, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem_nine,
    tribonacci_new_periodic_orbit_low_states_mem_ten⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_ten :
    tribonacciPeriodicOrbitRepresentativesTen.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesTen, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded_nine,
    tribonacci_period_ten_low_arms_bounded⟩

/-- The minima attained across the cumulative period-at-most-ten enumeration. -/
def tribonacciPeriodicOrbitMinimaTen : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesTen,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-ten enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit. -/
theorem tribonacci_periodic_orbit_maximin_ten :
    IsGreatest tribonacciPeriodicOrbitMinimaTen (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesTen,
      tribonacciPeriodicOrbitRepresentativesNine,
      tribonacciPeriodicOrbitRepresentativesEight,
      tribonacciPeriodicOrbitRepresentativesSeven,
      D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_ten orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_ten orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenAggregate
