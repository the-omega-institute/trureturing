/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenAggregate
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenAggregate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-at-most-eleven enumeration has maximin exactly the champion value. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinE
import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenAggregate

/- Library-search audit trail (2026-08-18):
   * Searched the level first, as at period ten.  The representative list and the
     aggregate low-arm bound already exist here as well; neither is rebuilt.
   * Missing is the same pair as at the two shorter levels: each recorded low
     state's membership in its own orbit, and the cumulative list with its
     optimality statement.  This is the level the source sentence names, so with
     it the claim "the enumeration up to period eleven exhibits the optimal
     cycle" acquires a formal counterpart at the period it actually states. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenAggregate

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
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenAggregate
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinE

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

/-- Each period-eleven certificate's recorded low state is one of its own states. -/
theorem tribonacci_new_periodic_orbit_low_states_mem_eleven :
    tribonacciPeriodElevenOrbitRepresentatives.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  norm_num [tribonacciPeriodElevenOrbitRepresentatives,
    tribonacciPeriodElevenOrbit01, tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
    tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit05, tribonacciPeriodElevenOrbit06,
    tribonacciPeriodElevenOrbit07, tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit09,
    tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11, tribonacciPeriodElevenOrbit12,
    tribonacciPeriodElevenOrbit13, tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
    tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit17, tribonacciPeriodElevenOrbit18,
    tribonacciPeriodElevenOrbit19, tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit21,
    tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23, tribonacciPeriodElevenOrbit24,
    tribonacciPeriodElevenOrbit25, tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
    tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit29, tribonacciPeriodElevenOrbit30,
    tribonacciPeriodElevenOrbit31, tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit33,
    tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35, tribonacciPeriodElevenOrbit36,
    tribonacciPeriodElevenOrbit37, tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
    tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit41, tribonacciPeriodElevenOrbit42,
    tribonacciPeriodElevenOrbit43, tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit45,
    tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47, tribonacciPeriodElevenOrbit48,
    tribonacciPeriodElevenOrbit49, tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
    tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit53, tribonacciPeriodElevenOrbit54,
    tribonacciPeriodElevenOrbit55, tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit57,
    tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59, tribonacciPeriodElevenOrbit60,
    tribonacciPeriodElevenOrbit61, tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
    tribonacciPeriodElevenOrbit64, tribonacciPeriodElevenOrbit65, tribonacciPeriodElevenOrbit66,
    tribonacciPeriodElevenOrbit67, tribonacciPeriodElevenOrbit68, tribonacciPeriodElevenOrbit69,
    tribonacciPeriodElevenOrbit70, tribonacciPeriodElevenOrbit71, tribonacciPeriodElevenOrbit72,
    tribonacciPeriodElevenOrbit73, tribonacciPeriodElevenOrbit74, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode]

/-- The cumulative list through period eleven. -/
def tribonacciPeriodicOrbitRepresentativesEleven : List TribonacciCodedOrbit :=
  tribonacciPeriodicOrbitRepresentativesTen ++
    tribonacciPeriodElevenOrbitRepresentatives

theorem tribonacci_periodic_orbit_low_states_mem_eleven :
    tribonacciPeriodicOrbitRepresentativesEleven.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesEleven, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem_ten,
    tribonacci_new_periodic_orbit_low_states_mem_eleven⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_eleven :
    tribonacciPeriodicOrbitRepresentativesEleven.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesEleven, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded_ten,
    tribonacci_period_eleven_low_arms_bounded⟩

/-- The minima attained across the cumulative period-at-most-eleven enumeration. -/
def tribonacciPeriodicOrbitMinimaEleven : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesEleven,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-eleven enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit.  This is the
period the source sentence names. -/
theorem tribonacci_periodic_orbit_maximin_eleven :
    IsGreatest tribonacciPeriodicOrbitMinimaEleven (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesEleven,
      tribonacciPeriodicOrbitRepresentativesTen,
      tribonacciPeriodicOrbitRepresentativesNine,
      tribonacciPeriodicOrbitRepresentativesEight,
      tribonacciPeriodicOrbitRepresentativesSeven,
      D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_eleven orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_eleven orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenAggregate
