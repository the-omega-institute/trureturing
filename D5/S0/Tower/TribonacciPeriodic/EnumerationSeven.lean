/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSeven
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSeven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-seven Tribonacci enumeration with unchanged maximin. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenMaximinA

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSeven

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.TribonacciPeriodic.EnumerationSix
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixed
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenMaximinA

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "transition" => tribonacciPeriodicTransition
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

abbrev CodedState := TribonacciCodedState
abbrev PeriodicState := TribonacciPeriodicState

def tribonacciEnumeratedOrbitStatesSeven : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesSeven.flatMap orbitStates).toFinset

def tribonacciInheritedPointCodesSeven : Finset CodedState :=
  (tribonacciPeriodSevenInheritedOrbits.flatMap orbitStates).toFinset

def tribonacciNewOrbitStatesSeven : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
    orbitStates).toFinset

theorem tribonacci_expected_point_codes_seven_decompose :
    tribonacciExpectedPointCodesSeven =
      tribonacciInheritedPointCodesSeven ∪
        tribonacciNewOrbitStatesSeven := by
  rw [tribonacciExpectedPointCodesSeven,
    tribonacciPeriodicOrbitRepresentativesAtSeven, List.flatMap_append,
    List.toFinset_append]
  rfl

theorem tribonacci_inherited_point_codes_seven_subset_six :
    tribonacciInheritedPointCodesSeven ⊆
      tribonacciPeriodicPointCodesSix := by
  intro code hcode
  rw [← tribonacci_enumerated_orbit_states_eq_fixed_points_six]
  rw [tribonacciInheritedPointCodesSeven, List.mem_toFinset,
    tribonacciPeriodSevenInheritedOrbits, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at hcode
  rw [tribonacciEnumeratedOrbitStatesSix, List.mem_toFinset,
    tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.mem_append]
  left
  rw [tribonacciPeriodicOrbitRepresentativesFive, List.flatMap_cons,
    List.mem_append]
  exact Or.inl hcode

theorem tribonacci_prior_union_fixed_points_seven :
    tribonacciPeriodicPointCodesSix ∪
        (tribonacciFixedPointCodes 7).toFinset =
      tribonacciPeriodicPointCodesSix ∪
        tribonacciNewOrbitStatesSeven := by
  rw [tribonacci_fixed_point_codes_seven_decompose,
    tribonacci_expected_point_codes_seven_decompose]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl
        (tribonacci_inherited_point_codes_seven_subset_six hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

/-- The twenty-five explicit cycles contain exactly all fixed-point codes
through period seven. -/
theorem tribonacci_enumerated_orbit_states_eq_fixed_points_seven :
    tribonacciEnumeratedOrbitStatesSeven =
      tribonacciPeriodicPointCodesSeven := by
  rw [tribonacciEnumeratedOrbitStatesSeven,
    tribonacciPeriodicOrbitRepresentativesSeven, List.flatMap_append,
    List.toFinset_append]
  change tribonacciEnumeratedOrbitStatesSix ∪
      tribonacciNewOrbitStatesSeven = tribonacciPeriodicPointCodesSeven
  rw [tribonacci_enumerated_orbit_states_eq_fixed_points_six,
    tribonacciPeriodicPointCodesSeven,
    tribonacci_prior_union_fixed_points_seven]

theorem tribonacci_periodic_orbit_representatives_valid_seven :
    tribonacciPeriodicOrbitRepresentativesSeven.Forall
      tribonacciCodedOrbitValid := by
  rw [tribonacciPeriodicOrbitRepresentativesSeven, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_representatives_valid_six,
    tribonacci_new_periodic_orbit_representatives_valid_seven⟩

theorem tribonacci_periodic_orbit_low_states_mem_seven :
    tribonacciPeriodicOrbitRepresentativesSeven.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesSeven, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem_six,
    tribonacci_new_periodic_orbit_low_states_mem_seven⟩

theorem tribonacci_new_periodic_state_count_seven :
    tribonacciNewOrbitStatesSeven.card = 70 := by
  rw [tribonacciNewOrbitStatesSeven,
    List.toFinset_card_of_nodup
      tribonacci_new_periodic_orbit_state_codes_nodup_seven]
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
    tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode]

/-- Ten new primitive cycles contribute seventy phases, for twenty-five cycles
and one hundred thirty-seven distinct periodic phase states in total. -/
theorem tribonacci_periodic_code_partition_seven :
    tribonacciPeriodicOrbitRepresentativesSeven.length = 25 /\
      tribonacciEnumeratedOrbitStatesSeven.card = 137 := by
  constructor
  · norm_num [tribonacciPeriodicOrbitRepresentativesSeven,
      tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive,
      tribonacciPeriodicOrbitRepresentativesExactlySix,
      tribonacciPeriodicOrbitRepresentativesExactlySeven]
  · rw [tribonacciEnumeratedOrbitStatesSeven,
      List.toFinset_card_of_nodup
        tribonacci_periodic_orbit_state_codes_nodup_seven]
    rw [tribonacciPeriodicOrbitRepresentativesSeven, List.flatMap_append,
      List.length_append]
    have hold :
        (tribonacciPeriodicOrbitRepresentativesSix.flatMap
          orbitStates).length = 67 := by
      rw [← List.toFinset_card_of_nodup
        tribonacci_periodic_orbit_state_codes_nodup_six]
      exact tribonacci_periodic_code_partition_six.2
    have hnew :
        (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
          orbitStates).length = 70 := by
      rw [← List.toFinset_card_of_nodup
        tribonacci_new_periodic_orbit_state_codes_nodup_seven]
      exact tribonacci_new_periodic_state_count_seven
    omega

/-- Every real state fixed by a nonzero iterate of period at most seven occurs
on one of the twenty-five decoded cycles. -/
theorem tribonacci_periodic_orbit_enumeration_complete_seven {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 7)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesSeven,
      state ∈ decodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    tribonacci_periodic_point_enumeration_complete_seven
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ tribonacciEnumeratedOrbitStatesSeven := by
    rw [tribonacci_enumerated_orbit_states_eq_fixed_points_seven]
    exact hcode
  rw [tribonacciEnumeratedOrbitStatesSeven, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [tribonacciDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem tribonacci_new_periodic_orbit_low_arms_bounded_seven :
    tribonacciPeriodicOrbitRepresentativesExactlySeven.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    List.forall_cons]
  exact ⟨tribonacci_period_seven_orbit_a_low_arm,
    tribonacci_period_seven_orbit_b_low_arm,
    tribonacci_period_seven_orbit_c_low_arm,
    tribonacci_period_seven_orbit_d_low_arm,
    tribonacci_period_seven_orbit_e_low_arm,
    tribonacci_period_seven_orbit_f_low_arm,
    tribonacci_period_seven_orbit_g_low_arm,
    tribonacci_period_seven_orbit_h_low_arm,
    tribonacci_period_seven_orbit_i_low_arm,
    tribonacci_period_seven_orbit_j_low_arm, by simp⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_seven :
    tribonacciPeriodicOrbitRepresentativesSeven.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesSeven, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded_six,
    tribonacci_new_periodic_orbit_low_arms_bounded_seven⟩

def tribonacciPeriodicOrbitMinimaSeven : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesSeven,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-seven enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit. -/
theorem tribonacci_periodic_orbit_maximin_seven :
    IsGreatest tribonacciPeriodicOrbitMinimaSeven (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesSeven,
      tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_seven orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_seven orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
