/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-eight Tribonacci enumeration with unchanged maximin. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightMaximinA

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEight

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixed
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightMaximinA

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "transition" => tribonacciPeriodicTransition
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

abbrev CodedState := TribonacciCodedState
abbrev PeriodicState := TribonacciPeriodicState

def tribonacciEnumeratedOrbitStatesEight : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesEight.flatMap orbitStates).toFinset

def tribonacciInheritedPointCodesEight : Finset CodedState :=
  (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates).toFinset

def tribonacciNewOrbitStatesEight : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
    orbitStates).toFinset

theorem tribonacci_expected_point_codes_eight_decompose :
    tribonacciExpectedPointCodesEight =
      tribonacciInheritedPointCodesEight ∪
        tribonacciNewOrbitStatesEight := by
  rw [tribonacciExpectedPointCodesEight,
    tribonacciPeriodicOrbitRepresentativesAtEight, List.flatMap_append,
    List.toFinset_append]
  rfl

theorem tribonacci_period_eight_inherited_orbits_mem_seven :
    tribonacciPeriodEightInheritedOrbits.Forall fun orbit =>
      orbit ∈ tribonacciPeriodicOrbitRepresentativesSeven := by
  simp [tribonacciPeriodEightInheritedOrbits,
    tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightInheritedOrbitD,
    tribonacciPeriodicOrbitRepresentativesSeven,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
    tribonacciPeriodicOrbitRepresentativesFive]

theorem tribonacci_inherited_point_codes_eight_subset_seven :
    tribonacciInheritedPointCodesEight ⊆
      tribonacciPeriodicPointCodesSeven := by
  intro code hcode
  rw [← tribonacci_enumerated_orbit_states_eq_fixed_points_seven]
  rw [tribonacciInheritedPointCodesEight, List.mem_toFinset] at hcode
  rw [tribonacciEnumeratedOrbitStatesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap] at hcode ⊢
  obtain ⟨orbit, horbit, hstate⟩ := hcode
  exact ⟨orbit, List.forall_iff_forall_mem.mp
    tribonacci_period_eight_inherited_orbits_mem_seven orbit horbit, hstate⟩

theorem tribonacci_prior_union_fixed_points_eight :
    tribonacciPeriodicPointCodesSeven ∪
        (tribonacciFixedPointCodes 8).toFinset =
      tribonacciPeriodicPointCodesSeven ∪
        tribonacciNewOrbitStatesEight := by
  rw [tribonacci_fixed_point_codes_eight_decompose,
    tribonacci_expected_point_codes_eight_decompose]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl
        (tribonacci_inherited_point_codes_eight_subset_seven hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

/-- The forty explicit cycles contain exactly all generated fixed-point codes
through period eight. -/
theorem tribonacci_enumerated_orbit_states_eq_fixed_points_eight :
    tribonacciEnumeratedOrbitStatesEight =
      tribonacciPeriodicPointCodesEight := by
  rw [tribonacciEnumeratedOrbitStatesEight,
    tribonacciPeriodicOrbitRepresentativesEight, List.flatMap_append,
    List.toFinset_append]
  change tribonacciEnumeratedOrbitStatesSeven ∪
      tribonacciNewOrbitStatesEight = tribonacciPeriodicPointCodesEight
  rw [tribonacci_enumerated_orbit_states_eq_fixed_points_seven,
    tribonacciPeriodicPointCodesEight,
    tribonacci_prior_union_fixed_points_eight]

theorem tribonacci_periodic_orbit_representatives_valid_eight :
    tribonacciPeriodicOrbitRepresentativesEight.Forall
      tribonacciCodedOrbitValid := by
  rw [tribonacciPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_representatives_valid_seven,
    tribonacci_new_periodic_orbit_representatives_valid_eight⟩

theorem tribonacci_periodic_orbit_low_states_mem_eight :
    tribonacciPeriodicOrbitRepresentativesEight.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem_seven,
    tribonacci_new_periodic_orbit_low_states_mem_eight⟩

theorem tribonacci_new_periodic_state_count_eight :
    tribonacciNewOrbitStatesEight.card = 120 := by
  rw [tribonacciNewOrbitStatesEight,
    List.toFinset_card_of_nodup
      tribonacci_new_periodic_orbit_state_codes_nodup_eight]
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlyEight,
    tribonacciPeriodEightOrbitA, tribonacciPeriodEightOrbitB,
    tribonacciPeriodEightOrbitC, tribonacciPeriodEightOrbitD,
    tribonacciPeriodEightOrbitE, tribonacciPeriodEightOrbitF,
    tribonacciPeriodEightOrbitG, tribonacciPeriodEightOrbitH,
    tribonacciPeriodEightOrbitI, tribonacciPeriodEightOrbitJ,
    tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
    tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
    tribonacciPeriodEightOrbitO, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode]

/-- Fifteen new primitive cycles contribute one hundred twenty phases, for
forty representative cycles and two hundred fifty-seven phase certificates. -/
theorem tribonacci_periodic_code_partition_eight :
    tribonacciPeriodicOrbitRepresentativesEight.length = 40 /\
      (tribonacciPeriodicOrbitRepresentativesEight.flatMap
        orbitStates).length = 257 := by
  constructor
  · norm_num [tribonacciPeriodicOrbitRepresentativesEight,
      tribonacciPeriodicOrbitRepresentativesSeven,
      D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive,
      tribonacciPeriodicOrbitRepresentativesExactlySix,
      tribonacciPeriodicOrbitRepresentativesExactlySeven,
      tribonacciPeriodicOrbitRepresentativesExactlyEight]
  · rw [tribonacciPeriodicOrbitRepresentativesEight, List.flatMap_append,
      List.length_append]
    have hprior :
        (tribonacciPeriodicOrbitRepresentativesSeven.flatMap
          orbitStates).length = 137 := by
      rw [← List.toFinset_card_of_nodup
        D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint.tribonacci_periodic_orbit_state_codes_nodup_seven]
      exact tribonacci_periodic_code_partition_seven.2
    have hnew :
        (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
          orbitStates).length = 120 := by
      rw [← List.toFinset_card_of_nodup
        tribonacci_new_periodic_orbit_state_codes_nodup_eight]
      exact tribonacci_new_periodic_state_count_eight
    omega

/-- Every real state fixed by a nonzero iterate of period at most eight occurs
on one of the forty decoded cycles. -/
theorem tribonacci_periodic_orbit_enumeration_complete_eight {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 8)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesEight,
      state ∈ decodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    tribonacci_periodic_point_enumeration_complete_eight
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ tribonacciEnumeratedOrbitStatesEight := by
    rw [tribonacci_enumerated_orbit_states_eq_fixed_points_eight]
    exact hcode
  rw [tribonacciEnumeratedOrbitStatesEight, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [tribonacciDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem tribonacci_new_periodic_orbit_low_arms_bounded_eight :
    tribonacciPeriodicOrbitRepresentativesExactlyEight.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlyEight,
    List.forall_cons]
  exact ⟨tribonacci_period_eight_orbit_a_low_arm,
    tribonacci_period_eight_orbit_b_low_arm,
    tribonacci_period_eight_orbit_c_low_arm,
    tribonacci_period_eight_orbit_d_low_arm,
    tribonacci_period_eight_orbit_e_low_arm,
    tribonacci_period_eight_orbit_f_low_arm,
    tribonacci_period_eight_orbit_g_low_arm,
    tribonacci_period_eight_orbit_h_low_arm,
    tribonacci_period_eight_orbit_i_low_arm,
    tribonacci_period_eight_orbit_j_low_arm,
    tribonacci_period_eight_orbit_k_low_arm,
    tribonacci_period_eight_orbit_l_low_arm,
    tribonacci_period_eight_orbit_m_low_arm,
    tribonacci_period_eight_orbit_n_low_arm,
    tribonacci_period_eight_orbit_o_low_arm, by simp⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_eight :
    tribonacciPeriodicOrbitRepresentativesEight.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded_seven,
    tribonacci_new_periodic_orbit_low_arms_bounded_eight⟩

def tribonacciPeriodicOrbitMinimaEight : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesEight,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-eight enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit. -/
theorem tribonacci_periodic_orbit_maximin_eight :
    IsGreatest tribonacciPeriodicOrbitMinimaEight (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesEight,
      tribonacciPeriodicOrbitRepresentativesSeven,
      D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_eight orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_eight orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEight
