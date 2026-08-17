/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The seventy-one period-seven equations have a uniform nonzero denominator. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates
local notation "transition" => tribonacciPeriodicTransition

abbrev Step := TribonacciPeriodicStep
abbrev CodedState := TribonacciCodedState
abbrev PeriodicState := TribonacciPeriodicState

theorem tribonacci_closed_itinerary_denominator_seven (steps : List Step)
    (hlength : steps.length = 7) :
    Ne (tribonacciCodeNorm
      (tribonacciCodeSub tribonacciCodeOne
        (tribonacciPathAffine steps).multiplier)) 0 := by
  rw [tribonacciPathAffine, tribonacci_path_affine_multiplier_aux, hlength]
  norm_num [tribonacciMultiplyByRoot,
    tribonacciIdentityAffine, tribonacciCodeNorm,
    tribonacciCodeCofactorZero, tribonacciCodeCofactorOne,
    tribonacciCodeCofactorTwo, tribonacciCodeSub, tribonacciCodeNeg,
    tribonacciCodeAdd, tribonacciCodeMul, tribonacciCodeOne,
    tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_fixed_point_code_count_exactly_seven :
    (fixedPointCodes 7).length = 71 := by
  decide

def tribonacciPeriodicPointCodesSeven : Finset CodedState :=
  tribonacciPeriodicPointCodesSix ∪ (fixedPointCodes 7).toFinset

theorem tribonacci_periodic_point_enumeration_complete_exactly_seven
    (state : PeriodicState) (hperiod : (transition^[7]) state = state) :
    ∃ code, code ∈ (fixedPointCodes 7).toFinset /\
      state = decodeTribonacciState code := by
  have hlength := tribonacci_actual_steps_length 7 state
  have hnorm := tribonacci_closed_itinerary_denominator_seven
    (tribonacciActualSteps 7 state) hlength
  obtain ⟨code, hcode, hdecode⟩ :=
    tribonacci_periodic_point_enumeration_complete state hperiod hnorm
  exact ⟨code, List.mem_toFinset.mpr hcode, hdecode⟩

theorem tribonacci_periodic_point_enumeration_complete_seven {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 7)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ code, code ∈ tribonacciPeriodicPointCodesSeven /\
      state = decodeTribonacciState code := by
  rcases lt_or_eq_of_le hperiodBound with hprior | rfl
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_six hperiodPos
        (by omega) state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hdecode⟩
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_exactly_seven
        state hperiod
    exact ⟨code, Finset.mem_union_right _ hcode, hdecode⟩

def tribonacciPeriodSevenInheritedOrbits : List TribonacciCodedOrbit :=
  [tribonacciMakeOrbit .large [.largeLeft] []]

def tribonacciPeriodicOrbitRepresentativesAtSeven :
    List TribonacciCodedOrbit :=
  tribonacciPeriodSevenInheritedOrbits ++
    tribonacciPeriodicOrbitRepresentativesExactlySeven

def tribonacciExpectedPointCodesSeven : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesAtSeven.flatMap
    orbitStates).toFinset

def tribonacciGapAfterSteps (gap : TribonacciPeriodicGap)
    (steps : List Step) : TribonacciPeriodicGap :=
  steps.foldl (fun _ step => tribonacciStepTarget step) gap

def tribonacciRotatedItineraries (gap : TribonacciPeriodicGap)
    (steps : List Step) :
    List (TribonacciPeriodicGap × List Step) :=
  (List.range steps.length).map fun phase =>
    (tribonacciGapAfterSteps gap (steps.take phase),
      steps.drop phase ++ steps.take phase)

def tribonacciCodeOfItinerary
    (itinerary : TribonacciPeriodicGap × List Step) : CodedState :=
  ⟨itinerary.1, tribonacciPathCandidateCode itinerary.2⟩

theorem tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    (gap : TribonacciPeriodicGap) (steps : List Step)
    (hclosed : (tribonacciRotatedItineraries gap steps).Forall fun itinerary =>
      itinerary ∈ tribonacciClosedItineraries 7) :
    ((tribonacciRotatedItineraries gap steps).map
      tribonacciCodeOfItinerary).toFinset ⊆
        (fixedPointCodes 7).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset, tribonacciFixedPointCodes,
    List.mem_map] at hcode ⊢
  obtain ⟨itinerary, hitinerary, rfl⟩ := hcode
  exact ⟨itinerary,
    List.forall_iff_forall_mem.mp hclosed itinerary hitinerary, rfl⟩

theorem tribonacci_period_seven_inherited_state_codes_nodup :
    (tribonacciPeriodSevenInheritedOrbits.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodSevenInheritedOrbits, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_inherited_new_state_codes_disjoint :
    List.Disjoint
      (tribonacciPeriodSevenInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
        orbitStates) := by
  rw [List.disjoint_left]
  intro code hinherited hnew
  have hold : code ∈
      (tribonacciPeriodicOrbitRepresentativesSix.flatMap orbitStates) := by
    have hfirst : code ∈
        orbitStates (tribonacciMakeOrbit .large [.largeLeft] []) := by
      simpa only [tribonacciPeriodSevenInheritedOrbits, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] using hinherited
    rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
      List.mem_append]
    left
    simp only [tribonacciPeriodicOrbitRepresentativesFive,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append]
    exact Or.inl hfirst
  exact (List.disjoint_left.mp
    tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven hold) hnew

theorem tribonacci_period_seven_expected_state_codes_nodup :
    (tribonacciPeriodicOrbitRepresentativesAtSeven.flatMap
      orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesAtSeven, List.flatMap_append,
    List.nodup_append']
  exact ⟨tribonacci_period_seven_inherited_state_codes_nodup,
    tribonacci_new_periodic_orbit_state_codes_nodup_seven,
    tribonacci_period_seven_inherited_new_state_codes_disjoint⟩

theorem tribonacci_period_seven_expected_point_code_count :
    tribonacciExpectedPointCodesSeven.card = 71 := by
  rw [tribonacciExpectedPointCodesSeven,
    List.toFinset_card_of_nodup
      tribonacci_period_seven_expected_state_codes_nodup]
  norm_num [tribonacciPeriodicOrbitRepresentativesAtSeven,
    tribonacciPeriodSevenInheritedOrbits,
    tribonacciPeriodicOrbitRepresentativesExactlySeven,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
    tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode]

theorem tribonacci_inherited_orbit_states_subset_fixed_points_seven :
    (tribonacciPeriodSevenInheritedOrbits.flatMap orbitStates).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset] at hcode ⊢
  simp [tribonacciPeriodSevenInheritedOrbits, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciFixedPointCodes,
    tribonacciClosedItineraries, tribonacciClosedFrom,
    tribonacciPathsFrom] at hcode ⊢
  norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot] at hcode ⊢
  tauto

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase
