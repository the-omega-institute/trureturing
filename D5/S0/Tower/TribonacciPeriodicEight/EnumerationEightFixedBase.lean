/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The one hundred thirty-one period-eight equations have a uniform nonzero denominator. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDisjoint
import D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
import D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixed
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDisjoint

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates
local notation "transition" => tribonacciPeriodicTransition

abbrev Step := TribonacciPeriodicStep
abbrev CodedState := TribonacciCodedState
abbrev PeriodicState := TribonacciPeriodicState

theorem tribonacci_closed_itinerary_denominator_eight (steps : List Step)
    (hlength : steps.length = 8) :
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

theorem tribonacci_fixed_point_code_count_exactly_eight :
    (fixedPointCodes 8).length = 131 := by
  have hlarge : (tribonacciClosedFrom .large 8).length = 81 := by
    decide
  have hsmall : (tribonacciClosedFrom .small 8).length = 13 := by
    decide
  have hcombined : (tribonacciClosedFrom .combined 8).length = 37 := by
    decide
  simp only [tribonacciFixedPointCodes, List.length_map,
    tribonacciClosedItineraries, List.length_append, hlarge, hsmall,
    hcombined]

def tribonacciPeriodicPointCodesEight : Finset CodedState :=
  tribonacciPeriodicPointCodesSeven ∪ (fixedPointCodes 8).toFinset

theorem tribonacci_periodic_point_enumeration_complete_exactly_eight
    (state : PeriodicState) (hperiod : (transition^[8]) state = state) :
    ∃ code, code ∈ (fixedPointCodes 8).toFinset /\
      state = decodeTribonacciState code := by
  have hlength := tribonacci_actual_steps_length 8 state
  have hnorm := tribonacci_closed_itinerary_denominator_eight
    (tribonacciActualSteps 8 state) hlength
  obtain ⟨code, hcode, hdecode⟩ :=
    tribonacci_periodic_point_enumeration_complete state hperiod hnorm
  exact ⟨code, List.mem_toFinset.mpr hcode, hdecode⟩

theorem tribonacci_periodic_point_enumeration_complete_eight {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 8)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ code, code ∈ tribonacciPeriodicPointCodesEight /\
      state = decodeTribonacciState code := by
  rcases lt_or_eq_of_le hperiodBound with hprior | rfl
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_seven hperiodPos
        (by omega) state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hdecode⟩
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_exactly_eight
        state hperiod
    exact ⟨code, Finset.mem_union_right _ hcode, hdecode⟩

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

theorem tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    (gap : TribonacciPeriodicGap) (steps : List Step)
    (hclosed : (tribonacciRotatedItineraries gap steps).Forall fun itinerary =>
      itinerary ∈ tribonacciClosedItineraries 8) :
    ((tribonacciRotatedItineraries gap steps).map
      tribonacciCodeOfItinerary).toFinset ⊆
        (fixedPointCodes 8).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset, tribonacciFixedPointCodes,
    List.mem_map] at hcode ⊢
  obtain ⟨itinerary, hitinerary, rfl⟩ := hcode
  exact ⟨itinerary,
    List.forall_iff_forall_mem.mp hclosed itinerary hitinerary, rfl⟩

def tribonacciPeriodEightExpandedInheritedOrbitA : TribonacciCodedOrbit :=
  tribonacciMakeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeLeft, .largeLeft, .largeLeft] []

def tribonacciPeriodEightExpandedInheritedOrbitB : TribonacciCodedOrbit :=
  tribonacciMakeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft] []

def tribonacciPeriodEightExpandedInheritedOrbitC : TribonacciCodedOrbit :=
  tribonacciMakeOrbit .small
    [.smallThrough, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedRight]
    [.smallThrough, .largeLeft]

def tribonacciPeriodEightExpandedInheritedOrbitD : TribonacciCodedOrbit :=
  tribonacciMakeOrbit .combined
    [.combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeLeft, .largeRight] []

theorem tribonacci_inherited_orbit_a_state_finset_eq_expanded_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitA).toFinset =
      (orbitStates tribonacciPeriodEightExpandedInheritedOrbitA).toFinset := by
  norm_num [tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightExpandedInheritedOrbitA,
    tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_inherited_orbit_b_state_finset_eq_expanded_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitB).toFinset =
      (orbitStates tribonacciPeriodEightExpandedInheritedOrbitB).toFinset := by
  norm_num [tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightExpandedInheritedOrbitB,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_inherited_orbit_c_state_finset_eq_expanded_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitC).toFinset =
      (orbitStates tribonacciPeriodEightExpandedInheritedOrbitC).toFinset := by
  norm_num [tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightExpandedInheritedOrbitC, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_inherited_orbit_d_state_finset_eq_expanded_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitD).toFinset =
      (orbitStates tribonacciPeriodEightExpandedInheritedOrbitD).toFinset := by
  norm_num [tribonacciPeriodEightInheritedOrbitD,
    tribonacciPeriodEightExpandedInheritedOrbitD, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_expanded_inherited_a_rotations_closed_eight :
    (tribonacciRotatedItineraries .large
        tribonacciPeriodEightExpandedInheritedOrbitA.steps).Forall
          (fun itinerary => itinerary ∈ tribonacciClosedItineraries 8) := by
  decide

theorem tribonacci_expanded_inherited_b_rotations_closed_eight :
    (tribonacciRotatedItineraries .large
        tribonacciPeriodEightExpandedInheritedOrbitB.steps).Forall
          (fun itinerary => itinerary ∈ tribonacciClosedItineraries 8) := by
  decide

theorem tribonacci_expanded_inherited_c_rotations_closed_eight :
    (tribonacciRotatedItineraries .small
        tribonacciPeriodEightExpandedInheritedOrbitC.steps).Forall
          (fun itinerary => itinerary ∈ tribonacciClosedItineraries 8) := by
  decide

theorem tribonacci_expanded_inherited_d_rotations_closed_eight :
    (tribonacciRotatedItineraries .combined
        tribonacciPeriodEightExpandedInheritedOrbitD.steps).Forall
          (fun itinerary => itinerary ∈ tribonacciClosedItineraries 8) := by
  decide

theorem tribonacci_expanded_inherited_a_states_eq_rotated_codes_eight :
    orbitStates tribonacciPeriodEightExpandedInheritedOrbitA =
        (tribonacciRotatedItineraries .large
          tribonacciPeriodEightExpandedInheritedOrbitA.steps).map
            tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightExpandedInheritedOrbitA,
    tribonacciMakeOrbit, tribonacciRotatedItineraries, List.range_succ,
    tribonacciGapAfterSteps, tribonacciCodeOfItinerary,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_expanded_inherited_b_states_eq_rotated_codes_eight :
    orbitStates tribonacciPeriodEightExpandedInheritedOrbitB =
        (tribonacciRotatedItineraries .large
          tribonacciPeriodEightExpandedInheritedOrbitB.steps).map
            tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightExpandedInheritedOrbitB,
    tribonacciMakeOrbit, tribonacciRotatedItineraries, List.range_succ,
    tribonacciGapAfterSteps, tribonacciCodeOfItinerary,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_expanded_inherited_c_states_eq_rotated_codes_eight :
    orbitStates tribonacciPeriodEightExpandedInheritedOrbitC =
        (tribonacciRotatedItineraries .small
          tribonacciPeriodEightExpandedInheritedOrbitC.steps).map
            tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightExpandedInheritedOrbitC,
    tribonacciMakeOrbit, tribonacciRotatedItineraries, List.range_succ,
    tribonacciGapAfterSteps, tribonacciCodeOfItinerary,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_expanded_inherited_d_states_eq_rotated_codes_eight :
    orbitStates tribonacciPeriodEightExpandedInheritedOrbitD =
        (tribonacciRotatedItineraries .combined
          tribonacciPeriodEightExpandedInheritedOrbitD.steps).map
            tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightExpandedInheritedOrbitD,
    tribonacciMakeOrbit, tribonacciRotatedItineraries, List.range_succ,
    tribonacciGapAfterSteps, tribonacciCodeOfItinerary,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_inherited_orbit_a_states_subset_fixed_points_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitA).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_inherited_orbit_a_state_finset_eq_expanded_eight,
    tribonacci_expanded_inherited_a_states_eq_rotated_codes_eight]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightExpandedInheritedOrbitA.steps
      tribonacci_expanded_inherited_a_rotations_closed_eight

theorem tribonacci_inherited_orbit_b_states_subset_fixed_points_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitB).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_inherited_orbit_b_state_finset_eq_expanded_eight,
    tribonacci_expanded_inherited_b_states_eq_rotated_codes_eight]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightExpandedInheritedOrbitB.steps
      tribonacci_expanded_inherited_b_rotations_closed_eight

theorem tribonacci_inherited_orbit_c_states_subset_fixed_points_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitC).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_inherited_orbit_c_state_finset_eq_expanded_eight,
    tribonacci_expanded_inherited_c_states_eq_rotated_codes_eight]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .small tribonacciPeriodEightExpandedInheritedOrbitC.steps
      tribonacci_expanded_inherited_c_rotations_closed_eight

theorem tribonacci_inherited_orbit_d_states_subset_fixed_points_eight :
    (orbitStates tribonacciPeriodEightInheritedOrbitD).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_inherited_orbit_d_state_finset_eq_expanded_eight,
    tribonacci_expanded_inherited_d_states_eq_rotated_codes_eight]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .combined tribonacciPeriodEightExpandedInheritedOrbitD.steps
      tribonacci_expanded_inherited_d_rotations_closed_eight

theorem tribonacci_inherited_orbit_states_subset_fixed_points_eight :
    (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  simpa only [tribonacciPeriodEightInheritedOrbits, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.toFinset_append,
    Finset.union_subset_iff] using
      ⟨tribonacci_inherited_orbit_a_states_subset_fixed_points_eight,
        tribonacci_inherited_orbit_b_states_subset_fixed_points_eight,
        tribonacci_inherited_orbit_c_states_subset_fixed_points_eight,
        tribonacci_inherited_orbit_d_states_subset_fixed_points_eight⟩

theorem tribonacci_period_eight_expected_point_code_count :
    tribonacciExpectedPointCodesEight.card = 131 := by
  rw [tribonacciExpectedPointCodesEight,
    List.toFinset_card_of_nodup tribonacci_period_eight_expected_state_codes_nodup]
  rw [tribonacciPeriodicOrbitRepresentativesAtEight, List.flatMap_append,
    List.length_append]
  have hinherited :
      (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates).length = 11 := by
    norm_num [tribonacciPeriodEightInheritedOrbits,
      tribonacciPeriodEightInheritedOrbitA,
      tribonacciPeriodEightInheritedOrbitB,
      tribonacciPeriodEightInheritedOrbitC,
      tribonacciPeriodEightInheritedOrbitD,
      tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit,
      tribonacciOrbitStates, tribonacciTraceCode]
  have hnew :
      (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
        orbitStates).length = 120 := by
    norm_num [tribonacciPeriodicOrbitRepresentativesExactlyEight,
      tribonacciPeriodEightOrbitA, tribonacciPeriodEightOrbitB,
      tribonacciPeriodEightOrbitC, tribonacciPeriodEightOrbitD,
      tribonacciPeriodEightOrbitE, tribonacciPeriodEightOrbitF,
      tribonacciPeriodEightOrbitG, tribonacciPeriodEightOrbitH,
      tribonacciPeriodEightOrbitI, tribonacciPeriodEightOrbitJ,
      tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
      tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
      tribonacciPeriodEightOrbitO, tribonacciMakeOrbit, tribonacciOrbitStates,
      tribonacciTraceCode]
  omega

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase
