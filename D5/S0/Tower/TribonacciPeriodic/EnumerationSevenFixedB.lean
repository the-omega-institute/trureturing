/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All ten period-seven orbits occur among the generated equations. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedB

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedBase

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_period_seven_rotations_closed_a :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitA.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_a :
    orbitStates tribonacciPeriodSevenOrbitA =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitA.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitA, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_a_seven :
    (orbitStates tribonacciPeriodSevenOrbitA).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_a]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitA.steps
      tribonacci_period_seven_rotations_closed_a

theorem tribonacci_period_seven_rotations_closed_b :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitB.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_b :
    orbitStates tribonacciPeriodSevenOrbitB =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitB.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitB, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_b_seven :
    (orbitStates tribonacciPeriodSevenOrbitB).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_b]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitB.steps
      tribonacci_period_seven_rotations_closed_b

theorem tribonacci_period_seven_rotations_closed_c :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitC.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_c :
    orbitStates tribonacciPeriodSevenOrbitC =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitC.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitC, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_c_seven :
    (orbitStates tribonacciPeriodSevenOrbitC).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_c]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitC.steps
      tribonacci_period_seven_rotations_closed_c

theorem tribonacci_period_seven_rotations_closed_d :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitD.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_d :
    orbitStates tribonacciPeriodSevenOrbitD =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitD.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitD, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_d_seven :
    (orbitStates tribonacciPeriodSevenOrbitD).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_d]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitD.steps
      tribonacci_period_seven_rotations_closed_d

theorem tribonacci_period_seven_rotations_closed_e :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitE.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_e :
    orbitStates tribonacciPeriodSevenOrbitE =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitE.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitE, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_e_seven :
    (orbitStates tribonacciPeriodSevenOrbitE).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_e]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitE.steps
      tribonacci_period_seven_rotations_closed_e

theorem tribonacci_first_new_orbit_states_subset_fixed_points_seven :
    (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 7).toFinset := by
  simpa only [tribonacciPeriodSevenOrbitsFirst,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toFinset_append, Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_a_seven,
        tribonacci_orbit_states_subset_fixed_points_b_seven,
        tribonacci_orbit_states_subset_fixed_points_c_seven,
        tribonacci_orbit_states_subset_fixed_points_d_seven,
        tribonacci_orbit_states_subset_fixed_points_e_seven⟩

theorem tribonacci_period_seven_rotations_closed_f :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitF.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_f :
    orbitStates tribonacciPeriodSevenOrbitF =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitF.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitF, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_f_seven :
    (orbitStates tribonacciPeriodSevenOrbitF).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_f]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitF.steps
      tribonacci_period_seven_rotations_closed_f

theorem tribonacci_period_seven_rotations_closed_g :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitG.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_g :
    orbitStates tribonacciPeriodSevenOrbitG =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitG.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitG, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_g_seven :
    (orbitStates tribonacciPeriodSevenOrbitG).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_g]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitG.steps
      tribonacci_period_seven_rotations_closed_g

theorem tribonacci_period_seven_rotations_closed_h :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitH.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_h :
    orbitStates tribonacciPeriodSevenOrbitH =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitH.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitH, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_h_seven :
    (orbitStates tribonacciPeriodSevenOrbitH).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_h]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitH.steps
      tribonacci_period_seven_rotations_closed_h

theorem tribonacci_period_seven_rotations_closed_i :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitI.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_i :
    orbitStates tribonacciPeriodSevenOrbitI =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitI.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitI, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_i_seven :
    (orbitStates tribonacciPeriodSevenOrbitI).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_i]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitI.steps
      tribonacci_period_seven_rotations_closed_i

theorem tribonacci_period_seven_rotations_closed_j :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodSevenOrbitJ.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 7 := by
  decide

theorem tribonacci_period_seven_states_eq_rotated_codes_j :
    orbitStates tribonacciPeriodSevenOrbitJ =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodSevenOrbitJ.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodSevenOrbitJ, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_j_seven :
    (orbitStates tribonacciPeriodSevenOrbitJ).toFinset ⊆
      (fixedPointCodes 7).toFinset := by
  rw [tribonacci_period_seven_states_eq_rotated_codes_j]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_seven
    .large tribonacciPeriodSevenOrbitJ.steps
      tribonacci_period_seven_rotations_closed_j

theorem tribonacci_last_new_orbit_states_subset_fixed_points_seven :
    (tribonacciPeriodSevenOrbitsLast.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 7).toFinset := by
  simpa only [tribonacciPeriodSevenOrbitsLast,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toFinset_append, Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_f_seven,
        tribonacci_orbit_states_subset_fixed_points_g_seven,
        tribonacci_orbit_states_subset_fixed_points_h_seven,
        tribonacci_orbit_states_subset_fixed_points_i_seven,
        tribonacci_orbit_states_subset_fixed_points_j_seven⟩

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixedB
