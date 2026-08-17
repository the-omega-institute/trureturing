/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All fifteen primitive period-eight orbits occur among the generated equations. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedB

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedBase

local notation "fixedPointCodes" => tribonacciFixedPointCodes
local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_period_eight_rotations_closed_a :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitA.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_a :
    orbitStates tribonacciPeriodEightOrbitA =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitA.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitA, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_a_eight :
    (orbitStates tribonacciPeriodEightOrbitA).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_a]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitA.steps
      tribonacci_period_eight_rotations_closed_a

theorem tribonacci_period_eight_rotations_closed_b :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitB.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_b :
    orbitStates tribonacciPeriodEightOrbitB =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitB.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitB, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_b_eight :
    (orbitStates tribonacciPeriodEightOrbitB).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_b]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitB.steps
      tribonacci_period_eight_rotations_closed_b

theorem tribonacci_period_eight_rotations_closed_c :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitC.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_c :
    orbitStates tribonacciPeriodEightOrbitC =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitC.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitC, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_c_eight :
    (orbitStates tribonacciPeriodEightOrbitC).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_c]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitC.steps
      tribonacci_period_eight_rotations_closed_c

theorem tribonacci_period_eight_rotations_closed_d :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitD.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_d :
    orbitStates tribonacciPeriodEightOrbitD =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitD.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitD, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_d_eight :
    (orbitStates tribonacciPeriodEightOrbitD).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_d]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitD.steps
      tribonacci_period_eight_rotations_closed_d

theorem tribonacci_period_eight_rotations_closed_e :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitE.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_e :
    orbitStates tribonacciPeriodEightOrbitE =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitE.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitE, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_e_eight :
    (orbitStates tribonacciPeriodEightOrbitE).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_e]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitE.steps
      tribonacci_period_eight_rotations_closed_e

theorem tribonacci_first_new_orbit_states_subset_fixed_points_eight :
    (tribonacciPeriodEightOrbitsFirst.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 8).toFinset := by
  simpa only [tribonacciPeriodEightOrbitsFirst,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toFinset_append, Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_a_eight,
        tribonacci_orbit_states_subset_fixed_points_b_eight,
        tribonacci_orbit_states_subset_fixed_points_c_eight,
        tribonacci_orbit_states_subset_fixed_points_d_eight,
        tribonacci_orbit_states_subset_fixed_points_e_eight⟩

theorem tribonacci_period_eight_rotations_closed_f :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitF.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_f :
    orbitStates tribonacciPeriodEightOrbitF =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitF.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitF, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_f_eight :
    (orbitStates tribonacciPeriodEightOrbitF).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_f]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitF.steps
      tribonacci_period_eight_rotations_closed_f

theorem tribonacci_period_eight_rotations_closed_g :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitG.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_g :
    orbitStates tribonacciPeriodEightOrbitG =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitG.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitG, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_g_eight :
    (orbitStates tribonacciPeriodEightOrbitG).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_g]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitG.steps
      tribonacci_period_eight_rotations_closed_g

theorem tribonacci_period_eight_rotations_closed_h :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitH.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_h :
    orbitStates tribonacciPeriodEightOrbitH =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitH.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitH, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_h_eight :
    (orbitStates tribonacciPeriodEightOrbitH).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_h]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitH.steps
      tribonacci_period_eight_rotations_closed_h

theorem tribonacci_period_eight_rotations_closed_i :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitI.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_i :
    orbitStates tribonacciPeriodEightOrbitI =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitI.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitI, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_i_eight :
    (orbitStates tribonacciPeriodEightOrbitI).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_i]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitI.steps
      tribonacci_period_eight_rotations_closed_i

theorem tribonacci_period_eight_rotations_closed_j :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitJ.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_j :
    orbitStates tribonacciPeriodEightOrbitJ =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitJ.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitJ, tribonacciMakeOrbit,
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

theorem tribonacci_orbit_states_subset_fixed_points_j_eight :
    (orbitStates tribonacciPeriodEightOrbitJ).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_j]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitJ.steps
      tribonacci_period_eight_rotations_closed_j

theorem tribonacci_period_eight_rotations_closed_k :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitK.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_k :
    orbitStates tribonacciPeriodEightOrbitK =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitK.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitK, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_k_eight :
    (orbitStates tribonacciPeriodEightOrbitK).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_k]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitK.steps
      tribonacci_period_eight_rotations_closed_k

theorem tribonacci_period_eight_rotations_closed_l :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitL.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_l :
    orbitStates tribonacciPeriodEightOrbitL =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitL.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitL, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_l_eight :
    (orbitStates tribonacciPeriodEightOrbitL).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_l]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitL.steps
      tribonacci_period_eight_rotations_closed_l

theorem tribonacci_period_eight_rotations_closed_m :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitM.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_m :
    orbitStates tribonacciPeriodEightOrbitM =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitM.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitM, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_m_eight :
    (orbitStates tribonacciPeriodEightOrbitM).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_m]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitM.steps
      tribonacci_period_eight_rotations_closed_m

theorem tribonacci_period_eight_rotations_closed_n :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitN.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_n :
    orbitStates tribonacciPeriodEightOrbitN =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitN.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitN, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_n_eight :
    (orbitStates tribonacciPeriodEightOrbitN).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_n]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitN.steps
      tribonacci_period_eight_rotations_closed_n

theorem tribonacci_period_eight_rotations_closed_o :
    (tribonacciRotatedItineraries .large
      tribonacciPeriodEightOrbitO.steps).Forall fun itinerary =>
        itinerary ∈ tribonacciClosedItineraries 8 := by
  decide

theorem tribonacci_period_eight_states_eq_rotated_codes_o :
    orbitStates tribonacciPeriodEightOrbitO =
      (tribonacciRotatedItineraries .large
        tribonacciPeriodEightOrbitO.steps).map tribonacciCodeOfItinerary := by
  norm_num [tribonacciPeriodEightOrbitO, tribonacciMakeOrbit,
    tribonacciRotatedItineraries, List.range_succ, tribonacciGapAfterSteps,
    tribonacciCodeOfItinerary, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_orbit_states_subset_fixed_points_o_eight :
    (orbitStates tribonacciPeriodEightOrbitO).toFinset ⊆
      (fixedPointCodes 8).toFinset := by
  rw [tribonacci_period_eight_states_eq_rotated_codes_o]
  exact tribonacci_rotated_itinerary_codes_subset_fixed_points_eight
    .large tribonacciPeriodEightOrbitO.steps
      tribonacci_period_eight_rotations_closed_o

theorem tribonacci_middle_new_orbit_states_subset_fixed_points_eight :
    (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 8).toFinset := by
  simpa only [tribonacciPeriodEightOrbitsMiddle, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.toFinset_append,
    Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_f_eight,
        tribonacci_orbit_states_subset_fixed_points_g_eight,
        tribonacci_orbit_states_subset_fixed_points_h_eight,
        tribonacci_orbit_states_subset_fixed_points_i_eight,
        tribonacci_orbit_states_subset_fixed_points_j_eight⟩

theorem tribonacci_last_new_orbit_states_subset_fixed_points_eight :
    (tribonacciPeriodEightOrbitsLast.flatMap orbitStates).toFinset ⊆
        (fixedPointCodes 8).toFinset := by
  simpa only [tribonacciPeriodEightOrbitsLast, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.toFinset_append,
    Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_k_eight,
        tribonacci_orbit_states_subset_fixed_points_l_eight,
        tribonacci_orbit_states_subset_fixed_points_m_eight,
        tribonacci_orbit_states_subset_fixed_points_n_eight,
        tribonacci_orbit_states_subset_fixed_points_o_eight⟩

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightFixedB
