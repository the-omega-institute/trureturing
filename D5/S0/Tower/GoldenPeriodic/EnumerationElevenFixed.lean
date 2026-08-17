/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationElevenFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Eight-block fixed-point decomposition for the period-eleven golden enumeration. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation

namespace D5.S0.Tower.GoldenPeriodic.EnumerationElevenFixed

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation


theorem golden_paths_from_large_succ (period : Nat) :
    goldenPathsFrom .large (period + 1) =
      (goldenPathsFrom .large period).map
          (fun path => (.left :: path.1, path.2)) ++
        (goldenPathsFrom .small period).map
          (fun path => (.right :: path.1, path.2)) := by
  rfl

theorem golden_paths_from_small_succ (period : Nat) :
    goldenPathsFrom .small (period + 1) =
      (goldenPathsFrom .large period).map
        (fun path => (.through :: path.1, path.2)) := by
  rfl

theorem golden_paths_from_large_eleven_split :
    goldenPathsFrom .large 11 =
      (goldenPathsFrom .large 8).map
          (fun path => (.left :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 8).map
          (fun path => (.left :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 8).map
          (fun path => (.left :: .right :: .through :: path.1, path.2)) ++
      (goldenPathsFrom .large 8).map
          (fun path => (.right :: .through :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 8).map
          (fun path => (.right :: .through :: .right :: path.1, path.2)) := by
  change goldenPathsFrom .large (10 + 1) = _
  rw [golden_paths_from_large_succ 10,
    golden_paths_from_large_succ 9, golden_paths_from_small_succ 9,
    golden_paths_from_large_succ 8, golden_paths_from_small_succ 8]
  simp only [List.map_append, List.map_map, Function.comp_def,
    List.append_assoc]

theorem golden_paths_from_small_eleven_split :
    goldenPathsFrom .small 11 =
      (goldenPathsFrom .large 8).map
          (fun path => (.through :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 8).map
          (fun path => (.through :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 8).map
          (fun path => (.through :: .right :: .through :: path.1, path.2)) := by
  change goldenPathsFrom .small (10 + 1) = _
  rw [golden_paths_from_small_succ 10, golden_paths_from_large_succ 9,
    golden_paths_from_large_succ 8, golden_paths_from_small_succ 8]
  simp only [List.map_append, List.map_map, Function.comp_def,
    List.append_assoc]

def goldenFixedPointCodesLargeLLLEleven : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .left :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLLREleven : List GoldenCodedState :=
  ((goldenPathsFrom .small 8).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .left :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLRTEleven : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .right :: .through :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeRTLEleven : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .large then
      some (.large, .right :: .through :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeRTREleven : List GoldenCodedState :=
  ((goldenPathsFrom .small 8).filterMap fun path =>
    if path.2 = .large then
      some (.large, .right :: .through :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTLLEleven : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .left :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTLREleven : List GoldenCodedState :=
  ((goldenPathsFrom .small 8).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .left :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTRTEleven : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .right :: .through :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeFourStepEleven
    (source : GoldenGapKind) (first second third fourth : GoldenPeriodicStep) :
    List GoldenCodedState :=
  ((goldenPathsFrom source 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, first :: second :: third :: fourth :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLLLLEleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .large .left .left .left .left

def goldenFixedPointCodesLargeLLLREleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .small .left .left .left .right

def goldenFixedPointCodesLargeLRTLEleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .large .left .right .through .left

def goldenFixedPointCodesLargeLRTREleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .small .left .right .through .right

def goldenFixedPointCodesLargeRTLLEleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .large .right .through .left .left

def goldenFixedPointCodesLargeRTLREleven : List GoldenCodedState :=
  goldenFixedPointCodesLargeFourStepEleven .small .right .through .left .right

theorem golden_fixed_point_codes_eleven_split :
    goldenFixedPointCodes 11 =
      goldenFixedPointCodesLargeLLLEleven ++
      goldenFixedPointCodesLargeLLREleven ++
      goldenFixedPointCodesLargeLRTEleven ++
      goldenFixedPointCodesLargeRTLEleven ++
      goldenFixedPointCodesLargeRTREleven ++
      goldenFixedPointCodesSmallTLLEleven ++
      goldenFixedPointCodesSmallTLREleven ++
      goldenFixedPointCodesSmallTRTEleven := by
  rw [goldenFixedPointCodes, goldenClosedItineraries,
    golden_paths_from_large_eleven_split, golden_paths_from_small_eleven_split]
  simp only [List.filterMap_append, List.filterMap_map, List.map_append,
    List.map_filterMap, Function.comp_apply, List.append_assoc]
  simp [List.map_filterMap,
    goldenFixedPointCodesLargeLLLEleven, goldenFixedPointCodesLargeLLREleven,
    goldenFixedPointCodesLargeLRTEleven, goldenFixedPointCodesLargeRTLEleven,
    goldenFixedPointCodesLargeRTREleven, goldenFixedPointCodesSmallTLLEleven,
    goldenFixedPointCodesSmallTLREleven, goldenFixedPointCodesSmallTRTEleven]

theorem golden_fixed_point_codes_large_lll_count_eleven :
    goldenFixedPointCodesLargeLLLEleven.length = 34 := by
  decide

theorem golden_fixed_point_codes_large_llr_count_eleven :
    goldenFixedPointCodesLargeLLREleven.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_lrt_count_eleven :
    goldenFixedPointCodesLargeLRTEleven.length = 34 := by
  decide

theorem golden_fixed_point_codes_large_rtl_count_eleven :
    goldenFixedPointCodesLargeRTLEleven.length = 34 := by
  decide

theorem golden_fixed_point_codes_large_rtr_count_eleven :
    goldenFixedPointCodesLargeRTREleven.length = 21 := by
  decide

theorem golden_fixed_point_codes_small_tll_count_eleven :
    goldenFixedPointCodesSmallTLLEleven.length = 21 := by
  decide

theorem golden_fixed_point_codes_small_tlr_count_eleven :
    goldenFixedPointCodesSmallTLREleven.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_trt_count_eleven :
    goldenFixedPointCodesSmallTRTEleven.length = 21 := by
  decide

theorem golden_fixed_point_block_counts_eleven :
    goldenFixedPointCodesLargeLLLEleven.length = 34 ∧
    goldenFixedPointCodesLargeLLREleven.length = 21 ∧
    goldenFixedPointCodesLargeLRTEleven.length = 34 ∧
    goldenFixedPointCodesLargeRTLEleven.length = 34 ∧
    goldenFixedPointCodesLargeRTREleven.length = 21 ∧
    goldenFixedPointCodesSmallTLLEleven.length = 21 ∧
    goldenFixedPointCodesSmallTLREleven.length = 13 ∧
    goldenFixedPointCodesSmallTRTEleven.length = 21 :=
  ⟨golden_fixed_point_codes_large_lll_count_eleven,
    golden_fixed_point_codes_large_llr_count_eleven,
    golden_fixed_point_codes_large_lrt_count_eleven,
    golden_fixed_point_codes_large_rtl_count_eleven,
    golden_fixed_point_codes_large_rtr_count_eleven,
    golden_fixed_point_codes_small_tll_count_eleven,
    golden_fixed_point_codes_small_tlr_count_eleven,
    golden_fixed_point_codes_small_trt_count_eleven⟩

theorem golden_fixed_point_codes_large_lll_fourth_split_eleven :
    goldenFixedPointCodesLargeLLLEleven =
      goldenFixedPointCodesLargeLLLLEleven ++
        goldenFixedPointCodesLargeLLLREleven := by
  rw [goldenFixedPointCodesLargeLLLEleven, golden_paths_from_large_succ 7]
  simp [goldenFixedPointCodesLargeLLLLEleven,
    goldenFixedPointCodesLargeLLLREleven,
    goldenFixedPointCodesLargeFourStepEleven, List.filterMap_append,
    List.filterMap_map, List.map_append, List.map_filterMap,
    Function.comp_apply]

theorem golden_fixed_point_codes_large_lrt_fourth_split_eleven :
    goldenFixedPointCodesLargeLRTEleven =
      goldenFixedPointCodesLargeLRTLEleven ++
        goldenFixedPointCodesLargeLRTREleven := by
  rw [goldenFixedPointCodesLargeLRTEleven, golden_paths_from_large_succ 7]
  simp [goldenFixedPointCodesLargeLRTLEleven,
    goldenFixedPointCodesLargeLRTREleven,
    goldenFixedPointCodesLargeFourStepEleven, List.filterMap_append,
    List.filterMap_map, List.map_append, List.map_filterMap,
    Function.comp_apply]

theorem golden_fixed_point_codes_large_rtl_fourth_split_eleven :
    goldenFixedPointCodesLargeRTLEleven =
      goldenFixedPointCodesLargeRTLLEleven ++
        goldenFixedPointCodesLargeRTLREleven := by
  rw [goldenFixedPointCodesLargeRTLEleven, golden_paths_from_large_succ 7]
  simp [goldenFixedPointCodesLargeRTLLEleven,
    goldenFixedPointCodesLargeRTLREleven,
    goldenFixedPointCodesLargeFourStepEleven, List.filterMap_append,
    List.filterMap_map, List.map_append, List.map_filterMap,
    Function.comp_apply]

theorem golden_fixed_point_codes_large_llll_eleven :
    goldenFixedPointCodesLargeLLLLEleven.toFinset =
      goldenStatesForFirstFourStepsEleven .left .left .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLLLLEleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_lllr_eleven :
    goldenFixedPointCodesLargeLLLREleven.toFinset =
      goldenStatesForFirstFourStepsEleven .left .left .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLLLREleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_lrtl_eleven :
    goldenFixedPointCodesLargeLRTLEleven.toFinset =
      goldenStatesForFirstFourStepsEleven .left .right .through .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLRTLEleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_lrtr_eleven :
    goldenFixedPointCodesLargeLRTREleven.toFinset =
      goldenStatesForFirstFourStepsEleven .left .right .through .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLRTREleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_rtll_eleven :
    goldenFixedPointCodesLargeRTLLEleven.toFinset =
      goldenStatesForFirstFourStepsEleven .right .through .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRTLLEleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_rtlr_eleven :
    goldenFixedPointCodesLargeRTLREleven.toFinset =
      goldenStatesForFirstFourStepsEleven .right .through .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRTLREleven,
    goldenFixedPointCodesLargeFourStepEleven,
    goldenStatesForFirstFourStepsEleven, goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_lll_eleven :
    goldenFixedPointCodesLargeLLLEleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .left .left .left := by
  rw [golden_fixed_point_codes_large_lll_fourth_split_eleven,
    List.toFinset_append, golden_fixed_point_codes_large_llll_eleven,
    golden_fixed_point_codes_large_lllr_eleven,
    golden_states_for_first_three_steps_lll_split_eleven]

theorem golden_fixed_point_codes_large_lrt_eleven :
    goldenFixedPointCodesLargeLRTEleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .left .right .through := by
  rw [golden_fixed_point_codes_large_lrt_fourth_split_eleven,
    List.toFinset_append, golden_fixed_point_codes_large_lrtl_eleven,
    golden_fixed_point_codes_large_lrtr_eleven,
    golden_states_for_first_three_steps_lrt_split_eleven]

theorem golden_fixed_point_codes_large_rtl_eleven :
    goldenFixedPointCodesLargeRTLEleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .right .through .left := by
  rw [golden_fixed_point_codes_large_rtl_fourth_split_eleven,
    List.toFinset_append, golden_fixed_point_codes_large_rtll_eleven,
    golden_fixed_point_codes_large_rtlr_eleven,
    golden_states_for_first_three_steps_rtl_split_eleven]

theorem golden_fixed_point_codes_large_llr_eleven :
    goldenFixedPointCodesLargeLLREleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .left .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLLREleven,
    goldenStatesForFirstThreeStepsEleven, goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_rtr_eleven :
    goldenFixedPointCodesLargeRTREleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .right .through .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRTREleven,
    goldenStatesForFirstThreeStepsEleven, goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_tll_eleven :
    goldenFixedPointCodesSmallTLLEleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .through .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTLLEleven,
    goldenStatesForFirstThreeStepsEleven, goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_tlr_eleven :
    goldenFixedPointCodesSmallTLREleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .through .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTLREleven,
    goldenStatesForFirstThreeStepsEleven, goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_trt_eleven :
    goldenFixedPointCodesSmallTRTEleven.toFinset =
      goldenStatesForFirstThreeStepsEleven .through .right .through := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTRTEleven,
    goldenStatesForFirstThreeStepsEleven, goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA,
    goldenPeriodicOrbitRepresentativesExactlyEleven, goldenPeriodElevenOrbitA,
    goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
    goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM,
    goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_eleven_decompose :
    (goldenFixedPointCodes 11).toFinset = goldenExpectedPointCodesEleven := by
  rw [golden_fixed_point_codes_eleven_split]
  simp only [List.toFinset_append]
  rw [golden_fixed_point_codes_large_lll_eleven,
    golden_fixed_point_codes_large_llr_eleven,
    golden_fixed_point_codes_large_lrt_eleven,
    golden_fixed_point_codes_large_rtl_eleven,
    golden_fixed_point_codes_large_rtr_eleven,
    golden_fixed_point_codes_small_tll_eleven,
    golden_fixed_point_codes_small_tlr_eleven,
    golden_fixed_point_codes_small_trt_eleven,
    golden_period_eleven_states_partition_by_first_three]

end D5.S0.Tower.GoldenPeriodic.EnumerationElevenFixed
