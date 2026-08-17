/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Twenty-one bounded fixed-equation blocks for exact period twelve. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveSeparation

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveFixed

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenFixed
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveSeparation

theorem golden_paths_from_large_twelve_split :
    goldenPathsFrom .large 12 =
      (goldenPathsFrom .large 7).map
        (fun path => (.left :: .left :: .left :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.left :: .left :: .left :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.left :: .left :: .left :: .right :: .through :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.left :: .left :: .right :: .through :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.left :: .left :: .right :: .through :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.left :: .right :: .through :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.left :: .right :: .through :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.left :: .right :: .through :: .right :: .through :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.right :: .through :: .left :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.right :: .through :: .left :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.right :: .through :: .left :: .right :: .through :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.right :: .through :: .right :: .through :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.right :: .through :: .right :: .through :: .right :: path.1, path.2)) := by
  change goldenPathsFrom .large (11 + 1) = _
  rw [golden_paths_from_large_succ 11,
    golden_paths_from_large_succ 10, golden_paths_from_small_succ 10,
    golden_paths_from_large_succ 9, golden_paths_from_small_succ 9,
    golden_paths_from_large_succ 8, golden_paths_from_small_succ 8,
    golden_paths_from_large_succ 7, golden_paths_from_small_succ 7]
  simp only [List.map_append, List.map_map, Function.comp_def,
    List.append_assoc]

theorem golden_paths_from_small_twelve_split :
    goldenPathsFrom .small 12 =
      (goldenPathsFrom .large 7).map
        (fun path => (.through :: .left :: .left :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.through :: .left :: .left :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.through :: .left :: .left :: .right :: .through :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.through :: .left :: .right :: .through :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.through :: .left :: .right :: .through :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.through :: .right :: .through :: .left :: .left :: path.1, path.2)) ++
      (goldenPathsFrom .small 7).map
        (fun path => (.through :: .right :: .through :: .left :: .right :: path.1, path.2)) ++
      (goldenPathsFrom .large 7).map
        (fun path => (.through :: .right :: .through :: .right :: .through :: path.1, path.2)) := by
  change goldenPathsFrom .small (11 + 1) = _
  rw [golden_paths_from_small_succ 11,
    golden_paths_from_large_succ 10,
    golden_paths_from_large_succ 9, golden_paths_from_small_succ 9,
    golden_paths_from_large_succ 8, golden_paths_from_small_succ 8,
    golden_paths_from_large_succ 7, golden_paths_from_small_succ 7]
  simp only [List.map_append, List.map_map, Function.comp_def,
    List.append_assoc]

def goldenFixedPointCodesBlockTwelve
    (start source : GoldenGapKind) (initialSteps : List GoldenPeriodicStep) :
    List GoldenCodedState :=
  ((goldenPathsFrom source 7).filterMap fun path =>
    if path.2 = start then some (start, initialSteps ++ path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLLLLLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.left, .left, .left, .left, .left]

def goldenFixedPointCodesLargeLLLLRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .small
    [.left, .left, .left, .left, .right]

def goldenFixedPointCodesLargeLLLRTTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.left, .left, .left, .right, .through]

def goldenFixedPointCodesLargeLLRTLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.left, .left, .right, .through, .left]

def goldenFixedPointCodesLargeLLRTRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .small
    [.left, .left, .right, .through, .right]

def goldenFixedPointCodesLargeLRTLLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.left, .right, .through, .left, .left]

def goldenFixedPointCodesLargeLRTLRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .small
    [.left, .right, .through, .left, .right]

def goldenFixedPointCodesLargeLRTRTTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.left, .right, .through, .right, .through]

def goldenFixedPointCodesLargeRTLLLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.right, .through, .left, .left, .left]

def goldenFixedPointCodesLargeRTLLRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .small
    [.right, .through, .left, .left, .right]

def goldenFixedPointCodesLargeRTLRTTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.right, .through, .left, .right, .through]

def goldenFixedPointCodesLargeRTRTLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .large
    [.right, .through, .right, .through, .left]

def goldenFixedPointCodesLargeRTRTRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .large .small
    [.right, .through, .right, .through, .right]

def goldenFixedPointCodesSmallTLLLLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .large
    [.through, .left, .left, .left, .left]

def goldenFixedPointCodesSmallTLLLRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .small
    [.through, .left, .left, .left, .right]

def goldenFixedPointCodesSmallTLLRTTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .large
    [.through, .left, .left, .right, .through]

def goldenFixedPointCodesSmallTLRTLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .large
    [.through, .left, .right, .through, .left]

def goldenFixedPointCodesSmallTLRTRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .small
    [.through, .left, .right, .through, .right]

def goldenFixedPointCodesSmallTRTLLTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .large
    [.through, .right, .through, .left, .left]

def goldenFixedPointCodesSmallTRTLRTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .small
    [.through, .right, .through, .left, .right]

def goldenFixedPointCodesSmallTRTRTTwelve : List GoldenCodedState :=
  goldenFixedPointCodesBlockTwelve .small .large
    [.through, .right, .through, .right, .through]

theorem golden_fixed_point_codes_twelve_split :
    goldenFixedPointCodes 12 =
      goldenFixedPointCodesLargeLLLLLTwelve ++
      goldenFixedPointCodesLargeLLLLRTwelve ++
      goldenFixedPointCodesLargeLLLRTTwelve ++
      goldenFixedPointCodesLargeLLRTLTwelve ++
      goldenFixedPointCodesLargeLLRTRTwelve ++
      goldenFixedPointCodesLargeLRTLLTwelve ++
      goldenFixedPointCodesLargeLRTLRTwelve ++
      goldenFixedPointCodesLargeLRTRTTwelve ++
      goldenFixedPointCodesLargeRTLLLTwelve ++
      goldenFixedPointCodesLargeRTLLRTwelve ++
      goldenFixedPointCodesLargeRTLRTTwelve ++
      goldenFixedPointCodesLargeRTRTLTwelve ++
      goldenFixedPointCodesLargeRTRTRTwelve ++
      goldenFixedPointCodesSmallTLLLLTwelve ++
      goldenFixedPointCodesSmallTLLLRTwelve ++
      goldenFixedPointCodesSmallTLLRTTwelve ++
      goldenFixedPointCodesSmallTLRTLTwelve ++
      goldenFixedPointCodesSmallTLRTRTwelve ++
      goldenFixedPointCodesSmallTRTLLTwelve ++
      goldenFixedPointCodesSmallTRTLRTwelve ++
      goldenFixedPointCodesSmallTRTRTTwelve := by
  rw [goldenFixedPointCodes, goldenClosedItineraries,
    golden_paths_from_large_twelve_split, golden_paths_from_small_twelve_split]
  simp only [List.filterMap_append, List.filterMap_map, List.map_append,
    List.map_filterMap, Function.comp_apply, List.append_assoc]
  simp [List.map_filterMap, goldenFixedPointCodesBlockTwelve,
    goldenFixedPointCodesLargeLLLLLTwelve,
    goldenFixedPointCodesLargeLLLLRTwelve,
    goldenFixedPointCodesLargeLLLRTTwelve,
    goldenFixedPointCodesLargeLLRTLTwelve,
    goldenFixedPointCodesLargeLLRTRTwelve,
    goldenFixedPointCodesLargeLRTLLTwelve,
    goldenFixedPointCodesLargeLRTLRTwelve,
    goldenFixedPointCodesLargeLRTRTTwelve,
    goldenFixedPointCodesLargeRTLLLTwelve,
    goldenFixedPointCodesLargeRTLLRTwelve,
    goldenFixedPointCodesLargeRTLRTTwelve,
    goldenFixedPointCodesLargeRTRTLTwelve,
    goldenFixedPointCodesLargeRTRTRTwelve,
    goldenFixedPointCodesSmallTLLLLTwelve,
    goldenFixedPointCodesSmallTLLLRTwelve,
    goldenFixedPointCodesSmallTLLRTTwelve,
    goldenFixedPointCodesSmallTLRTLTwelve,
    goldenFixedPointCodesSmallTLRTRTwelve,
    goldenFixedPointCodesSmallTRTLLTwelve,
    goldenFixedPointCodesSmallTRTLRTwelve,
    goldenFixedPointCodesSmallTRTRTTwelve]

theorem golden_fixed_point_codes_large_lllll_count_twelve :
    goldenFixedPointCodesLargeLLLLLTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_llllr_count_twelve :
    goldenFixedPointCodesLargeLLLLRTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_large_lllrt_count_twelve :
    goldenFixedPointCodesLargeLLLRTTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_llrtl_count_twelve :
    goldenFixedPointCodesLargeLLRTLTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_llrtr_count_twelve :
    goldenFixedPointCodesLargeLLRTRTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_large_lrtll_count_twelve :
    goldenFixedPointCodesLargeLRTLLTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_lrtlr_count_twelve :
    goldenFixedPointCodesLargeLRTLRTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_large_lrtrt_count_twelve :
    goldenFixedPointCodesLargeLRTRTTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_rtlll_count_twelve :
    goldenFixedPointCodesLargeRTLLLTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_rtllr_count_twelve :
    goldenFixedPointCodesLargeRTLLRTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_large_rtlrt_count_twelve :
    goldenFixedPointCodesLargeRTLRTTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_rtrtl_count_twelve :
    goldenFixedPointCodesLargeRTRTLTwelve.length = 21 := by
  decide

theorem golden_fixed_point_codes_large_rtrtr_count_twelve :
    goldenFixedPointCodesLargeRTRTRTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_tllll_count_twelve :
    goldenFixedPointCodesSmallTLLLLTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_tlllr_count_twelve :
    goldenFixedPointCodesSmallTLLLRTwelve.length = 8 := by
  decide

theorem golden_fixed_point_codes_small_tllrt_count_twelve :
    goldenFixedPointCodesSmallTLLRTTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_tlrtl_count_twelve :
    goldenFixedPointCodesSmallTLRTLTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_tlrtr_count_twelve :
    goldenFixedPointCodesSmallTLRTRTwelve.length = 8 := by
  decide

theorem golden_fixed_point_codes_small_trtll_count_twelve :
    goldenFixedPointCodesSmallTRTLLTwelve.length = 13 := by
  decide

theorem golden_fixed_point_codes_small_trtlr_count_twelve :
    goldenFixedPointCodesSmallTRTLRTwelve.length = 8 := by
  decide

theorem golden_fixed_point_codes_small_trtrt_count_twelve :
    goldenFixedPointCodesSmallTRTRTTwelve.length = 13 := by
  decide

theorem golden_fixed_point_code_count_exactly_twelve :
    (goldenFixedPointCodes 12).length = 322 := by
  rw [golden_fixed_point_codes_twelve_split]
  simp only [List.length_append]
  rw [golden_fixed_point_codes_large_lllll_count_twelve,
    golden_fixed_point_codes_large_llllr_count_twelve,
    golden_fixed_point_codes_large_lllrt_count_twelve,
    golden_fixed_point_codes_large_llrtl_count_twelve,
    golden_fixed_point_codes_large_llrtr_count_twelve,
    golden_fixed_point_codes_large_lrtll_count_twelve,
    golden_fixed_point_codes_large_lrtlr_count_twelve,
    golden_fixed_point_codes_large_lrtrt_count_twelve,
    golden_fixed_point_codes_large_rtlll_count_twelve,
    golden_fixed_point_codes_large_rtllr_count_twelve,
    golden_fixed_point_codes_large_rtlrt_count_twelve,
    golden_fixed_point_codes_large_rtrtl_count_twelve,
    golden_fixed_point_codes_large_rtrtr_count_twelve,
    golden_fixed_point_codes_small_tllll_count_twelve,
    golden_fixed_point_codes_small_tlllr_count_twelve,
    golden_fixed_point_codes_small_tllrt_count_twelve,
    golden_fixed_point_codes_small_tlrtl_count_twelve,
    golden_fixed_point_codes_small_tlrtr_count_twelve,
    golden_fixed_point_codes_small_trtll_count_twelve,
    golden_fixed_point_codes_small_trtlr_count_twelve,
    golden_fixed_point_codes_small_trtrt_count_twelve]

macro "solve_golden_twelve_block" : tactic =>
  `(tactic|
    (apply Finset.ext
     intro code
     simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
       List.filterMap_nil, goldenFixedPointCodesBlockTwelve,
       goldenFixedPointCodesLargeLLLLLTwelve,
       goldenFixedPointCodesLargeLLLLRTwelve,
       goldenFixedPointCodesLargeLLLRTTwelve,
       goldenFixedPointCodesLargeLLRTLTwelve,
       goldenFixedPointCodesLargeLLRTRTwelve,
       goldenFixedPointCodesLargeLRTLLTwelve,
       goldenFixedPointCodesLargeLRTLRTwelve,
       goldenFixedPointCodesLargeLRTRTTwelve,
       goldenFixedPointCodesLargeRTLLLTwelve,
       goldenFixedPointCodesLargeRTLLRTwelve,
       goldenFixedPointCodesLargeRTLRTTwelve,
       goldenFixedPointCodesLargeRTRTLTwelve,
       goldenFixedPointCodesLargeRTRTRTwelve,
       goldenFixedPointCodesSmallTLLLLTwelve,
       goldenFixedPointCodesSmallTLLLRTwelve,
       goldenFixedPointCodesSmallTLLRTTwelve,
       goldenFixedPointCodesSmallTLRTLTwelve,
       goldenFixedPointCodesSmallTLRTRTwelve,
       goldenFixedPointCodesSmallTRTLLTwelve,
       goldenFixedPointCodesSmallTRTLRTwelve,
       goldenFixedPointCodesSmallTRTRTTwelve,
       goldenStatesForFirstFiveStepsTwelve,
       goldenStatesForFirstFiveStepsIn, goldenPeriodTwelveStateFirstFiveSteps,
       goldenPeriodicOrbitRepresentativesAtTwelve,
       goldenPeriodTwelveInheritedOrbits,
       goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
       goldenPeriodicOrbitRepresentativesExactlyTwelve,
       goldenPeriodTwelveOrbitA,
       goldenPeriodTwelveOrbitB,
       goldenPeriodTwelveOrbitC,
       goldenPeriodTwelveOrbitD,
       goldenPeriodTwelveOrbitE,
       goldenPeriodTwelveOrbitF,
       goldenPeriodTwelveOrbitG,
       goldenPeriodTwelveOrbitH,
       goldenPeriodTwelveOrbitI,
       goldenPeriodTwelveOrbitJ,
       goldenPeriodTwelveOrbitK,
       goldenPeriodTwelveOrbitL,
       goldenPeriodTwelveOrbitM,
       goldenPeriodTwelveOrbitN,
       goldenPeriodTwelveOrbitO,
       goldenPeriodTwelveOrbitP,
       goldenPeriodTwelveOrbitQ,
       goldenPeriodTwelveOrbitR,
       goldenPeriodTwelveOrbitS,
       goldenPeriodTwelveOrbitT,
       goldenPeriodTwelveOrbitU,
       goldenPeriodTwelveOrbitV,
       goldenPeriodTwelveOrbitW,
       goldenPeriodTwelveOrbitX,
       goldenPeriodTwelveOrbitY,
       goldenOrbitStateFirstFiveSteps, goldenOrbitStates, goldenTraceCode,
       goldenPathsFrom]
     norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
       goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
       goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
       goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul,
       goldenCodeOne, goldenCodeZero, goldenCodePhi, qphi]
     tauto))

theorem golden_fixed_point_codes_large_lllll_twelve :
    goldenFixedPointCodesLargeLLLLLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .left, .left, .left, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_llllr_twelve :
    goldenFixedPointCodesLargeLLLLRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .left, .left, .left, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_lllrt_twelve :
    goldenFixedPointCodesLargeLLLRTTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .left, .left, .right, .through) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_llrtl_twelve :
    goldenFixedPointCodesLargeLLRTLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .left, .right, .through, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_llrtr_twelve :
    goldenFixedPointCodesLargeLLRTRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .left, .right, .through, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_lrtll_twelve :
    goldenFixedPointCodesLargeLRTLLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .right, .through, .left, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_lrtlr_twelve :
    goldenFixedPointCodesLargeLRTLRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .right, .through, .left, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_lrtrt_twelve :
    goldenFixedPointCodesLargeLRTRTTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.left, .right, .through, .right, .through) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_rtlll_twelve :
    goldenFixedPointCodesLargeRTLLLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.right, .through, .left, .left, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_rtllr_twelve :
    goldenFixedPointCodesLargeRTLLRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.right, .through, .left, .left, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_rtlrt_twelve :
    goldenFixedPointCodesLargeRTLRTTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.right, .through, .left, .right, .through) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_rtrtl_twelve :
    goldenFixedPointCodesLargeRTRTLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.right, .through, .right, .through, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_large_rtrtr_twelve :
    goldenFixedPointCodesLargeRTRTRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.right, .through, .right, .through, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_tllll_twelve :
    goldenFixedPointCodesSmallTLLLLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .left, .left, .left, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_tlllr_twelve :
    goldenFixedPointCodesSmallTLLLRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .left, .left, .left, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_tllrt_twelve :
    goldenFixedPointCodesSmallTLLRTTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .left, .left, .right, .through) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_tlrtl_twelve :
    goldenFixedPointCodesSmallTLRTLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .left, .right, .through, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_tlrtr_twelve :
    goldenFixedPointCodesSmallTLRTRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .left, .right, .through, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_trtll_twelve :
    goldenFixedPointCodesSmallTRTLLTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .right, .through, .left, .left) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_trtlr_twelve :
    goldenFixedPointCodesSmallTRTLRTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .right, .through, .left, .right) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_small_trtrt_twelve :
    goldenFixedPointCodesSmallTRTRTTwelve.toFinset =
      goldenStatesForFirstFiveStepsTwelve (.through, .right, .through, .right, .through) := by
  solve_golden_twelve_block

theorem golden_fixed_point_codes_twelve_decompose :
    (goldenFixedPointCodes 12).toFinset = goldenExpectedPointCodesTwelve := by
  rw [golden_fixed_point_codes_twelve_split]
  simp only [List.toFinset_append]
  rw [golden_fixed_point_codes_large_lllll_twelve,
    golden_fixed_point_codes_large_llllr_twelve,
    golden_fixed_point_codes_large_lllrt_twelve,
    golden_fixed_point_codes_large_llrtl_twelve,
    golden_fixed_point_codes_large_llrtr_twelve,
    golden_fixed_point_codes_large_lrtll_twelve,
    golden_fixed_point_codes_large_lrtlr_twelve,
    golden_fixed_point_codes_large_lrtrt_twelve,
    golden_fixed_point_codes_large_rtlll_twelve,
    golden_fixed_point_codes_large_rtllr_twelve,
    golden_fixed_point_codes_large_rtlrt_twelve,
    golden_fixed_point_codes_large_rtrtl_twelve,
    golden_fixed_point_codes_large_rtrtr_twelve,
    golden_fixed_point_codes_small_tllll_twelve,
    golden_fixed_point_codes_small_tlllr_twelve,
    golden_fixed_point_codes_small_tllrt_twelve,
    golden_fixed_point_codes_small_tlrtl_twelve,
    golden_fixed_point_codes_small_tlrtr_twelve,
    golden_fixed_point_codes_small_trtll_twelve,
    golden_fixed_point_codes_small_trtlr_twelve,
    golden_fixed_point_codes_small_trtrt_twelve]
  rw [golden_period_twelve_states_partition_by_first_five]
  simp [goldenLegalFiveSteps, goldenFiveStepStateUnion]

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveFixed
