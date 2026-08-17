/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationTenFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Eight-block fixed-point decomposition for the period-ten golden enumeration. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationTenData

namespace D5.S0.Tower.GoldenPeriodic.EnumerationTenFixed

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData

def goldenInheritedPointCodesTen : Finset GoldenCodedState :=
  ([1, 2, 5].flatMap goldenFixedPointCodes).toFinset

def goldenNewOrbitStatesTen : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates).toFinset

def goldenExpectedPointCodesTen : Finset GoldenCodedState :=
  goldenInheritedPointCodesTen ∪ goldenNewOrbitStatesTen

def goldenPeriodTenInheritedOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 0 0⟩, [.left], ⟨.large, qphi 0 0⟩⟩

def goldenPeriodTenInheritedOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 1 0⟩, [.right, .through], ⟨.large, qphi 1 0⟩⟩

def goldenPeriodTenInheritedOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (5 / 11) (-2 / 11)⟩,
    [.left, .left, .left, .right, .through],
    ⟨.small, qphi (5 / 11) (-2 / 11)⟩⟩

def goldenPeriodTenInheritedOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (8 / 11) (-1 / 11)⟩,
    [.left, .right, .through, .right, .through],
    ⟨.large, qphi (-1 / 11) (7 / 11)⟩⟩

def goldenPeriodTenInheritedOrbits : List GoldenCodedOrbit :=
  [goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD]

def goldenPeriodicOrbitRepresentativesAtTen : List GoldenCodedOrbit :=
  goldenPeriodTenInheritedOrbits ++ goldenPeriodicOrbitRepresentativesExactlyTen

def goldenOrbitStateFirstThreeSteps (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)) :=
  (goldenOrbitStates orbit).zip
    (orbit.steps.zip ((orbit.steps.rotate 1).zip (orbit.steps.rotate 2)))

def goldenPeriodTenStateFirstThreeSteps :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)) :=
  goldenPeriodicOrbitRepresentativesAtTen.flatMap goldenOrbitStateFirstThreeSteps

@[simp] def goldenStatesForFirstThreeStepsIn
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second third : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2.1 = first ∧ item.2.2.1 = second ∧ item.2.2.2 = third then
      some item.1
    else none).toFinset

def goldenStatesForFirstThreeStepsTen
    (first second third : GoldenPeriodicStep) : Finset GoldenCodedState :=
  goldenStatesForFirstThreeStepsIn goldenPeriodTenStateFirstThreeSteps
    first second third

def goldenThreeStepLegal
    (steps : GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep) :
    Prop :=
  steps = (.left, .left, .left) ∨
  steps = (.left, .left, .right) ∨
  steps = (.left, .right, .through) ∨
  steps = (.right, .through, .left) ∨
  steps = (.right, .through, .right) ∨
  steps = (.through, .left, .left) ∨
  steps = (.through, .left, .right) ∨
  steps = (.through, .right, .through)

theorem golden_orbit_state_first_three_steps_fst (orbit : GoldenCodedOrbit) :
    (goldenOrbitStateFirstThreeSteps orbit).map Prod.fst =
      goldenOrbitStates orbit := by
  rw [goldenOrbitStateFirstThreeSteps, List.map_fst_zip]
  simp [goldenOrbitStates, golden_trace_code_length]

theorem golden_inherited_orbit_states_eq_point_codes_ten :
    (goldenPeriodTenInheritedOrbits.flatMap goldenOrbitStates).toFinset =
      goldenInheritedPointCodesTen := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenInheritedPointCodesTen, goldenOrbitStates, goldenTraceCode,
    goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_period_ten_state_first_three_fst :
    (goldenPeriodTenStateFirstThreeSteps.map Prod.fst).toFinset =
      goldenExpectedPointCodesTen := by
  rw [goldenPeriodTenStateFirstThreeSteps, List.map_flatMap]
  simp_rw [golden_orbit_state_first_three_steps_fst]
  rw [goldenPeriodicOrbitRepresentativesAtTen, List.flatMap_append,
    List.toFinset_append, golden_inherited_orbit_states_eq_point_codes_ten]
  rfl

theorem golden_states_for_first_three_steps_in_subset
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second third : GoldenPeriodicStep) :
    goldenStatesForFirstThreeStepsIn items first second third ⊆
      (items.map Prod.fst).toFinset := by
  intro state hstate
  simp only [goldenStatesForFirstThreeStepsIn, List.mem_toFinset,
    List.mem_filterMap, List.mem_map] at hstate ⊢
  obtain ⟨item, hitem, hselected⟩ := hstate
  split at hselected
  · simp only [Option.some.injEq] at hselected
    exact ⟨item, hitem, hselected⟩
  · contradiction

theorem golden_legal_three_step_partition
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)))
    (hlegal : items.Forall fun item => goldenThreeStepLegal item.2) :
    (items.map Prod.fst).toFinset =
      goldenStatesForFirstThreeStepsIn items .left .left .left ∪
      goldenStatesForFirstThreeStepsIn items .left .left .right ∪
      goldenStatesForFirstThreeStepsIn items .left .right .through ∪
      goldenStatesForFirstThreeStepsIn items .right .through .left ∪
      goldenStatesForFirstThreeStepsIn items .right .through .right ∪
      goldenStatesForFirstThreeStepsIn items .through .left .left ∪
      goldenStatesForFirstThreeStepsIn items .through .left .right ∪
      goldenStatesForFirstThreeStepsIn items .through .right .through := by
  apply Finset.Subset.antisymm
  · intro state hstate
    rw [List.mem_toFinset] at hstate
    simp only [List.mem_map] at hstate
    obtain ⟨item, hitem, rfl⟩ := hstate
    have hitemLegal := List.forall_iff_forall_mem.mp hlegal item hitem
    rcases item with ⟨state, steps⟩
    rcases hitemLegal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hitem]
  · simp only [Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨
      golden_states_for_first_three_steps_in_subset _ _ _ _,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩,
      golden_states_for_first_three_steps_in_subset _ _ _ _⟩

theorem golden_period_ten_first_three_steps_legal :
    goldenPeriodTenStateFirstThreeSteps.Forall fun item =>
      goldenThreeStepLegal item.2 := by
  norm_num [goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenThreeStepLegal]

theorem golden_period_ten_states_partition_by_first_three :
    goldenExpectedPointCodesTen =
      goldenStatesForFirstThreeStepsTen .left .left .left ∪
      goldenStatesForFirstThreeStepsTen .left .left .right ∪
      goldenStatesForFirstThreeStepsTen .left .right .through ∪
      goldenStatesForFirstThreeStepsTen .right .through .left ∪
      goldenStatesForFirstThreeStepsTen .right .through .right ∪
      goldenStatesForFirstThreeStepsTen .through .left .left ∪
      goldenStatesForFirstThreeStepsTen .through .left .right ∪
      goldenStatesForFirstThreeStepsTen .through .right .through := by
  rw [← golden_period_ten_state_first_three_fst]
  exact golden_legal_three_step_partition _
    golden_period_ten_first_three_steps_legal

def goldenFixedPointCodesLargeLLLTen : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .left :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLLRTen : List GoldenCodedState :=
  ((goldenPathsFrom .small 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .left :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLRTTen : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, .left :: .right :: .through :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeRTLTen : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, .right :: .through :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeRTRTen : List GoldenCodedState :=
  ((goldenPathsFrom .small 7).filterMap fun path =>
    if path.2 = .large then
      some (.large, .right :: .through :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTLLTen : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .left :: .left :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTLRTen : List GoldenCodedState :=
  ((goldenPathsFrom .small 7).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .left :: .right :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallTRTTen : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .small then
      some (.small, .through :: .right :: .through :: path.1)
    else none).map fun itinerary =>
      ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

theorem golden_fixed_point_codes_ten_split :
    goldenFixedPointCodes 10 =
      goldenFixedPointCodesLargeLLLTen ++
      goldenFixedPointCodesLargeLLRTen ++
      goldenFixedPointCodesLargeLRTTen ++
      goldenFixedPointCodesLargeRTLTen ++
      goldenFixedPointCodesLargeRTRTen ++
      goldenFixedPointCodesSmallTLLTen ++
      goldenFixedPointCodesSmallTLRTen ++
      goldenFixedPointCodesSmallTRTTen := by
  simp [goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom,
    goldenFixedPointCodesLargeLLLTen, goldenFixedPointCodesLargeLLRTen,
    goldenFixedPointCodesLargeLRTTen, goldenFixedPointCodesLargeRTLTen,
    goldenFixedPointCodesLargeRTRTen, goldenFixedPointCodesSmallTLLTen,
    goldenFixedPointCodesSmallTLRTen, goldenFixedPointCodesSmallTRTTen]

theorem golden_fixed_point_block_counts_ten :
    goldenFixedPointCodesLargeLLLTen.length = 21 ∧
    goldenFixedPointCodesLargeLLRTen.length = 13 ∧
    goldenFixedPointCodesLargeLRTTen.length = 21 ∧
    goldenFixedPointCodesLargeRTLTen.length = 21 ∧
    goldenFixedPointCodesLargeRTRTen.length = 13 ∧
    goldenFixedPointCodesSmallTLLTen.length = 13 ∧
    goldenFixedPointCodesSmallTLRTen.length = 8 ∧
    goldenFixedPointCodesSmallTRTTen.length = 13 := by
  decide

theorem golden_fixed_point_codes_large_lll_ten :
    goldenFixedPointCodesLargeLLLTen.toFinset =
      goldenStatesForFirstThreeStepsTen .left .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLLLTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_llr_ten :
    goldenFixedPointCodesLargeLLRTen.toFinset =
      goldenStatesForFirstThreeStepsTen .left .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLLRTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_lrt_ten :
    goldenFixedPointCodesLargeLRTTen.toFinset =
      goldenStatesForFirstThreeStepsTen .left .right .through := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLRTTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_rtl_ten :
    goldenFixedPointCodesLargeRTLTen.toFinset =
      goldenStatesForFirstThreeStepsTen .right .through .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRTLTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_large_rtr_ten :
    goldenFixedPointCodesLargeRTRTen.toFinset =
      goldenStatesForFirstThreeStepsTen .right .through .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRTRTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_tll_ten :
    goldenFixedPointCodesSmallTLLTen.toFinset =
      goldenStatesForFirstThreeStepsTen .through .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTLLTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_tlr_ten :
    goldenFixedPointCodesSmallTLRTen.toFinset =
      goldenStatesForFirstThreeStepsTen .through .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTLRTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_small_trt_ten :
    goldenFixedPointCodesSmallTRTTen.toFinset =
      goldenStatesForFirstThreeStepsTen .through .right .through := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallTRTTen,
    goldenStatesForFirstThreeStepsTen, goldenPeriodTenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtTen, goldenPeriodTenInheritedOrbits,
    goldenPeriodTenInheritedOrbitA, goldenPeriodTenInheritedOrbitB,
    goldenPeriodTenInheritedOrbitC, goldenPeriodTenInheritedOrbitD,
    goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]
  tauto

theorem golden_fixed_point_codes_ten_decompose :
    (goldenFixedPointCodes 10).toFinset = goldenExpectedPointCodesTen := by
  rw [golden_fixed_point_codes_ten_split]
  simp only [List.toFinset_append]
  rw [golden_fixed_point_codes_large_lll_ten,
    golden_fixed_point_codes_large_llr_ten,
    golden_fixed_point_codes_large_lrt_ten,
    golden_fixed_point_codes_large_rtl_ten,
    golden_fixed_point_codes_large_rtr_ten,
    golden_fixed_point_codes_small_tll_ten,
    golden_fixed_point_codes_small_tlr_ten,
    golden_fixed_point_codes_small_trt_ten,
    golden_period_ten_states_partition_by_first_three]

end D5.S0.Tower.GoldenPeriodic.EnumerationTenFixed
