/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationNine
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationNine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-nine enumeration for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationNineData

namespace D5.S0.Tower.GoldenPeriodic.EnumerationNine

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData

/- Library-search audit (2026-08-17): the repository has the frozen P <= 8
certificate but no P = 9 extension; no pinned library theorem specializes the
finite-list and rational-arithmetic kernels to this golden transition. -/

def goldenPeriodicOrbitRepresentativesNine : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesEight ++
    goldenPeriodicOrbitRepresentativesExactlyNine

def goldenPeriodicPointCodesNine : Finset GoldenCodedState :=
  goldenPeriodicPointCodesEight ∪ (goldenFixedPointCodes 9).toFinset

theorem golden_fixed_point_code_count_exactly_nine :
    (goldenFixedPointCodes 9).length = 76 := by
  decide

theorem golden_closed_itinerary_denominators_exactly_nine :
    (goldenClosedItineraries 9).Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  simp [List.map_cons, List.map_nil, List.filterMap_nil,
    goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_periodic_point_enumeration_complete_exactly_nine
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[9]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesNine, state = decodeGoldenState code := by
  let steps := goldenActualSteps 9 state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries 9 := by
    exact golden_actual_steps_mem_closed hperiod
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp
      golden_closed_itinerary_denominators_exactly_nine (state.kind, steps) hitinerary
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[9]) state).coordinate :=
        golden_actual_steps_coordinate 9 state
      _ = state.coordinate := congrArg GoldenSurvivorState.coordinate hperiod
  have haffine := golden_path_affine_value steps state.coordinate
  rw [hclosedCoordinate] at haffine
  have hdenValue :
      goldenCodeValue
        (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    golden_code_value_ne_zero_of_norm_ne_zero _ hnorm
  have hcandidate :
      goldenCodeValue (goldenPathCandidateCode steps) = state.coordinate := by
    rw [goldenPathCandidateCode, golden_code_value_div _ _ hnorm]
    apply (div_eq_iff hdenValue).2
    rw [golden_code_value_sub]
    have hone : goldenCodeValue goldenCodeOne = 1 := by
      norm_num [goldenCodeValue, goldenCodeOne]
    rw [hone]
    linear_combination haffine
  let code : GoldenCodedState :=
    ⟨state.kind, goldenPathCandidateCode steps⟩
  have hcode : code ∈ goldenPeriodicPointCodesNine := by
    rw [goldenPeriodicPointCodesNine, Finset.mem_union]
    right
    rw [List.mem_toFinset]
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

theorem golden_periodic_point_enumeration_complete_nine {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 9)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesNine, state = decodeGoldenState code := by
  by_cases hperiodEight : period ≤ 8
  · obtain ⟨code, hcode, hstate⟩ :=
      golden_periodic_point_enumeration_complete_eight
        hperiodPos hperiodEight state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hstate⟩
  · have hperiodNine : period = 9 := by omega
    subst period
    exact golden_periodic_point_enumeration_complete_exactly_nine state hperiod

theorem golden_periodic_orbit_representatives_valid_nine :
    goldenPeriodicOrbitRepresentativesNine.Forall goldenCodedOrbitValid := by
  rw [goldenPeriodicOrbitRepresentativesNine, List.forall_append]
  exact ⟨golden_periodic_orbit_representatives_valid_eight,
    golden_new_periodic_orbit_representatives_valid_nine⟩

def goldenEnumeratedOrbitStatesNine : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates).toFinset

theorem golden_periodic_orbit_state_codes_nodup_nine :
    (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates).Nodup := by
  rw [goldenPeriodicOrbitRepresentativesNine, List.flatMap_append,
    List.nodup_append']
  exact ⟨golden_periodic_orbit_state_codes_nodup_eight,
    golden_new_periodic_orbit_state_codes_nodup_nine,
    golden_old_new_periodic_orbit_state_codes_disjoint_nine⟩

def goldenInheritedPointCodesNine : Finset GoldenCodedState :=
  ([1, 3].flatMap goldenFixedPointCodes).toFinset

def goldenNewOrbitStatesNine : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates).toFinset

def goldenExpectedPointCodesNine : Finset GoldenCodedState :=
  goldenInheritedPointCodesNine ∪ goldenNewOrbitStatesNine

def goldenPeriodNineInheritedOrbit : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 0 0⟩, [.left], ⟨.large, qphi 0 0⟩⟩

def goldenPeriodNineInheritedOrbits : List GoldenCodedOrbit :=
  [goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit]

def goldenPeriodicOrbitRepresentativesAtNine : List GoldenCodedOrbit :=
  goldenPeriodNineInheritedOrbits ++ goldenPeriodicOrbitRepresentativesExactlyNine

def goldenPeriodNineStateSteps : List (GoldenCodedState × GoldenPeriodicStep) :=
  goldenPeriodicOrbitRepresentativesAtNine.flatMap goldenOrbitStateSteps

def goldenStatesForStepNine (step : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (goldenPeriodNineStateSteps.filterMap fun item =>
    if item.2 = step then some item.1 else none).toFinset

theorem golden_inherited_orbit_states_eq_point_codes_nine :
    (goldenPeriodNineInheritedOrbits.flatMap goldenOrbitStates).toFinset =
      goldenInheritedPointCodesNine := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenInheritedPointCodesNine, goldenOrbitStates, goldenTraceCode,
    goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]

theorem golden_period_nine_state_steps_fst :
    (goldenPeriodNineStateSteps.map Prod.fst).toFinset =
      goldenExpectedPointCodesNine := by
  rw [goldenPeriodNineStateSteps, List.map_flatMap]
  simp_rw [golden_orbit_state_steps_fst]
  rw [goldenPeriodicOrbitRepresentativesAtNine, List.flatMap_append,
    List.toFinset_append, golden_inherited_orbit_states_eq_point_codes_nine]
  rfl

theorem golden_period_nine_states_partition_by_step :
    goldenExpectedPointCodesNine =
      goldenStatesForStepNine .left ∪ goldenStatesForStepNine .right ∪
        goldenStatesForStepNine .through := by
  rw [← golden_period_nine_state_steps_fst,
    golden_state_step_partition goldenPeriodNineStateSteps]
  rfl

def goldenFixedPointCodesLargeLeftLeftNine : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .large then some (.large, .left :: .left :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLeftRightNine : List GoldenCodedState :=
  ((goldenPathsFrom .small 7).filterMap fun path =>
    if path.2 = .large then some (.large, .left :: .right :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeLeftNine : List GoldenCodedState :=
  goldenFixedPointCodesLargeLeftLeftNine ++ goldenFixedPointCodesLargeLeftRightNine

def goldenFixedPointCodesLargeRightNine : List GoldenCodedState :=
  ((goldenPathsFrom .small 8).filterMap fun path =>
    if path.2 = .large then some (.large, .right :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallThroughNine : List GoldenCodedState :=
  ((goldenPathsFrom .large 8).filterMap fun path =>
    if path.2 = .small then some (.small, .through :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

theorem golden_fixed_point_codes_nine_split :
    goldenFixedPointCodes 9 = goldenFixedPointCodesLargeLeftNine ++
      goldenFixedPointCodesLargeRightNine ++ goldenFixedPointCodesSmallThroughNine := by
  simp [goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom,
    goldenFixedPointCodesLargeLeftNine, goldenFixedPointCodesLargeLeftLeftNine,
    goldenFixedPointCodesLargeLeftRightNine, goldenFixedPointCodesLargeRightNine,
    goldenFixedPointCodesSmallThroughNine]

def goldenOrbitStateFirstTwoSteps
    (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState × (GoldenPeriodicStep × GoldenPeriodicStep)) :=
  (goldenOrbitStates orbit).zip (orbit.steps.zip (orbit.steps.rotate 1))

def goldenPeriodNineStateFirstTwoSteps :
    List (GoldenCodedState × (GoldenPeriodicStep × GoldenPeriodicStep)) :=
  goldenPeriodicOrbitRepresentativesAtNine.flatMap goldenOrbitStateFirstTwoSteps

def goldenStatesForFirstStepIn
    (items : List (GoldenCodedState × (GoldenPeriodicStep × GoldenPeriodicStep)))
    (first : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2.1 = first then some item.1 else none).toFinset

def goldenStatesForFirstTwoStepsIn
    (items : List (GoldenCodedState × (GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2.1 = first ∧ item.2.2 = second then some item.1 else none).toFinset

def goldenStatesForFirstTwoStepsNine
    (first second : GoldenPeriodicStep) : Finset GoldenCodedState :=
  goldenStatesForFirstTwoStepsIn goldenPeriodNineStateFirstTwoSteps first second

theorem golden_first_step_partition_by_second
    (items : List (GoldenCodedState × (GoldenPeriodicStep × GoldenPeriodicStep)))
    (first : GoldenPeriodicStep) :
    goldenStatesForFirstStepIn items first =
      goldenStatesForFirstTwoStepsIn items first .left ∪
        goldenStatesForFirstTwoStepsIn items first .right ∪
          goldenStatesForFirstTwoStepsIn items first .through := by
  induction items with
  | nil => simp [goldenStatesForFirstStepIn, goldenStatesForFirstTwoStepsIn]
  | cons item rest ih =>
      rcases item with ⟨state, ⟨itemFirst, itemSecond⟩⟩
      cases first <;> cases itemFirst <;> cases itemSecond <;>
        simp only [goldenStatesForFirstStepIn,
          goldenStatesForFirstTwoStepsIn] at ih ⊢ <;>
        simp [ih, Finset.union_assoc]

theorem golden_states_for_left_step_as_first_two_nine :
    goldenStatesForStepNine .left =
      goldenStatesForFirstStepIn goldenPeriodNineStateFirstTwoSteps .left := by
  apply Finset.ext
  intro code
  simp [goldenStatesForStepNine, goldenStatesForFirstStepIn,
    goldenPeriodNineStateSteps, goldenPeriodNineStateFirstTwoSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateSteps,
    goldenOrbitStateFirstTwoSteps, goldenOrbitStates, goldenTraceCode]

theorem golden_states_for_left_through_steps_empty_nine :
    goldenStatesForFirstTwoStepsNine .left .through = ∅ := by
  apply Finset.ext
  intro code
  simp [goldenStatesForFirstTwoStepsNine, goldenStatesForFirstTwoStepsIn,
    goldenPeriodNineStateFirstTwoSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateFirstTwoSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_states_for_left_step_split_nine :
    goldenStatesForStepNine .left =
      goldenStatesForFirstTwoStepsNine .left .left ∪
        goldenStatesForFirstTwoStepsNine .left .right := by
  rw [golden_states_for_left_step_as_first_two_nine,
    golden_first_step_partition_by_second]
  change goldenStatesForFirstTwoStepsNine .left .left ∪
      goldenStatesForFirstTwoStepsNine .left .right ∪
        goldenStatesForFirstTwoStepsNine .left .through =
    goldenStatesForFirstTwoStepsNine .left .left ∪
      goldenStatesForFirstTwoStepsNine .left .right
  rw [golden_states_for_left_through_steps_empty_nine, Finset.union_empty]

theorem golden_fixed_point_codes_large_left_left_nine :
    goldenFixedPointCodesLargeLeftLeftNine.toFinset =
      goldenStatesForFirstTwoStepsNine .left .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLeftLeftNine,
    goldenStatesForFirstTwoStepsNine, goldenStatesForFirstTwoStepsIn,
    goldenPeriodNineStateFirstTwoSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateFirstTwoSteps, goldenOrbitStates,
    goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_large_left_right_nine :
    goldenFixedPointCodesLargeLeftRightNine.toFinset =
      goldenStatesForFirstTwoStepsNine .left .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLeftRightNine,
    goldenStatesForFirstTwoStepsNine, goldenStatesForFirstTwoStepsIn,
    goldenPeriodNineStateFirstTwoSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateFirstTwoSteps, goldenOrbitStates,
    goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_large_left_nine :
    goldenFixedPointCodesLargeLeftNine.toFinset = goldenStatesForStepNine .left := by
  rw [goldenFixedPointCodesLargeLeftNine, List.toFinset_append,
    golden_fixed_point_codes_large_left_left_nine,
    golden_fixed_point_codes_large_left_right_nine,
    golden_states_for_left_step_split_nine]

theorem golden_fixed_point_codes_large_right_nine :
    goldenFixedPointCodesLargeRightNine.toFinset = goldenStatesForStepNine .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRightNine,
    goldenStatesForStepNine, goldenPeriodNineStateSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateSteps, goldenOrbitStates,
    goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_small_through_nine :
    goldenFixedPointCodesSmallThroughNine.toFinset =
      goldenStatesForStepNine .through := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallThroughNine,
    goldenStatesForStepNine, goldenPeriodNineStateSteps,
    goldenPeriodicOrbitRepresentativesAtNine, goldenPeriodNineInheritedOrbits,
    goldenPeriodNineInheritedOrbit, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
    goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
    goldenPeriodNineOrbitH, goldenOrbitStateSteps, goldenOrbitStates,
    goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_nine_decompose :
    (goldenFixedPointCodes 9).toFinset =
      goldenInheritedPointCodesNine ∪ goldenNewOrbitStatesNine := by
  rw [golden_fixed_point_codes_nine_split, List.toFinset_append,
    List.toFinset_append, golden_fixed_point_codes_large_left_nine,
    golden_fixed_point_codes_large_right_nine,
    golden_fixed_point_codes_small_through_nine,
    ← golden_period_nine_states_partition_by_step]
  rfl

theorem golden_inherited_point_codes_nine_subset_seven :
    goldenInheritedPointCodesNine ⊆ goldenPeriodicPointCodesSeven := by
  intro code hcode
  simp only [goldenInheritedPointCodesNine, List.mem_toFinset,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcode
  obtain ⟨period, hperiod, hcode⟩ := hcode
  rw [goldenPeriodicPointCodesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap]
  rcases hperiod with rfl | rfl
  · exact ⟨0, List.mem_range.mpr (by omega), by simpa using hcode⟩
  · exact ⟨2, List.mem_range.mpr (by omega), by simpa using hcode⟩

theorem golden_inherited_point_codes_nine_subset_eight :
    goldenInheritedPointCodesNine ⊆ goldenPeriodicPointCodesEight := by
  intro code hcode
  rw [goldenPeriodicPointCodesEight, Finset.mem_union]
  exact Or.inl (golden_inherited_point_codes_nine_subset_seven hcode)

theorem golden_prior_union_fixed_points_nine :
    goldenPeriodicPointCodesEight ∪ (goldenFixedPointCodes 9).toFinset =
      goldenPeriodicPointCodesEight ∪ goldenNewOrbitStatesNine := by
  rw [golden_fixed_point_codes_nine_decompose]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (golden_inherited_point_codes_nine_subset_eight hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

theorem golden_enumerated_orbit_states_eq_fixed_points_nine :
    goldenEnumeratedOrbitStatesNine = goldenPeriodicPointCodesNine := by
  rw [goldenEnumeratedOrbitStatesNine, goldenPeriodicOrbitRepresentativesNine,
    List.flatMap_append, List.toFinset_append]
  change goldenEnumeratedOrbitStatesEight ∪ goldenNewOrbitStatesNine =
    goldenPeriodicPointCodesNine
  rw [golden_enumerated_orbit_states_eq_fixed_points_eight,
    goldenPeriodicPointCodesNine]
  exact golden_prior_union_fixed_points_nine.symm

theorem golden_periodic_point_code_count_nine :
    goldenPeriodicPointCodesNine.card = 172 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points_nine,
    goldenEnumeratedOrbitStatesNine,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup_nine]
  rw [goldenPeriodicOrbitRepresentativesNine, List.flatMap_append,
    List.length_append]
  have hold :
      (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates).length =
        100 := by
    rw [← List.toFinset_card_of_nodup
      golden_periodic_orbit_state_codes_nodup_eight]
    exact golden_periodic_code_partition_eight.2
  have hnew :
      (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap
        goldenOrbitStates).length = 72 := by
    norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenOrbitStates,
    goldenTraceCode]
  omega

theorem golden_periodic_code_partition_nine :
    goldenPeriodicOrbitRepresentativesNine.length = 25 ∧
      goldenEnumeratedOrbitStatesNine.card = 172 := by
  constructor
  · norm_num [goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven,
      goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodicOrbitRepresentativesExactlyNine]
  · rw [golden_enumerated_orbit_states_eq_fixed_points_nine]
    exact golden_periodic_point_code_count_nine

theorem golden_periodic_orbit_enumeration_complete_nine {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 9)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesNine,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete_nine
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesNine := by
    rw [golden_enumerated_orbit_states_eq_fixed_points_nine]
    exact hcode
  rw [goldenEnumeratedOrbitStatesNine, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem golden_periodic_orbit_low_states_mem_nine :
    goldenPeriodicOrbitRepresentativesNine.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  rw [goldenPeriodicOrbitRepresentativesNine, List.forall_append]
  exact ⟨golden_periodic_orbit_low_states_mem_eight,
    golden_new_periodic_orbit_low_states_mem_nine⟩

theorem golden_periodic_orbit_low_arms_bounded_nine :
    goldenPeriodicOrbitRepresentativesNine.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  rw [goldenPeriodicOrbitRepresentativesNine, List.forall_append]
  exact ⟨golden_periodic_orbit_low_arms_bounded_eight,
    golden_new_periodic_orbit_low_arms_bounded_nine⟩

def goldenPeriodicOrbitMinimaNine : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesNine,
    GoldenOrbitMinimum orbit value}

theorem golden_periodic_orbit_minimum_exists_nine (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesNine) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp
    golden_periodic_orbit_low_states_mem_nine orbit horbit
  have hstates : (goldenOrbitStates orbit).toFinset.Nonempty :=
    ⟨orbit.lowState, List.mem_toFinset.mpr hcode⟩
  obtain ⟨code, hstate, hleast⟩ :=
    Finset.exists_min_image (goldenOrbitStates orbit).toFinset
      (fun item => goldenStateArm (decodeGoldenState item)) hstates
  refine ⟨goldenStateArm (decodeGoldenState code), ⟨?_,
    decodeGoldenState code, ?_, rfl⟩⟩
  · intro other hother
    rw [goldenDecodedOrbitStates, List.mem_map] at hother
    obtain ⟨otherCode, hotherCode, rfl⟩ := hother
    exact hleast otherCode (List.mem_toFinset.mpr hotherCode)
  · rw [goldenDecodedOrbitStates, List.mem_map]
    exact ⟨code, List.mem_toFinset.mp hstate, rfl⟩

theorem golden_periodic_orbit_maximin_nine :
    IsGreatest goldenPeriodicOrbitMinimaNine goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem_nine orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded_nine orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.GoldenPeriodic.EnumerationNine
