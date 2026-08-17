/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationEight
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-eight enumeration for the golden survivor map. -/

import D5.S0.Tower.Champions.GoldenPeriodicEnumeration

namespace D5.S0.Tower.GoldenPeriodic.EnumerationEight

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen complete enumeration through period
     seven and its exact quadratic generator, but no period-eight extension.
   * Pinned mathlib supplies the finite-list and rational-arithmetic kernels;
     no library theorem specializes them to this golden transition.
   * This module extends the frozen certificate by one period only. -/

def goldenPeriodEightOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 15) (-4 / 15)⟩,
    [.left, .left, .left, .left, .left, .left, .right, .through],
    ⟨.large, qphi (7 / 15) (-4 / 15)⟩⟩

def goldenPeriodEightOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (2 / 3) (-1 / 3)⟩,
    [.left, .left, .left, .left, .right, .through, .right, .through],
    ⟨.large, qphi (2 / 3) (-1 / 3)⟩⟩

def goldenPeriodEightOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (2 / 5) (-2 / 15)⟩,
    [.left, .left, .left, .right, .through, .left, .right, .through],
    ⟨.large, qphi (2 / 5) (-2 / 15)⟩⟩

def goldenPeriodEightOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (4 / 5) (-4 / 15)⟩,
    [.left, .left, .right, .through, .right, .through, .right, .through],
    ⟨.large, qphi (8 / 15) (4 / 15)⟩⟩

def goldenPeriodEightOrbitE : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (11 / 15) (-2 / 15)⟩,
    [.left, .right, .through, .left, .right, .through, .right, .through],
    ⟨.large, qphi (-2 / 15) (3 / 5)⟩⟩

/-- The five new primitive period-eight cycles. -/
def goldenPeriodicOrbitRepresentativesExactlyEight : List GoldenCodedOrbit :=
  [goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE]

/-- The frozen twelve cycles followed by the five new period-eight cycles. -/
def goldenPeriodicOrbitRepresentativesEight : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesSeven ++
    goldenPeriodicOrbitRepresentativesExactlyEight

/-- Point codes from the frozen range together with all period-eight equations. -/
def goldenPeriodicPointCodesEight : Finset GoldenCodedState :=
  goldenPeriodicPointCodesSeven ∪ (goldenFixedPointCodes 8).toFinset

/-- The period-eight symbolic generator has forty-seven closed equations. -/
theorem golden_fixed_point_code_count_exactly_eight :
    (goldenFixedPointCodes 8).length = 47 := by
  decide

/-- Five primitive cycles are added at period eight. -/
theorem golden_new_periodic_orbit_count_eight :
    goldenPeriodicOrbitRepresentativesExactlyEight.length = 5 := by
  rfl

/-- Every newly displayed cycle has period-eight word length. -/
theorem golden_new_periodic_orbit_lengths_eight :
    goldenPeriodicOrbitRepresentativesExactlyEight.map
      (fun orbit => orbit.steps.length) = [8, 8, 8, 8, 8] := by
  rfl

/-- Every period-eight affine fixed-point equation has a nonzero denominator. -/
theorem golden_closed_itinerary_denominators_exactly_eight :
    (goldenClosedItineraries 8).Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  simp [List.map_cons, List.map_nil, List.filterMap_nil,
    goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

/-- Point-level completeness for the newly added exact period. -/
theorem golden_periodic_point_enumeration_complete_exactly_eight
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[8]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesEight, state = decodeGoldenState code := by
  let steps := goldenActualSteps 8 state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries 8 := by
    exact golden_actual_steps_mem_closed hperiod
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp
      golden_closed_itinerary_denominators_exactly_eight (state.kind, steps) hitinerary
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[8]) state).coordinate :=
        golden_actual_steps_coordinate 8 state
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
  have hcode : code ∈ goldenPeriodicPointCodesEight := by
    rw [goldenPeriodicPointCodesEight, Finset.mem_union]
    right
    rw [List.mem_toFinset]
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

/-- Every real state fixed by a nonzero iterate of period at most eight occurs
in the incremental exact quadratic point enumeration. -/
theorem golden_periodic_point_enumeration_complete_eight {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 8)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesEight, state = decodeGoldenState code := by
  by_cases hperiodSeven : period ≤ 7
  · obtain ⟨code, hcode, hstate⟩ :=
      golden_periodic_point_enumeration_complete hperiodPos hperiodSeven state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hstate⟩
  · have hperiodEight : period = 8 := by omega
    subst period
    exact golden_periodic_point_enumeration_complete_exactly_eight state hperiod

/-- The five new code cycles close and have no repeated phase state. -/
theorem golden_new_periodic_orbit_codes_close_and_are_nodup :
    goldenPeriodicOrbitRepresentativesExactlyEight.Forall fun orbit =>
      goldenApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (goldenOrbitStates orbit).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenApplyStepsCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenOrbitStates, goldenTraceCode, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

/-- Each selected low code occurs on its new period-eight cycle. -/
theorem golden_new_periodic_orbit_low_states_mem :
    goldenPeriodicOrbitRepresentativesExactlyEight.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_eight_orbit_a_valid :
    goldenCodedOrbitValid goldenPeriodEightOrbitA := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodEightOrbitA, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eight_orbit_b_valid :
    goldenCodedOrbitValid goldenPeriodEightOrbitB := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodEightOrbitB, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eight_orbit_c_valid :
    goldenCodedOrbitValid goldenPeriodEightOrbitC := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodEightOrbitC, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eight_orbit_d_valid :
    goldenCodedOrbitValid goldenPeriodEightOrbitD := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodEightOrbitD, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eight_orbit_e_valid :
    goldenCodedOrbitValid goldenPeriodEightOrbitE := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodEightOrbitE, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

/-- Every new code follows the certified real branches and stays in the closed
unit chart. -/
theorem golden_new_periodic_orbit_representatives_valid :
    goldenPeriodicOrbitRepresentativesExactlyEight.Forall goldenCodedOrbitValid := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyEight, List.forall_cons]
  exact ⟨golden_period_eight_orbit_a_valid, golden_period_eight_orbit_b_valid,
    golden_period_eight_orbit_c_valid, golden_period_eight_orbit_d_valid,
    golden_period_eight_orbit_e_valid, by simp⟩

/-- All seventeen displayed cycles are valid real golden survivor cycles. -/
theorem golden_periodic_orbit_representatives_valid_eight :
    goldenPeriodicOrbitRepresentativesEight.Forall goldenCodedOrbitValid := by
  rw [goldenPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨golden_periodic_orbit_representatives_valid,
    golden_new_periodic_orbit_representatives_valid⟩

def goldenEnumeratedOrbitStatesEight : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates).toFinset

/-- The seventeen cycle lists are pairwise disjoint and internally
duplicate-free. -/
theorem golden_new_periodic_orbit_state_codes_nodup_eight :
    (goldenPeriodicOrbitRepresentativesExactlyEight.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_old_new_periodic_orbit_state_codes_disjoint_eight :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesSeven.flatMap goldenOrbitStates)
      (goldenPeriodicOrbitRepresentativesExactlyEight.flatMap goldenOrbitStates) := by
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_periodic_orbit_state_codes_nodup_eight :
    (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates).Nodup := by
  rw [goldenPeriodicOrbitRepresentativesEight, List.flatMap_append,
    List.nodup_append']
  exact ⟨golden_periodic_orbit_state_codes_nodup,
    golden_new_periodic_orbit_state_codes_nodup_eight,
    golden_old_new_periodic_orbit_state_codes_disjoint_eight⟩

def goldenInheritedPointCodesEight : Finset GoldenCodedState :=
  ([1, 2, 4].flatMap goldenFixedPointCodes).toFinset

def goldenNewOrbitStatesEight : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesExactlyEight.flatMap
    goldenOrbitStates).toFinset

def goldenExpectedPointCodesEight : Finset GoldenCodedState :=
  goldenInheritedPointCodesEight ∪ goldenNewOrbitStatesEight

def goldenPeriodEightInheritedOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 0 0⟩, [.left], ⟨.large, qphi 0 0⟩⟩

def goldenPeriodEightInheritedOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 1 0⟩, [.right, .through], ⟨.large, qphi 1 0⟩⟩

def goldenPeriodEightInheritedOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (3 / 5) (-1 / 5)⟩,
    [.left, .left, .right, .through],
    ⟨.small, qphi (3 / 5) (-1 / 5)⟩⟩

def goldenPeriodEightInheritedOrbits : List GoldenCodedOrbit :=
  [goldenPeriodEightInheritedOrbitA, goldenPeriodEightInheritedOrbitB,
    goldenPeriodEightInheritedOrbitC]

def goldenPeriodicOrbitRepresentativesAtEight : List GoldenCodedOrbit :=
  goldenPeriodEightInheritedOrbits ++ goldenPeriodicOrbitRepresentativesExactlyEight

def goldenOrbitStateSteps (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState × GoldenPeriodicStep) :=
  (goldenOrbitStates orbit).zip orbit.steps

def goldenPeriodEightStateSteps : List (GoldenCodedState × GoldenPeriodicStep) :=
  goldenPeriodicOrbitRepresentativesAtEight.flatMap goldenOrbitStateSteps

def goldenStatesForStepEight (step : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (goldenPeriodEightStateSteps.filterMap fun item =>
    if item.2 = step then some item.1 else none).toFinset

theorem golden_trace_code_length (state : GoldenCodedState)
    (steps : List GoldenPeriodicStep) :
    (goldenTraceCode state steps).length = steps.length := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
      simp [goldenTraceCode, ih]

theorem golden_orbit_state_steps_fst (orbit : GoldenCodedOrbit) :
    (goldenOrbitStateSteps orbit).map Prod.fst = goldenOrbitStates orbit := by
  rw [goldenOrbitStateSteps, List.map_fst_zip]
  rw [goldenOrbitStates, golden_trace_code_length]

theorem golden_inherited_orbit_states_eq_point_codes_eight :
    (goldenPeriodEightInheritedOrbits.flatMap goldenOrbitStates).toFinset =
      goldenInheritedPointCodesEight := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenPeriodEightInheritedOrbits,
    goldenPeriodEightInheritedOrbitA, goldenPeriodEightInheritedOrbitB,
    goldenPeriodEightInheritedOrbitC, goldenInheritedPointCodesEight,
    goldenOrbitStates, goldenTraceCode, goldenFixedPointCodes,
    goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_period_eight_state_steps_fst :
    (goldenPeriodEightStateSteps.map Prod.fst).toFinset =
      goldenExpectedPointCodesEight := by
  rw [goldenPeriodEightStateSteps, List.map_flatMap]
  simp_rw [golden_orbit_state_steps_fst]
  rw [goldenPeriodicOrbitRepresentativesAtEight, List.flatMap_append,
    List.toFinset_append, golden_inherited_orbit_states_eq_point_codes_eight]
  rfl

theorem golden_state_step_partition (items : List (GoldenCodedState × GoldenPeriodicStep)) :
    (items.map Prod.fst).toFinset =
      (items.filterMap fun item =>
        if item.2 = .left then some item.1 else none).toFinset ∪
      (items.filterMap fun item =>
        if item.2 = .right then some item.1 else none).toFinset ∪
      (items.filterMap fun item =>
        if item.2 = .through then some item.1 else none).toFinset := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      cases item with
      | mk state step =>
          cases step <;>
            simp [ih, Finset.union_assoc]

theorem golden_period_eight_states_partition_by_step :
    goldenExpectedPointCodesEight =
      goldenStatesForStepEight .left ∪ goldenStatesForStepEight .right ∪
        goldenStatesForStepEight .through := by
  rw [← golden_period_eight_state_steps_fst,
    golden_state_step_partition goldenPeriodEightStateSteps]
  rfl

def goldenFixedPointCodesLargeLeftEight : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .large then some (.large, .left :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesLargeRightEight : List GoldenCodedState :=
  ((goldenPathsFrom .small 7).filterMap fun path =>
    if path.2 = .large then some (.large, .right :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

def goldenFixedPointCodesSmallThroughEight : List GoldenCodedState :=
  ((goldenPathsFrom .large 7).filterMap fun path =>
    if path.2 = .small then some (.small, .through :: path.1) else none).map
      fun itinerary => ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

theorem golden_fixed_point_codes_eight_split :
    goldenFixedPointCodes 8 = goldenFixedPointCodesLargeLeftEight ++
      goldenFixedPointCodesLargeRightEight ++ goldenFixedPointCodesSmallThroughEight := by
  simp [goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom,
    goldenFixedPointCodesLargeLeftEight, goldenFixedPointCodesLargeRightEight,
    goldenFixedPointCodesSmallThroughEight]

theorem golden_fixed_point_codes_large_left_eight :
    goldenFixedPointCodesLargeLeftEight.toFinset = goldenStatesForStepEight .left := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeLeftEight,
    goldenStatesForStepEight, goldenPeriodEightStateSteps,
    goldenPeriodicOrbitRepresentativesAtEight, goldenPeriodEightInheritedOrbits,
    goldenPeriodEightInheritedOrbitA, goldenPeriodEightInheritedOrbitB,
    goldenPeriodEightInheritedOrbitC, goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenOrbitStateSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_large_right_eight :
    goldenFixedPointCodesLargeRightEight.toFinset = goldenStatesForStepEight .right := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesLargeRightEight,
    goldenStatesForStepEight, goldenPeriodEightStateSteps,
    goldenPeriodicOrbitRepresentativesAtEight, goldenPeriodEightInheritedOrbits,
    goldenPeriodEightInheritedOrbitA, goldenPeriodEightInheritedOrbitB,
    goldenPeriodEightInheritedOrbitC, goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenOrbitStateSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

theorem golden_fixed_point_codes_small_through_eight :
    goldenFixedPointCodesSmallThroughEight.toFinset =
      goldenStatesForStepEight .through := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenFixedPointCodesSmallThroughEight,
    goldenStatesForStepEight, goldenPeriodEightStateSteps,
    goldenPeriodicOrbitRepresentativesAtEight, goldenPeriodEightInheritedOrbits,
    goldenPeriodEightInheritedOrbitA, goldenPeriodEightInheritedOrbitB,
    goldenPeriodEightInheritedOrbitC, goldenPeriodicOrbitRepresentativesExactlyEight,
    goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
    goldenPeriodEightOrbitD, goldenPeriodEightOrbitE, goldenOrbitStateSteps,
    goldenOrbitStates, goldenTraceCode, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]; tauto

/-- Period-eight fixed-point equations consist of the periods dividing eight
and forty new phase states. -/
theorem golden_fixed_point_codes_eight_decompose :
    (goldenFixedPointCodes 8).toFinset =
      goldenInheritedPointCodesEight ∪ goldenNewOrbitStatesEight := by
  rw [golden_fixed_point_codes_eight_split, List.toFinset_append,
    List.toFinset_append, golden_fixed_point_codes_large_left_eight,
    golden_fixed_point_codes_large_right_eight,
    golden_fixed_point_codes_small_through_eight,
    ← golden_period_eight_states_partition_by_step]
  rfl

theorem golden_inherited_point_codes_eight_subset_seven :
    goldenInheritedPointCodesEight ⊆ goldenPeriodicPointCodesSeven := by
  intro code hcode
  simp only [goldenInheritedPointCodesEight, List.mem_toFinset,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcode
  obtain ⟨period, hperiod, hcode⟩ := hcode
  rw [goldenPeriodicPointCodesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap]
  rcases hperiod with rfl | rfl | rfl
  · exact ⟨0, List.mem_range.mpr (by omega), by simpa using hcode⟩
  · exact ⟨1, List.mem_range.mpr (by omega), by simpa using hcode⟩
  · exact ⟨3, List.mem_range.mpr (by omega), by simpa using hcode⟩

theorem golden_prior_union_fixed_points_eight :
    goldenPeriodicPointCodesSeven ∪ (goldenFixedPointCodes 8).toFinset =
      goldenPeriodicPointCodesSeven ∪ goldenNewOrbitStatesEight := by
  rw [golden_fixed_point_codes_eight_decompose]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (golden_inherited_point_codes_eight_subset_seven hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

/-- The incremental symbolic generator and the seventeen explicit cycles give
the same finite set. -/
theorem golden_enumerated_orbit_states_eq_fixed_points_eight :
    goldenEnumeratedOrbitStatesEight = goldenPeriodicPointCodesEight := by
  rw [goldenEnumeratedOrbitStatesEight, goldenPeriodicOrbitRepresentativesEight,
    List.flatMap_append, List.toFinset_append]
  change goldenEnumeratedOrbitStatesSeven ∪ goldenNewOrbitStatesEight =
    goldenPeriodicPointCodesEight
  rw [golden_enumerated_orbit_states_eq_fixed_points, goldenPeriodicPointCodesEight]
  exact golden_prior_union_fixed_points_eight.symm

/-- Deduplication through period eight gives one hundred periodic states. -/
theorem golden_periodic_point_code_count_eight :
    goldenPeriodicPointCodesEight.card = 100 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points_eight,
    goldenEnumeratedOrbitStatesEight,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup_eight]
  norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenOrbitStates, goldenTraceCode]

/-- The one hundred states partition into seventeen displayed cycles. -/
theorem golden_periodic_code_partition_eight :
    goldenPeriodicOrbitRepresentativesEight.length = 17 ∧
      goldenEnumeratedOrbitStatesEight.card = 100 := by
  constructor
  · norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven,
      goldenPeriodicOrbitRepresentativesExactlyEight]
  · rw [golden_enumerated_orbit_states_eq_fixed_points_eight]
    exact golden_periodic_point_code_count_eight

/-- Orbit-level completeness through period eight. -/
theorem golden_periodic_orbit_enumeration_complete_eight {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 8)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesEight,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete_eight
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesEight := by
    rw [golden_enumerated_orbit_states_eq_fixed_points_eight]
    exact hcode
  rw [goldenEnumeratedOrbitStatesEight, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem golden_period_eight_orbit_a_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodEightOrbitA.lowState) ≤
      goldenThreshold := by
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodEightOrbitA, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_period_eight_orbit_b_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodEightOrbitB.lowState) ≤
      goldenThreshold := by
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodEightOrbitB, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_period_eight_orbit_c_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodEightOrbitC.lowState) ≤
      goldenThreshold := by
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodEightOrbitC, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_period_eight_orbit_d_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodEightOrbitD.lowState) ≤
      goldenThreshold := by
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodEightOrbitD, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_period_eight_orbit_e_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodEightOrbitE.lowState) ≤
      goldenThreshold := by
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodEightOrbitE, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_new_periodic_orbit_low_arms_bounded_eight :
    goldenPeriodicOrbitRepresentativesExactlyEight.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyEight, List.forall_cons]
  exact ⟨golden_period_eight_orbit_a_low_arm, golden_period_eight_orbit_b_low_arm,
    golden_period_eight_orbit_c_low_arm, golden_period_eight_orbit_d_low_arm,
    golden_period_eight_orbit_e_low_arm, by simp⟩

theorem golden_periodic_orbit_low_states_mem_eight :
    goldenPeriodicOrbitRepresentativesEight.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  rw [goldenPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨golden_periodic_orbit_low_states_mem,
    golden_new_periodic_orbit_low_states_mem⟩

theorem golden_periodic_orbit_low_arms_bounded_eight :
    goldenPeriodicOrbitRepresentativesEight.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  rw [goldenPeriodicOrbitRepresentativesEight, List.forall_append]
  exact ⟨golden_periodic_orbit_low_arms_bounded,
    golden_new_periodic_orbit_low_arms_bounded_eight⟩

def goldenPeriodicOrbitMinimaEight : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesEight,
    GoldenOrbitMinimum orbit value}

/-- Every displayed orbit through period eight has an attained arm minimum. -/
theorem golden_periodic_orbit_minimum_exists_eight (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesEight) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp
    golden_periodic_orbit_low_states_mem_eight orbit horbit
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

/-- The complete period-at-most-eight enumeration has maximin exactly
`phi^-2 / 2`. -/
theorem golden_periodic_orbit_maximin_eight :
    IsGreatest goldenPeriodicOrbitMinimaEight goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem_eight orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded_eight orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.GoldenPeriodic.EnumerationEight
