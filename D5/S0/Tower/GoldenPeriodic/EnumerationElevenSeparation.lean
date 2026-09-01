/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separation and low-arm certificates for the period-eleven golden orbits. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationElevenDisjoint

namespace D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTen
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData

def goldenInheritedPointCodesEleven : Finset GoldenCodedState :=
  ([1].flatMap goldenFixedPointCodes).toFinset

def goldenNewOrbitStatesEleven : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap goldenOrbitStates).toFinset

def goldenExpectedPointCodesEleven : Finset GoldenCodedState :=
  goldenInheritedPointCodesEleven ∪ goldenNewOrbitStatesEleven

def goldenPeriodElevenInheritedOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi 0 0⟩, [.left], ⟨.large, qphi 0 0⟩⟩

def goldenPeriodElevenInheritedOrbits : List GoldenCodedOrbit :=
  [goldenPeriodElevenInheritedOrbitA]

def goldenPeriodicOrbitRepresentativesAtEleven : List GoldenCodedOrbit :=
  goldenPeriodElevenInheritedOrbits ++ goldenPeriodicOrbitRepresentativesExactlyEleven

def goldenOrbitStateFirstFourSteps (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)) :=
  (goldenOrbitStates orbit).zip
    (orbit.steps.zip ((orbit.steps.rotate 1).zip
      ((orbit.steps.rotate 2).zip (orbit.steps.rotate 3))))

def goldenFirstThreeOfFour
    (item : GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)) :
    GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep) :=
  (item.1, item.2.1, item.2.2.1, item.2.2.2.1)

def goldenOrbitStateFirstThreeSteps (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)) :=
  (goldenOrbitStateFirstFourSteps orbit).map goldenFirstThreeOfFour

def goldenPeriodElevenStateFirstThreeSteps :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)) :=
  goldenPeriodicOrbitRepresentativesAtEleven.flatMap goldenOrbitStateFirstThreeSteps

def goldenPeriodElevenStateFirstFourSteps :
    List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)) :=
  goldenPeriodicOrbitRepresentativesAtEleven.flatMap goldenOrbitStateFirstFourSteps

@[simp] def goldenStatesForFirstThreeStepsIn
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second third : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2.1 = first ∧ item.2.2.1 = second ∧ item.2.2.2 = third then
      some item.1
    else none).toFinset

def goldenStatesForFirstThreeStepsEleven
    (first second third : GoldenPeriodicStep) : Finset GoldenCodedState :=
  goldenStatesForFirstThreeStepsIn goldenPeriodElevenStateFirstThreeSteps
    first second third

@[simp] def goldenStatesForFirstFourStepsIn
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second third fourth : GoldenPeriodicStep) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2.1 = first ∧ item.2.2.1 = second ∧
        item.2.2.2.1 = third ∧ item.2.2.2.2 = fourth then
      some item.1
    else none).toFinset

def goldenStatesForFirstFourStepsEleven
    (first second third fourth : GoldenPeriodicStep) : Finset GoldenCodedState :=
  goldenStatesForFirstFourStepsIn goldenPeriodElevenStateFirstFourSteps
    first second third fourth

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

theorem golden_orbit_state_first_four_steps_fst (orbit : GoldenCodedOrbit) :
    (goldenOrbitStateFirstFourSteps orbit).map Prod.fst =
      goldenOrbitStates orbit := by
  rw [goldenOrbitStateFirstFourSteps, List.map_fst_zip]
  simp [goldenOrbitStates, golden_trace_code_length]

theorem golden_orbit_state_first_three_steps_fst (orbit : GoldenCodedOrbit) :
    (goldenOrbitStateFirstThreeSteps orbit).map Prod.fst =
      goldenOrbitStates orbit := by
  rw [goldenOrbitStateFirstThreeSteps, List.map_map]
  simpa [goldenFirstThreeOfFour, Function.comp_def] using
    golden_orbit_state_first_four_steps_fst orbit

theorem golden_period_eleven_state_first_three_eq_four_map :
    goldenPeriodElevenStateFirstThreeSteps =
      goldenPeriodElevenStateFirstFourSteps.map goldenFirstThreeOfFour := by
  rw [goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodElevenStateFirstFourSteps, List.map_flatMap]
  rfl

theorem golden_inherited_orbit_states_eq_point_codes_eleven :
    (goldenPeriodElevenInheritedOrbits.flatMap goldenOrbitStates).toFinset =
      goldenInheritedPointCodesEleven := by
  apply Finset.ext
  intro code
  simp [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.filterMap_nil, goldenPeriodElevenInheritedOrbits,
    goldenPeriodElevenInheritedOrbitA, goldenInheritedPointCodesEleven,
    goldenOrbitStates, goldenTraceCode,
    goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine,
    goldenAffineCompose, goldenCodeDiv, goldenCodeInv, goldenCodeNorm,
    goldenCodeSub, goldenCodeNeg, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, qphi]

theorem golden_period_eleven_state_first_three_fst :
    (goldenPeriodElevenStateFirstThreeSteps.map Prod.fst).toFinset =
      goldenExpectedPointCodesEleven := by
  rw [goldenPeriodElevenStateFirstThreeSteps, List.map_flatMap]
  simp_rw [golden_orbit_state_first_three_steps_fst]
  rw [goldenPeriodicOrbitRepresentativesAtEleven, List.flatMap_append,
    List.toFinset_append, golden_inherited_orbit_states_eq_point_codes_eleven]
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

theorem golden_states_for_first_three_steps_split_four
    (items : List (GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)))
    (first second third : GoldenPeriodicStep)
    (hfourth : items.Forall fun item =>
      (item.2.1 = first ∧ item.2.2.1 = second ∧ item.2.2.2.1 = third) →
        item.2.2.2.2 = .left ∨ item.2.2.2.2 = .right) :
    goldenStatesForFirstThreeStepsIn (items.map goldenFirstThreeOfFour)
        first second third =
      goldenStatesForFirstFourStepsIn items first second third .left ∪
        goldenStatesForFirstFourStepsIn items first second third .right := by
  apply Finset.Subset.antisymm
  · intro state hstate
    simp only [goldenStatesForFirstThreeStepsIn, List.filterMap_map,
      Function.comp_apply, List.mem_toFinset, List.mem_filterMap] at hstate
    obtain ⟨item, hitem, hselected⟩ := hstate
    by_cases hselectedCondition : (goldenFirstThreeOfFour item).2.1 = first ∧ (goldenFirstThreeOfFour item).2.2.1 = second ∧ (goldenFirstThreeOfFour item).2.2.2 = third
    · rw [if_pos hselectedCondition] at hselected
      simp only [Option.some.injEq, goldenFirstThreeOfFour] at hselected
      have hthree : item.2.1 = first ∧ item.2.2.1 = second ∧ item.2.2.2.1 = third := by
        simpa only [goldenFirstThreeOfFour] using hselectedCondition
      rw [Finset.mem_union]
      rcases List.forall_iff_forall_mem.mp hfourth item hitem hthree with
        hleft | hright
      · left
        rw [goldenStatesForFirstFourStepsIn, List.mem_toFinset]
        simp only [List.mem_filterMap]
        refine ⟨item, hitem, ?_⟩
        simp [hthree.1, hthree.2.1, hthree.2.2, hleft, hselected]
      · right
        rw [goldenStatesForFirstFourStepsIn, List.mem_toFinset]
        simp only [List.mem_filterMap]
        refine ⟨item, hitem, ?_⟩
        simp [hthree.1, hthree.2.1, hthree.2.2, hright, hselected]
    · rw [if_neg hselectedCondition] at hselected
      cases hselected
  · intro state hstate
    rw [Finset.mem_union] at hstate
    simp only [goldenStatesForFirstThreeStepsIn, List.filterMap_map,
      Function.comp_apply, goldenFirstThreeOfFour, List.mem_toFinset,
      List.mem_filterMap]
    rcases hstate with hstate | hstate
    · rw [goldenStatesForFirstFourStepsIn, List.mem_toFinset] at hstate
      simp only [List.mem_filterMap] at hstate
      obtain ⟨item, hitem, hselected⟩ := hstate
      split at hselected
      · rename_i hfour
        simp only [Option.some.injEq] at hselected
        refine ⟨item, hitem, ?_⟩
        simp [hfour.1, hfour.2.1, hfour.2.2.1, hselected]
      · contradiction
    · rw [goldenStatesForFirstFourStepsIn, List.mem_toFinset] at hstate
      simp only [List.mem_filterMap] at hstate
      obtain ⟨item, hitem, hselected⟩ := hstate
      split at hselected
      · rename_i hfour
        simp only [Option.some.injEq] at hselected
        refine ⟨item, hitem, ?_⟩
        simp [hfour.1, hfour.2.1, hfour.2.2.1, hselected]
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

theorem golden_period_eleven_inherited_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenInheritedOrbitA).Forall
      fun item => goldenThreeStepLegal item.2 := by
  norm_num [goldenPeriodElevenInheritedOrbitA, goldenOrbitStateFirstThreeSteps,
    goldenOrbitStateFirstFourSteps, goldenFirstThreeOfFour, goldenOrbitStates,
    goldenTraceCode, goldenThreeStepLegal]

theorem golden_period_eleven_orbits_ab_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitA).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitB).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_cd_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitC).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitD).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_ef_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitE).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitF).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_gh_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitG).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitH).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_ij_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitI).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitJ).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_kl_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitK).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitL).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_mn_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitM).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitN).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_op_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitO).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitP).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_orbits_qr_first_three_steps_legal :
    (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitQ).Forall
        (fun item => goldenThreeStepLegal item.2) ∧
      (goldenOrbitStateFirstThreeSteps goldenPeriodElevenOrbitR).Forall
        (fun item => goldenThreeStepLegal item.2) := by
  norm_num [goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstThreeSteps, goldenOrbitStateFirstFourSteps,
    goldenFirstThreeOfFour, goldenOrbitStates, goldenTraceCode,
    goldenThreeStepLegal]

theorem golden_period_eleven_first_three_steps_legal :
    goldenPeriodElevenStateFirstThreeSteps.Forall fun item =>
      goldenThreeStepLegal item.2 := by
  simp only [goldenPeriodElevenStateFirstThreeSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodicOrbitRepresentativesExactlyEleven, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.flatMap_append, List.forall_append]
  exact ⟨golden_period_eleven_inherited_first_three_steps_legal,
    golden_period_eleven_orbits_ab_first_three_steps_legal.1,
    golden_period_eleven_orbits_ab_first_three_steps_legal.2,
    golden_period_eleven_orbits_cd_first_three_steps_legal.1,
    golden_period_eleven_orbits_cd_first_three_steps_legal.2,
    golden_period_eleven_orbits_ef_first_three_steps_legal.1,
    golden_period_eleven_orbits_ef_first_three_steps_legal.2,
    golden_period_eleven_orbits_gh_first_three_steps_legal.1,
    golden_period_eleven_orbits_gh_first_three_steps_legal.2,
    golden_period_eleven_orbits_ij_first_three_steps_legal.1,
    golden_period_eleven_orbits_ij_first_three_steps_legal.2,
    golden_period_eleven_orbits_kl_first_three_steps_legal.1,
    golden_period_eleven_orbits_kl_first_three_steps_legal.2,
    golden_period_eleven_orbits_mn_first_three_steps_legal.1,
    golden_period_eleven_orbits_mn_first_three_steps_legal.2,
    golden_period_eleven_orbits_op_first_three_steps_legal.1,
    golden_period_eleven_orbits_op_first_three_steps_legal.2,
    golden_period_eleven_orbits_qr_first_three_steps_legal.1,
    golden_period_eleven_orbits_qr_first_three_steps_legal.2⟩

def goldenLargeThreeStepFourthLegal
    (item : GoldenCodedState ×
      (GoldenPeriodicStep × GoldenPeriodicStep ×
        GoldenPeriodicStep × GoldenPeriodicStep)) : Prop :=
  ((item.2.1 = .left ∧ item.2.2.1 = .left ∧ item.2.2.2.1 = .left) ∨
    (item.2.1 = .left ∧ item.2.2.1 = .right ∧
      item.2.2.2.1 = .through) ∨
    (item.2.1 = .right ∧ item.2.2.1 = .through ∧
      item.2.2.2.1 = .left)) →
    item.2.2.2.2 = .left ∨ item.2.2.2.2 = .right

theorem golden_period_eleven_inherited_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenInheritedOrbitA).Forall
      goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenInheritedOrbitA, goldenOrbitStateFirstFourSteps,
    goldenOrbitStates, goldenTraceCode, goldenLargeThreeStepFourthLegal]

theorem golden_period_eleven_orbits_ab_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitA).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitB).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_cd_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitC).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitD).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_ef_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitE).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitF).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_gh_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitG).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitH).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_ij_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitI).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitJ).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_kl_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitK).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitL).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_mn_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitM).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitN).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_op_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitO).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitP).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_orbits_qr_large_three_step_fourth_legal :
    (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitQ).Forall
        goldenLargeThreeStepFourthLegal ∧
      (goldenOrbitStateFirstFourSteps goldenPeriodElevenOrbitR).Forall
        goldenLargeThreeStepFourthLegal := by
  norm_num [goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStateFirstFourSteps, goldenOrbitStates, goldenTraceCode,
    goldenLargeThreeStepFourthLegal] ; tauto

theorem golden_period_eleven_large_three_step_fourth_legal :
    goldenPeriodElevenStateFirstFourSteps.Forall
      goldenLargeThreeStepFourthLegal := by
  simp only [goldenPeriodElevenStateFirstFourSteps,
    goldenPeriodicOrbitRepresentativesAtEleven, goldenPeriodElevenInheritedOrbits,
    goldenPeriodicOrbitRepresentativesExactlyEleven, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.flatMap_append, List.forall_append]
  exact ⟨golden_period_eleven_inherited_large_three_step_fourth_legal,
    golden_period_eleven_orbits_ab_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_ab_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_cd_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_cd_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_ef_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_ef_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_gh_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_gh_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_ij_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_ij_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_kl_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_kl_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_mn_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_mn_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_op_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_op_large_three_step_fourth_legal.2,
    golden_period_eleven_orbits_qr_large_three_step_fourth_legal.1,
    golden_period_eleven_orbits_qr_large_three_step_fourth_legal.2⟩

theorem golden_states_for_first_three_steps_lll_split_eleven :
    goldenStatesForFirstThreeStepsEleven .left .left .left =
      goldenStatesForFirstFourStepsEleven .left .left .left .left ∪
        goldenStatesForFirstFourStepsEleven .left .left .left .right := by
  rw [goldenStatesForFirstThreeStepsEleven,
    golden_period_eleven_state_first_three_eq_four_map,
    goldenStatesForFirstFourStepsEleven]
  apply golden_states_for_first_three_steps_split_four
  apply List.forall_iff_forall_mem.mpr
  intro item hitem hthree
  exact (List.forall_iff_forall_mem.mp
    golden_period_eleven_large_three_step_fourth_legal item hitem) (Or.inl hthree)

theorem golden_states_for_first_three_steps_lrt_split_eleven :
    goldenStatesForFirstThreeStepsEleven .left .right .through =
      goldenStatesForFirstFourStepsEleven .left .right .through .left ∪
        goldenStatesForFirstFourStepsEleven .left .right .through .right := by
  rw [goldenStatesForFirstThreeStepsEleven,
    golden_period_eleven_state_first_three_eq_four_map,
    goldenStatesForFirstFourStepsEleven]
  apply golden_states_for_first_three_steps_split_four
  apply List.forall_iff_forall_mem.mpr
  intro item hitem hthree
  exact (List.forall_iff_forall_mem.mp
    golden_period_eleven_large_three_step_fourth_legal item hitem)
      (Or.inr (Or.inl hthree))

theorem golden_states_for_first_three_steps_rtl_split_eleven :
    goldenStatesForFirstThreeStepsEleven .right .through .left =
      goldenStatesForFirstFourStepsEleven .right .through .left .left ∪
        goldenStatesForFirstFourStepsEleven .right .through .left .right := by
  rw [goldenStatesForFirstThreeStepsEleven,
    golden_period_eleven_state_first_three_eq_four_map,
    goldenStatesForFirstFourStepsEleven]
  apply golden_states_for_first_three_steps_split_four
  apply List.forall_iff_forall_mem.mpr
  intro item hitem hthree
  exact (List.forall_iff_forall_mem.mp
    golden_period_eleven_large_three_step_fourth_legal item hitem)
      (Or.inr (Or.inr hthree))


theorem golden_period_eleven_states_partition_by_first_three :
    goldenExpectedPointCodesEleven =
      goldenStatesForFirstThreeStepsEleven .left .left .left ∪
      goldenStatesForFirstThreeStepsEleven .left .left .right ∪
      goldenStatesForFirstThreeStepsEleven .left .right .through ∪
      goldenStatesForFirstThreeStepsEleven .right .through .left ∪
      goldenStatesForFirstThreeStepsEleven .right .through .right ∪
      goldenStatesForFirstThreeStepsEleven .through .left .left ∪
      goldenStatesForFirstThreeStepsEleven .through .left .right ∪
      goldenStatesForFirstThreeStepsEleven .through .right .through := by
  rw [← golden_period_eleven_state_first_three_fst]
  exact golden_legal_three_step_partition _
    golden_period_eleven_first_three_steps_legal


theorem golden_period_eleven_orbits_ab_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitA.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitB.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitA, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitB, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_cd_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitC.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitD.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitC, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitD, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_ef_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitE.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitF.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitE, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitF, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_gh_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitG.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitH.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitG, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitH, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_ij_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitI.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitJ.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitI, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitJ, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_kl_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitK.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitL.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitK, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitL, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_mn_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitM.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitN.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitM, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitN, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_op_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitO.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitP.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitO, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitP, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_eleven_orbits_qr_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitQ.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodElevenOrbitR.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitQ, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodElevenOrbitR, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_new_periodic_orbit_low_arms_bounded_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyEleven, List.forall_cons]
  exact ⟨golden_period_eleven_orbits_ab_low_arms.1,
    golden_period_eleven_orbits_ab_low_arms.2, golden_period_eleven_orbits_cd_low_arms.1,
    golden_period_eleven_orbits_cd_low_arms.2, golden_period_eleven_orbits_ef_low_arms.1,
    golden_period_eleven_orbits_ef_low_arms.2, golden_period_eleven_orbits_gh_low_arms.1,
    golden_period_eleven_orbits_gh_low_arms.2, golden_period_eleven_orbits_ij_low_arms.1,
    golden_period_eleven_orbits_ij_low_arms.2,
    golden_period_eleven_orbits_kl_low_arms.1,
    golden_period_eleven_orbits_kl_low_arms.2,
    golden_period_eleven_orbits_mn_low_arms.1,
    golden_period_eleven_orbits_mn_low_arms.2,
    golden_period_eleven_orbits_op_low_arms.1,
    golden_period_eleven_orbits_op_low_arms.2,
    golden_period_eleven_orbits_qr_low_arms.1,
    golden_period_eleven_orbits_qr_low_arms.2, by simp⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation
