/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five-step separation and low-arm certificates for period twelve. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointB

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveSeparation

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationEleven
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData

def goldenPeriodTwelveInheritedOrbits : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesSeven.filter fun orbit =>
    12 % orbit.steps.length = 0

def goldenInheritedPointCodesTwelve : Finset GoldenCodedState :=
  (goldenPeriodTwelveInheritedOrbits.flatMap goldenOrbitStates).toFinset

def goldenNewOrbitStatesTwelve : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesExactlyTwelve.flatMap
    goldenOrbitStates).toFinset

def goldenExpectedPointCodesTwelve : Finset GoldenCodedState :=
  goldenInheritedPointCodesTwelve ∪ goldenNewOrbitStatesTwelve

def goldenPeriodicOrbitRepresentativesAtTwelve : List GoldenCodedOrbit :=
  goldenPeriodTwelveInheritedOrbits ++
    goldenPeriodicOrbitRepresentativesExactlyTwelve

abbrev GoldenFiveSteps :=
  GoldenPeriodicStep × GoldenPeriodicStep × GoldenPeriodicStep ×
    GoldenPeriodicStep × GoldenPeriodicStep

def goldenOrbitStateFirstFiveSteps (orbit : GoldenCodedOrbit) :
    List (GoldenCodedState × GoldenFiveSteps) :=
  (goldenOrbitStates orbit).zip
    (orbit.steps.zip ((orbit.steps.rotate 1).zip
      ((orbit.steps.rotate 2).zip
        ((orbit.steps.rotate 3).zip (orbit.steps.rotate 4)))))

def goldenPeriodTwelveStateFirstFiveSteps :
    List (GoldenCodedState × GoldenFiveSteps) :=
  goldenPeriodicOrbitRepresentativesAtTwelve.flatMap
    goldenOrbitStateFirstFiveSteps

@[simp] def goldenStatesForFirstFiveStepsIn
    (items : List (GoldenCodedState × GoldenFiveSteps))
    (steps : GoldenFiveSteps) : Finset GoldenCodedState :=
  (items.filterMap fun item =>
    if item.2 = steps then some item.1 else none).toFinset

def goldenStatesForFirstFiveStepsTwelve
    (steps : GoldenFiveSteps) : Finset GoldenCodedState :=
  goldenStatesForFirstFiveStepsIn goldenPeriodTwelveStateFirstFiveSteps steps

def goldenLegalFiveSteps : List GoldenFiveSteps :=
  [(.left, .left, .left, .left, .left),
    (.left, .left, .left, .left, .right),
    (.left, .left, .left, .right, .through),
    (.left, .left, .right, .through, .left),
    (.left, .left, .right, .through, .right),
    (.left, .right, .through, .left, .left),
    (.left, .right, .through, .left, .right),
    (.left, .right, .through, .right, .through),
    (.right, .through, .left, .left, .left),
    (.right, .through, .left, .left, .right),
    (.right, .through, .left, .right, .through),
    (.right, .through, .right, .through, .left),
    (.right, .through, .right, .through, .right),
    (.through, .left, .left, .left, .left),
    (.through, .left, .left, .left, .right),
    (.through, .left, .left, .right, .through),
    (.through, .left, .right, .through, .left),
    (.through, .left, .right, .through, .right),
    (.through, .right, .through, .left, .left),
    (.through, .right, .through, .left, .right),
    (.through, .right, .through, .right, .through)]

def goldenFiveStepStateUnion : List GoldenFiveSteps → Finset GoldenCodedState
  | [] => ∅
  | steps :: rest =>
      goldenStatesForFirstFiveStepsTwelve steps ∪
        goldenFiveStepStateUnion rest

theorem golden_orbit_state_first_five_steps_fst (orbit : GoldenCodedOrbit) :
    (goldenOrbitStateFirstFiveSteps orbit).map Prod.fst =
      goldenOrbitStates orbit := by
  rw [goldenOrbitStateFirstFiveSteps, List.map_fst_zip]
  simp [goldenOrbitStates, golden_trace_code_length]

theorem golden_inherited_orbit_states_eq_point_codes_twelve :
    (goldenPeriodTwelveInheritedOrbits.flatMap goldenOrbitStates).toFinset =
      goldenInheritedPointCodesTwelve := by
  rfl

theorem golden_period_twelve_state_first_five_fst :
    (goldenPeriodTwelveStateFirstFiveSteps.map Prod.fst).toFinset =
      goldenExpectedPointCodesTwelve := by
  rw [goldenPeriodTwelveStateFirstFiveSteps, List.map_flatMap]
  simp_rw [golden_orbit_state_first_five_steps_fst]
  rw [goldenPeriodicOrbitRepresentativesAtTwelve, List.flatMap_append,
    List.toFinset_append, golden_inherited_orbit_states_eq_point_codes_twelve]
  rfl

theorem golden_states_for_first_five_steps_in_subset
    (items : List (GoldenCodedState × GoldenFiveSteps))
    (steps : GoldenFiveSteps) :
    goldenStatesForFirstFiveStepsIn items steps ⊆
      (items.map Prod.fst).toFinset := by
  intro state hstate
  simp only [goldenStatesForFirstFiveStepsIn, List.mem_toFinset,
    List.mem_filterMap, List.mem_map] at hstate ⊢
  obtain ⟨item, hitem, hselected⟩ := hstate
  split at hselected
  · simp only [Option.some.injEq] at hselected
    exact ⟨item, hitem, hselected⟩
  · contradiction

theorem golden_mem_five_step_state_union_iff
    (state : GoldenCodedState) (prefixes : List GoldenFiveSteps) :
    state ∈ goldenFiveStepStateUnion prefixes ↔
      ∃ steps ∈ prefixes, state ∈ goldenStatesForFirstFiveStepsTwelve steps := by
  induction prefixes with
  | nil => simp [goldenFiveStepStateUnion]
  | cons steps rest ih =>
      simp only [goldenFiveStepStateUnion, Finset.mem_union]
      constructor
      · intro hstate
        rcases hstate with hstate | hstate
        · exact ⟨steps, by simp, hstate⟩
        · obtain ⟨candidate, hprefix, hpresent⟩ := ih.mp hstate
          exact ⟨candidate, by simp [hprefix], hpresent⟩
      · rintro ⟨candidate, hprefix, hpresent⟩
        simp only [List.mem_cons] at hprefix
        rcases hprefix with rfl | hprefix
        · exact Or.inl hpresent
        · exact Or.inr (ih.mpr ⟨candidate, hprefix, hpresent⟩)

theorem golden_legal_five_step_partition
    (hlegal : goldenPeriodTwelveStateFirstFiveSteps.Forall fun item =>
      item.2 ∈ goldenLegalFiveSteps) :
    (goldenPeriodTwelveStateFirstFiveSteps.map Prod.fst).toFinset =
      goldenFiveStepStateUnion goldenLegalFiveSteps := by
  apply Finset.Subset.antisymm
  · intro state hstate
    rw [List.mem_toFinset] at hstate
    simp only [List.mem_map] at hstate
    obtain ⟨item, hitem, rfl⟩ := hstate
    rw [golden_mem_five_step_state_union_iff]
    refine ⟨item.2, List.forall_iff_forall_mem.mp hlegal item hitem, ?_⟩
    simp only [goldenStatesForFirstFiveStepsTwelve,
      goldenStatesForFirstFiveStepsIn, List.mem_toFinset,
      List.mem_filterMap]
    exact ⟨item, hitem, by simp⟩
  · intro state hstate
    rw [golden_mem_five_step_state_union_iff] at hstate
    obtain ⟨steps, _, hsteps⟩ := hstate
    exact golden_states_for_first_five_steps_in_subset _ _ hsteps

theorem golden_period_twelve_inherited_first_five_steps_legal :
    (goldenPeriodTwelveInheritedOrbits.flatMap
      goldenOrbitStateFirstFiveSteps).Forall fun item =>
        item.2 ∈ goldenLegalFiveSteps := by
  norm_num [goldenPeriodTwelveInheritedOrbits,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_ab_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitA).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitB).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_cd_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitC).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitD).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_ef_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitE).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitF).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_gh_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitG).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitH).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_ij_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitI).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitJ).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_kl_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitK).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitL).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_mn_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitM).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitN).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_op_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitO).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitP).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_qr_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitQ).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitR).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_st_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitS).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitT).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitT,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_uv_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitU).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitV).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitU, goldenPeriodTwelveOrbitV,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbits_wx_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitW).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) ∧
      (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitX).Forall
        (fun item => item.2 ∈ goldenLegalFiveSteps) := by
  norm_num [goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_orbit_y_first_five_steps_legal :
    (goldenOrbitStateFirstFiveSteps goldenPeriodTwelveOrbitY).Forall
      fun item => item.2 ∈ goldenLegalFiveSteps := by
  norm_num [goldenPeriodTwelveOrbitY, goldenOrbitStateFirstFiveSteps, goldenLegalFiveSteps,
    goldenOrbitStates, goldenTraceCode]

theorem golden_period_twelve_first_five_steps_legal :
    goldenPeriodTwelveStateFirstFiveSteps.Forall fun item =>
      item.2 ∈ goldenLegalFiveSteps := by
  simp only [goldenPeriodTwelveStateFirstFiveSteps,
    goldenPeriodicOrbitRepresentativesAtTwelve,
    goldenPeriodicOrbitRepresentativesExactlyTwelve, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.flatMap_append, List.forall_append]
  exact ⟨golden_period_twelve_inherited_first_five_steps_legal,
    golden_period_twelve_orbits_ab_first_five_steps_legal.1,
    golden_period_twelve_orbits_ab_first_five_steps_legal.2,
    golden_period_twelve_orbits_cd_first_five_steps_legal.1,
    golden_period_twelve_orbits_cd_first_five_steps_legal.2,
    golden_period_twelve_orbits_ef_first_five_steps_legal.1,
    golden_period_twelve_orbits_ef_first_five_steps_legal.2,
    golden_period_twelve_orbits_gh_first_five_steps_legal.1,
    golden_period_twelve_orbits_gh_first_five_steps_legal.2,
    golden_period_twelve_orbits_ij_first_five_steps_legal.1,
    golden_period_twelve_orbits_ij_first_five_steps_legal.2,
    golden_period_twelve_orbits_kl_first_five_steps_legal.1,
    golden_period_twelve_orbits_kl_first_five_steps_legal.2,
    golden_period_twelve_orbits_mn_first_five_steps_legal.1,
    golden_period_twelve_orbits_mn_first_five_steps_legal.2,
    golden_period_twelve_orbits_op_first_five_steps_legal.1,
    golden_period_twelve_orbits_op_first_five_steps_legal.2,
    golden_period_twelve_orbits_qr_first_five_steps_legal.1,
    golden_period_twelve_orbits_qr_first_five_steps_legal.2,
    golden_period_twelve_orbits_st_first_five_steps_legal.1,
    golden_period_twelve_orbits_st_first_five_steps_legal.2,
    golden_period_twelve_orbits_uv_first_five_steps_legal.1,
    golden_period_twelve_orbits_uv_first_five_steps_legal.2,
    golden_period_twelve_orbits_wx_first_five_steps_legal.1,
    golden_period_twelve_orbits_wx_first_five_steps_legal.2,
    golden_period_twelve_orbit_y_first_five_steps_legal⟩

theorem golden_period_twelve_states_partition_by_first_five :
    goldenExpectedPointCodesTwelve =
      goldenFiveStepStateUnion goldenLegalFiveSteps := by
  rw [← golden_period_twelve_state_first_five_fst]
  exact golden_legal_five_step_partition
    golden_period_twelve_first_five_steps_legal

theorem golden_period_twelve_orbits_ab_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitA.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitB.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitA, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitB, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_cd_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitC.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitD.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitC, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitD, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_ef_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitE.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitF.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitE, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitF, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_gh_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitG.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitH.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitG, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitH, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_ij_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitI.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitJ.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitI, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitJ, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_kl_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitK.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitL.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitK, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitL, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_mn_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitM.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitN.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitM, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitN, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_op_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitO.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitP.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitO, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitP, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_qr_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitQ.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitR.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitQ, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitR, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_st_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitS.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitT.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitS, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitT, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_uv_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitU.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitV.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitU, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitV, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbits_wx_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitW.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitX.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitW, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTwelveOrbitX, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_twelve_orbit_y_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodTwelveOrbitY.lowState) ≤
      goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodTwelveOrbitY, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_new_periodic_orbit_low_arms_bounded_twelve :
    goldenPeriodicOrbitRepresentativesExactlyTwelve.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyTwelve, List.forall_cons]
  exact ⟨golden_period_twelve_orbits_ab_low_arms.1,
    golden_period_twelve_orbits_ab_low_arms.2,
    golden_period_twelve_orbits_cd_low_arms.1,
    golden_period_twelve_orbits_cd_low_arms.2,
    golden_period_twelve_orbits_ef_low_arms.1,
    golden_period_twelve_orbits_ef_low_arms.2,
    golden_period_twelve_orbits_gh_low_arms.1,
    golden_period_twelve_orbits_gh_low_arms.2,
    golden_period_twelve_orbits_ij_low_arms.1,
    golden_period_twelve_orbits_ij_low_arms.2,
    golden_period_twelve_orbits_kl_low_arms.1,
    golden_period_twelve_orbits_kl_low_arms.2,
    golden_period_twelve_orbits_mn_low_arms.1,
    golden_period_twelve_orbits_mn_low_arms.2,
    golden_period_twelve_orbits_op_low_arms.1,
    golden_period_twelve_orbits_op_low_arms.2,
    golden_period_twelve_orbits_qr_low_arms.1,
    golden_period_twelve_orbits_qr_low_arms.2,
    golden_period_twelve_orbits_st_low_arms.1,
    golden_period_twelve_orbits_st_low_arms.2,
    golden_period_twelve_orbits_uv_low_arms.1,
    golden_period_twelve_orbits_uv_low_arms.2,
    golden_period_twelve_orbits_wx_low_arms.1,
    golden_period_twelve_orbits_wx_low_arms.2,
    golden_period_twelve_orbit_y_low_arm, by simp⟩

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveSeparation
