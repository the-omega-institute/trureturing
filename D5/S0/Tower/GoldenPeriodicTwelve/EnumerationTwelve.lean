/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-twelve enumeration for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveFixed

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelve

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationEleven
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDistinct
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointB
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveSeparation
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveFixed

/- Library-search audit (2026-08-17): the repository has the frozen P <= 11
certificate but no P = 12 extension; no pinned library theorem specializes the
finite-list and rational-arithmetic kernels to this golden transition. -/

def goldenPeriodicOrbitRepresentativesTwelve : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesEleven ++
    goldenPeriodicOrbitRepresentativesExactlyTwelve

def goldenPeriodicPointCodesTwelve : Finset GoldenCodedState :=
  goldenPeriodicPointCodesEleven ∪ (goldenFixedPointCodes 12).toFinset

def goldenClosedItinerariesBlockTwelve
    (start source : GoldenGapKind) (initialSteps : List GoldenPeriodicStep) :
    List (GoldenGapKind × List GoldenPeriodicStep) :=
  (goldenPathsFrom source 7).filterMap fun path =>
    if path.2 = start then some (start, initialSteps ++ path.1) else none

def goldenClosedItineraryDenominatorNonzeroTwelve
    (itinerary : GoldenGapKind × List GoldenPeriodicStep) : Prop :=
  goldenCodeNorm
    (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0

theorem golden_closed_itineraries_twelve_split :
    goldenClosedItineraries 12 =
      goldenClosedItinerariesBlockTwelve .large .large
          [.left, .left, .left, .left, .left] ++
      goldenClosedItinerariesBlockTwelve .large .small
          [.left, .left, .left, .left, .right] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.left, .left, .left, .right, .through] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.left, .left, .right, .through, .left] ++
      goldenClosedItinerariesBlockTwelve .large .small
          [.left, .left, .right, .through, .right] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.left, .right, .through, .left, .left] ++
      goldenClosedItinerariesBlockTwelve .large .small
          [.left, .right, .through, .left, .right] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.left, .right, .through, .right, .through] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.right, .through, .left, .left, .left] ++
      goldenClosedItinerariesBlockTwelve .large .small
          [.right, .through, .left, .left, .right] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.right, .through, .left, .right, .through] ++
      goldenClosedItinerariesBlockTwelve .large .large
          [.right, .through, .right, .through, .left] ++
      goldenClosedItinerariesBlockTwelve .large .small
          [.right, .through, .right, .through, .right] ++
      goldenClosedItinerariesBlockTwelve .small .large
          [.through, .left, .left, .left, .left] ++
      goldenClosedItinerariesBlockTwelve .small .small
          [.through, .left, .left, .left, .right] ++
      goldenClosedItinerariesBlockTwelve .small .large
          [.through, .left, .left, .right, .through] ++
      goldenClosedItinerariesBlockTwelve .small .large
          [.through, .left, .right, .through, .left] ++
      goldenClosedItinerariesBlockTwelve .small .small
          [.through, .left, .right, .through, .right] ++
      goldenClosedItinerariesBlockTwelve .small .large
          [.through, .right, .through, .left, .left] ++
      goldenClosedItinerariesBlockTwelve .small .small
          [.through, .right, .through, .left, .right] ++
      goldenClosedItinerariesBlockTwelve .small .large
          [.through, .right, .through, .right, .through] := by
  rw [goldenClosedItineraries, golden_paths_from_large_twelve_split,
    golden_paths_from_small_twelve_split]
  simp [goldenClosedItinerariesBlockTwelve, List.filterMap_append,
    List.filterMap_map, List.append_assoc]

macro "solve_golden_twelve_denominator" : tactic =>
  `(tactic|
    (simp [goldenClosedItinerariesBlockTwelve,
       goldenClosedItineraryDenominatorNonzeroTwelve, goldenPathsFrom]
     norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
       goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
       goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero,
       goldenCodePhi]))

theorem golden_closed_itinerary_denominator_large_lllll_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.left, .left, .left, .left, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_llllr_twelve :
    (goldenClosedItinerariesBlockTwelve .large .small
      [.left, .left, .left, .left, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_lllrt_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.left, .left, .left, .right, .through]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_llrtl_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.left, .left, .right, .through, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_llrtr_twelve :
    (goldenClosedItinerariesBlockTwelve .large .small
      [.left, .left, .right, .through, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_lrtll_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.left, .right, .through, .left, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_lrtlr_twelve :
    (goldenClosedItinerariesBlockTwelve .large .small
      [.left, .right, .through, .left, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_lrtrt_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.left, .right, .through, .right, .through]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_rtlll_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.right, .through, .left, .left, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_rtllr_twelve :
    (goldenClosedItinerariesBlockTwelve .large .small
      [.right, .through, .left, .left, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_rtlrt_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.right, .through, .left, .right, .through]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_rtrtl_twelve :
    (goldenClosedItinerariesBlockTwelve .large .large
      [.right, .through, .right, .through, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_large_rtrtr_twelve :
    (goldenClosedItinerariesBlockTwelve .large .small
      [.right, .through, .right, .through, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_tllll_twelve :
    (goldenClosedItinerariesBlockTwelve .small .large
      [.through, .left, .left, .left, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_tlllr_twelve :
    (goldenClosedItinerariesBlockTwelve .small .small
      [.through, .left, .left, .left, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_tllrt_twelve :
    (goldenClosedItinerariesBlockTwelve .small .large
      [.through, .left, .left, .right, .through]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_tlrtl_twelve :
    (goldenClosedItinerariesBlockTwelve .small .large
      [.through, .left, .right, .through, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_tlrtr_twelve :
    (goldenClosedItinerariesBlockTwelve .small .small
      [.through, .left, .right, .through, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_trtll_twelve :
    (goldenClosedItinerariesBlockTwelve .small .large
      [.through, .right, .through, .left, .left]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_trtlr_twelve :
    (goldenClosedItinerariesBlockTwelve .small .small
      [.through, .right, .through, .left, .right]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominator_small_trtrt_twelve :
    (goldenClosedItinerariesBlockTwelve .small .large
      [.through, .right, .through, .right, .through]).Forall
        goldenClosedItineraryDenominatorNonzeroTwelve := by
  solve_golden_twelve_denominator

theorem golden_closed_itinerary_denominators_exactly_twelve :
    (goldenClosedItineraries 12).Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  change (goldenClosedItineraries 12).Forall
    goldenClosedItineraryDenominatorNonzeroTwelve
  rw [golden_closed_itineraries_twelve_split]
  have appendForall {xs ys : List (GoldenGapKind × List GoldenPeriodicStep)}
      (hxs : xs.Forall goldenClosedItineraryDenominatorNonzeroTwelve)
      (hys : ys.Forall goldenClosedItineraryDenominatorNonzeroTwelve) :
      (xs ++ ys).Forall goldenClosedItineraryDenominatorNonzeroTwelve :=
    List.forall_append.mpr ⟨hxs, hys⟩
  exact appendForall
    (appendForall
      (appendForall
        (appendForall
          (appendForall
            (appendForall
              (appendForall
                (appendForall
                  (appendForall
                    (appendForall
                      (appendForall
                        (appendForall
                          (appendForall
                            (appendForall
                              (appendForall
                                (appendForall
                                  (appendForall
                                    (appendForall
                                      (appendForall
                                        (appendForall
                                          golden_closed_itinerary_denominator_large_lllll_twelve
                                          golden_closed_itinerary_denominator_large_llllr_twelve)
                                        golden_closed_itinerary_denominator_large_lllrt_twelve)
                                      golden_closed_itinerary_denominator_large_llrtl_twelve)
                                    golden_closed_itinerary_denominator_large_llrtr_twelve)
                                  golden_closed_itinerary_denominator_large_lrtll_twelve)
                                golden_closed_itinerary_denominator_large_lrtlr_twelve)
                              golden_closed_itinerary_denominator_large_lrtrt_twelve)
                            golden_closed_itinerary_denominator_large_rtlll_twelve)
                          golden_closed_itinerary_denominator_large_rtllr_twelve)
                        golden_closed_itinerary_denominator_large_rtlrt_twelve)
                      golden_closed_itinerary_denominator_large_rtrtl_twelve)
                    golden_closed_itinerary_denominator_large_rtrtr_twelve)
                  golden_closed_itinerary_denominator_small_tllll_twelve)
                golden_closed_itinerary_denominator_small_tlllr_twelve)
              golden_closed_itinerary_denominator_small_tllrt_twelve)
            golden_closed_itinerary_denominator_small_tlrtl_twelve)
          golden_closed_itinerary_denominator_small_tlrtr_twelve)
        golden_closed_itinerary_denominator_small_trtll_twelve)
      golden_closed_itinerary_denominator_small_trtlr_twelve)
    golden_closed_itinerary_denominator_small_trtrt_twelve

theorem golden_periodic_point_enumeration_complete_exactly_twelve
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[12]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesTwelve, state = decodeGoldenState code := by
  let steps := goldenActualSteps 12 state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries 12 := by
    exact golden_actual_steps_mem_closed hperiod
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp
      golden_closed_itinerary_denominators_exactly_twelve (state.kind, steps) hitinerary
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[12]) state).coordinate :=
        golden_actual_steps_coordinate 12 state
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
  have hcode : code ∈ goldenPeriodicPointCodesTwelve := by
    rw [goldenPeriodicPointCodesTwelve, Finset.mem_union]
    right
    rw [List.mem_toFinset]
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

theorem golden_periodic_point_enumeration_complete_twelve {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 12)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesTwelve, state = decodeGoldenState code := by
  by_cases hperiodEleven : period ≤ 11
  · obtain ⟨code, hcode, hstate⟩ :=
      golden_periodic_point_enumeration_complete_eleven
        hperiodPos hperiodEleven state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hstate⟩
  · have hperiodTwelve : period = 12 := by omega
    subst period
    exact golden_periodic_point_enumeration_complete_exactly_twelve state hperiod

theorem golden_periodic_orbit_representatives_valid_twelve :
    goldenPeriodicOrbitRepresentativesTwelve.Forall goldenCodedOrbitValid := by
  rw [goldenPeriodicOrbitRepresentativesTwelve, List.forall_append]
  exact ⟨golden_periodic_orbit_representatives_valid_eleven,
    golden_new_periodic_orbit_representatives_valid_twelve⟩

def goldenEnumeratedOrbitStatesTwelve : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesTwelve.flatMap goldenOrbitStates).toFinset

theorem golden_periodic_orbit_state_codes_nodup_twelve :
    (goldenPeriodicOrbitRepresentativesTwelve.flatMap goldenOrbitStates).Nodup := by
  rw [goldenPeriodicOrbitRepresentativesTwelve, List.flatMap_append,
    List.nodup_append']
  exact ⟨golden_periodic_orbit_state_codes_nodup_eleven,
    golden_new_periodic_orbit_state_codes_nodup_twelve,
    golden_old_new_periodic_orbit_state_codes_disjoint_twelve⟩

theorem golden_inherited_point_codes_twelve_subset_seven :
    goldenInheritedPointCodesTwelve ⊆ goldenPeriodicPointCodesSeven := by
  intro code hcode
  rw [goldenInheritedPointCodesTwelve, List.mem_toFinset] at hcode
  simp only [List.mem_flatMap] at hcode
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := hcode
  rw [goldenPeriodTwelveInheritedOrbits, List.mem_filter] at horbit
  rw [← golden_enumerated_orbit_states_eq_fixed_points,
    goldenEnumeratedOrbitStatesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap]
  exact ⟨orbit, horbit.1, hcodeOrbit⟩

theorem golden_inherited_point_codes_twelve_subset_eleven :
    goldenInheritedPointCodesTwelve ⊆ goldenPeriodicPointCodesEleven := by
  intro code hcode
  rw [goldenPeriodicPointCodesEleven, Finset.mem_union]
  rw [D5.S0.Tower.GoldenPeriodic.EnumerationTen.goldenPeriodicPointCodesTen,
    Finset.mem_union]
  rw [D5.S0.Tower.GoldenPeriodic.EnumerationNine.goldenPeriodicPointCodesNine,
    Finset.mem_union]
  rw [goldenPeriodicPointCodesEight, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl
    (Or.inl (golden_inherited_point_codes_twelve_subset_seven hcode))))

theorem golden_prior_union_fixed_points_twelve :
    goldenPeriodicPointCodesEleven ∪ (goldenFixedPointCodes 12).toFinset =
      goldenPeriodicPointCodesEleven ∪ goldenNewOrbitStatesTwelve := by
  rw [golden_fixed_point_codes_twelve_decompose, goldenExpectedPointCodesTwelve]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (golden_inherited_point_codes_twelve_subset_eleven hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

theorem golden_enumerated_orbit_states_eq_fixed_points_twelve :
    goldenEnumeratedOrbitStatesTwelve = goldenPeriodicPointCodesTwelve := by
  rw [goldenEnumeratedOrbitStatesTwelve, goldenPeriodicOrbitRepresentativesTwelve,
    List.flatMap_append, List.toFinset_append]
  change goldenEnumeratedOrbitStatesEleven ∪ goldenNewOrbitStatesTwelve =
    goldenPeriodicPointCodesTwelve
  rw [golden_enumerated_orbit_states_eq_fixed_points_eleven,
    goldenPeriodicPointCodesTwelve]
  exact golden_prior_union_fixed_points_twelve.symm

theorem golden_periodic_point_code_count_twelve :
    goldenPeriodicPointCodesTwelve.card = 780 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points_twelve,
    goldenEnumeratedOrbitStatesTwelve,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup_twelve]
  rw [goldenPeriodicOrbitRepresentativesTwelve, List.flatMap_append,
    List.length_append]
  have hold :
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates).length =
        480 := by
    rw [← List.toFinset_card_of_nodup
      golden_periodic_orbit_state_codes_nodup_eleven]
    exact golden_periodic_code_partition_eleven.2
  have hnew :
      (goldenPeriodicOrbitRepresentativesExactlyTwelve.flatMap
        goldenOrbitStates).length = 300 := by
    simp only [List.length_flatMap, goldenOrbitStates,
      golden_trace_code_length]
    rw [golden_new_periodic_orbit_lengths_twelve]
    norm_num
  omega

theorem golden_periodic_code_partition_twelve :
    goldenPeriodicOrbitRepresentativesTwelve.length = 79 ∧
      goldenEnumeratedOrbitStatesTwelve.card = 780 := by
  constructor
  · rw [goldenPeriodicOrbitRepresentativesTwelve, List.length_append]
    have hold := golden_periodic_code_partition_eleven.1
    have hnew := golden_new_periodic_orbit_count_twelve
    omega
  · rw [golden_enumerated_orbit_states_eq_fixed_points_twelve]
    exact golden_periodic_point_code_count_twelve

theorem golden_periodic_orbit_enumeration_complete_twelve {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 12)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesTwelve,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete_twelve
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesTwelve := by
    rw [golden_enumerated_orbit_states_eq_fixed_points_twelve]
    exact hcode
  rw [goldenEnumeratedOrbitStatesTwelve, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem golden_periodic_orbit_low_states_mem_twelve :
    goldenPeriodicOrbitRepresentativesTwelve.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  rw [goldenPeriodicOrbitRepresentativesTwelve, List.forall_append]
  exact ⟨golden_periodic_orbit_low_states_mem_eleven,
    golden_new_periodic_orbit_low_states_mem_twelve⟩

theorem golden_periodic_orbit_low_arms_bounded_twelve :
    goldenPeriodicOrbitRepresentativesTwelve.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  rw [goldenPeriodicOrbitRepresentativesTwelve, List.forall_append]
  exact ⟨golden_periodic_orbit_low_arms_bounded_eleven,
    golden_new_periodic_orbit_low_arms_bounded_twelve⟩

def goldenPeriodicOrbitMinimaTwelve : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesTwelve,
    GoldenOrbitMinimum orbit value}

theorem golden_periodic_orbit_minimum_exists_twelve (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesTwelve) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp
    golden_periodic_orbit_low_states_mem_twelve orbit horbit
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

theorem golden_periodic_orbit_maximin_twelve :
    IsGreatest goldenPeriodicOrbitMinimaTwelve goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesTwelve,
      goldenPeriodicOrbitRepresentativesEleven,
      D5.S0.Tower.GoldenPeriodic.EnumerationTen.goldenPeriodicOrbitRepresentativesTen,
      D5.S0.Tower.GoldenPeriodic.EnumerationNine.goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem_twelve orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded_twelve orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelve
