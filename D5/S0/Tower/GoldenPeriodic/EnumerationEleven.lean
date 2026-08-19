/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationEleven
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationEleven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-eleven enumeration for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationElevenFixed

namespace D5.S0.Tower.GoldenPeriodic.EnumerationEleven

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationTen
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenDistinct
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenDisjoint
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenSeparation
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenFixed

/- Library-search audit (2026-08-17): the repository has the frozen P <= 10
certificate but no P = 11 extension; no pinned library theorem specializes the
finite-list and rational-arithmetic kernels to this golden transition. -/

def goldenPeriodicOrbitRepresentativesEleven : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesTen ++
    goldenPeriodicOrbitRepresentativesExactlyEleven

def goldenPeriodicPointCodesEleven : Finset GoldenCodedState :=
  goldenPeriodicPointCodesTen ∪ (goldenFixedPointCodes 11).toFinset

theorem golden_fixed_point_code_count_exactly_eleven :
    (goldenFixedPointCodes 11).length = 199 := by
  rw [golden_fixed_point_codes_eleven_split]
  simp only [List.length_append]
  have hcounts := golden_fixed_point_block_counts_eleven
  omega

def goldenClosedItinerariesBlockEleven
    (start finish source : GoldenGapKind) (initialSteps : List GoldenPeriodicStep)
    (depth : Nat) : List (GoldenGapKind × List GoldenPeriodicStep) :=
  (goldenPathsFrom source depth).filterMap fun path =>
    if path.2 = finish then some (start, initialSteps ++ path.1) else none

def goldenClosedItineraryDenominatorNonzeroEleven
    (itinerary : GoldenGapKind × List GoldenPeriodicStep) : Prop :=
  goldenCodeNorm
    (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0

theorem golden_closed_itineraries_eleven_split :
    goldenClosedItineraries 11 =
      goldenClosedItinerariesBlockEleven .large .large .large
          [.left, .left, .left, .left] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .small
          [.left, .left, .left, .right] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .small
          [.left, .left, .right] 8 ++
      goldenClosedItinerariesBlockEleven .large .large .large
          [.left, .right, .through, .left] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .small
          [.left, .right, .through, .right] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .large
          [.right, .through, .left, .left] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .small
          [.right, .through, .left, .right] 7 ++
      goldenClosedItinerariesBlockEleven .large .large .small
          [.right, .through, .right] 8 ++
      goldenClosedItinerariesBlockEleven .small .small .large
          [.through, .left, .left, .left] 7 ++
      goldenClosedItinerariesBlockEleven .small .small .small
          [.through, .left, .left, .right] 7 ++
      goldenClosedItinerariesBlockEleven .small .small .small
          [.through, .left, .right] 8 ++
      goldenClosedItinerariesBlockEleven .small .small .large
          [.through, .right, .through, .left] 7 ++
      goldenClosedItinerariesBlockEleven .small .small .small
          [.through, .right, .through, .right] 7 := by
  rw [goldenClosedItineraries, golden_paths_from_large_eleven_split,
    golden_paths_from_small_eleven_split]
  simp_rw [golden_paths_from_large_succ 7]
  simp [goldenClosedItinerariesBlockEleven, List.filterMap_append,
    List.filterMap_map, List.append_assoc]

theorem golden_closed_itinerary_denominator_large_llll_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .large
      [.left, .left, .left, .left] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_lllr_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .small
      [.left, .left, .left, .right] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_llr_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .small
      [.left, .left, .right] 8).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_lrtl_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .large
      [.left, .right, .through, .left] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_lrtr_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .small
      [.left, .right, .through, .right] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_rtll_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .large
      [.right, .through, .left, .left] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_rtlr_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .small
      [.right, .through, .left, .right] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_large_rtr_eleven :
    (goldenClosedItinerariesBlockEleven .large .large .small
      [.right, .through, .right] 8).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_small_tlll_eleven :
    (goldenClosedItinerariesBlockEleven .small .small .large
      [.through, .left, .left, .left] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_small_tllr_eleven :
    (goldenClosedItinerariesBlockEleven .small .small .small
      [.through, .left, .left, .right] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_small_tlr_eleven :
    (goldenClosedItinerariesBlockEleven .small .small .small
      [.through, .left, .right] 8).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_small_trtl_eleven :
    (goldenClosedItinerariesBlockEleven .small .small .large
      [.through, .right, .through, .left] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominator_small_trtr_eleven :
    (goldenClosedItinerariesBlockEleven .small .small .small
      [.through, .right, .through, .right] 7).Forall
        goldenClosedItineraryDenominatorNonzeroEleven := by
  simp [goldenClosedItinerariesBlockEleven,
    goldenClosedItineraryDenominatorNonzeroEleven, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_closed_itinerary_denominators_exactly_eleven :
    (goldenClosedItineraries 11).Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  change (goldenClosedItineraries 11).Forall
    goldenClosedItineraryDenominatorNonzeroEleven
  rw [golden_closed_itineraries_eleven_split]
  have appendForall {xs ys : List (GoldenGapKind × List GoldenPeriodicStep)}
      (hxs : xs.Forall goldenClosedItineraryDenominatorNonzeroEleven)
      (hys : ys.Forall goldenClosedItineraryDenominatorNonzeroEleven) :
      (xs ++ ys).Forall goldenClosedItineraryDenominatorNonzeroEleven :=
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
                          golden_closed_itinerary_denominator_large_llll_eleven
                          golden_closed_itinerary_denominator_large_lllr_eleven)
                        golden_closed_itinerary_denominator_large_llr_eleven)
                      golden_closed_itinerary_denominator_large_lrtl_eleven)
                    golden_closed_itinerary_denominator_large_lrtr_eleven)
                  golden_closed_itinerary_denominator_large_rtll_eleven)
                golden_closed_itinerary_denominator_large_rtlr_eleven)
              golden_closed_itinerary_denominator_large_rtr_eleven)
            golden_closed_itinerary_denominator_small_tlll_eleven)
          golden_closed_itinerary_denominator_small_tllr_eleven)
        golden_closed_itinerary_denominator_small_tlr_eleven)
      golden_closed_itinerary_denominator_small_trtl_eleven)
    golden_closed_itinerary_denominator_small_trtr_eleven

theorem golden_periodic_point_enumeration_complete_exactly_eleven
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[11]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesEleven, state = decodeGoldenState code := by
  let steps := goldenActualSteps 11 state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries 11 := by
    exact golden_actual_steps_mem_closed hperiod
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp
      golden_closed_itinerary_denominators_exactly_eleven (state.kind, steps) hitinerary
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[11]) state).coordinate :=
        golden_actual_steps_coordinate 11 state
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
  have hcode : code ∈ goldenPeriodicPointCodesEleven := by
    rw [goldenPeriodicPointCodesEleven, Finset.mem_union]
    right
    rw [List.mem_toFinset]
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

theorem golden_periodic_point_enumeration_complete_eleven {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 11)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesEleven, state = decodeGoldenState code := by
  by_cases hperiodTen : period ≤ 10
  · obtain ⟨code, hcode, hstate⟩ :=
      golden_periodic_point_enumeration_complete_ten
        hperiodPos hperiodTen state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hstate⟩
  · have hperiodEleven : period = 11 := by omega
    subst period
    exact golden_periodic_point_enumeration_complete_exactly_eleven state hperiod

theorem golden_periodic_orbit_representatives_valid_eleven :
    goldenPeriodicOrbitRepresentativesEleven.Forall goldenCodedOrbitValid := by
  rw [goldenPeriodicOrbitRepresentativesEleven, List.forall_append]
  exact ⟨golden_periodic_orbit_representatives_valid_ten,
    golden_new_periodic_orbit_representatives_valid_eleven⟩

def goldenEnumeratedOrbitStatesEleven : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates).toFinset

theorem golden_periodic_orbit_state_codes_nodup_eleven :
    (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates).Nodup := by
  rw [goldenPeriodicOrbitRepresentativesEleven, List.flatMap_append,
    List.nodup_append']
  exact ⟨golden_periodic_orbit_state_codes_nodup_ten,
    golden_new_periodic_orbit_state_codes_nodup_eleven,
    golden_old_new_periodic_orbit_state_codes_disjoint_eleven⟩

theorem golden_inherited_point_codes_eleven_subset_seven :
    goldenInheritedPointCodesEleven ⊆ goldenPeriodicPointCodesSeven := by
  intro code hcode
  simp only [goldenInheritedPointCodesEleven, List.mem_toFinset,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcode
  obtain ⟨period, hperiod, hcode⟩ := hcode
  rw [goldenPeriodicPointCodesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap]
  rcases hperiod with rfl | hperiod
  · exact ⟨0, List.mem_range.mpr (by omega), by simpa using hcode⟩

theorem golden_inherited_point_codes_eleven_subset_ten :
    goldenInheritedPointCodesEleven ⊆ goldenPeriodicPointCodesTen := by
  intro code hcode
  rw [goldenPeriodicPointCodesTen, Finset.mem_union]
  rw [D5.S0.Tower.GoldenPeriodic.EnumerationNine.goldenPeriodicPointCodesNine,
    Finset.mem_union]
  rw [goldenPeriodicPointCodesEight, Finset.mem_union]
  exact Or.inl (Or.inl
    (Or.inl (golden_inherited_point_codes_eleven_subset_seven hcode)))

theorem golden_prior_union_fixed_points_eleven :
    goldenPeriodicPointCodesTen ∪ (goldenFixedPointCodes 11).toFinset =
      goldenPeriodicPointCodesTen ∪ goldenNewOrbitStatesEleven := by
  rw [golden_fixed_point_codes_eleven_decompose, goldenExpectedPointCodesEleven]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (golden_inherited_point_codes_eleven_subset_ten hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

theorem golden_enumerated_orbit_states_eq_fixed_points_eleven :
    goldenEnumeratedOrbitStatesEleven = goldenPeriodicPointCodesEleven := by
  rw [goldenEnumeratedOrbitStatesEleven, goldenPeriodicOrbitRepresentativesEleven,
    List.flatMap_append, List.toFinset_append]
  change goldenEnumeratedOrbitStatesTen ∪ goldenNewOrbitStatesEleven =
    goldenPeriodicPointCodesEleven
  rw [golden_enumerated_orbit_states_eq_fixed_points_ten,
    goldenPeriodicPointCodesEleven]
  exact golden_prior_union_fixed_points_eleven.symm

theorem golden_periodic_point_code_count_eleven :
    goldenPeriodicPointCodesEleven.card = 480 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points_eleven,
    goldenEnumeratedOrbitStatesEleven,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup_eleven]
  rw [goldenPeriodicOrbitRepresentativesEleven, List.flatMap_append,
    List.length_append]
  have hold :
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates).length =
        282 := by
    rw [← List.toFinset_card_of_nodup
      golden_periodic_orbit_state_codes_nodup_ten]
    exact golden_periodic_code_partition_ten.2
  have hnew :
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates).length = 198 := by
    simp only [List.length_flatMap, goldenOrbitStates,
      golden_trace_code_length]
    rw [golden_new_periodic_orbit_lengths_eleven]
    norm_num
  omega

theorem golden_periodic_code_partition_eleven :
    goldenPeriodicOrbitRepresentativesEleven.length = 54 ∧
      goldenEnumeratedOrbitStatesEleven.card = 480 := by
  constructor
  · rw [goldenPeriodicOrbitRepresentativesEleven, List.length_append]
    have hold := golden_periodic_code_partition_ten.1
    have hnew := golden_new_periodic_orbit_count_eleven
    omega
  · rw [golden_enumerated_orbit_states_eq_fixed_points_eleven]
    exact golden_periodic_point_code_count_eleven

theorem golden_periodic_orbit_enumeration_complete_eleven {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 11)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesEleven,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete_eleven
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesEleven := by
    rw [golden_enumerated_orbit_states_eq_fixed_points_eleven]
    exact hcode
  rw [goldenEnumeratedOrbitStatesEleven, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem golden_periodic_orbit_low_states_mem_eleven :
    goldenPeriodicOrbitRepresentativesEleven.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  rw [goldenPeriodicOrbitRepresentativesEleven, List.forall_append]
  exact ⟨golden_periodic_orbit_low_states_mem_ten,
    golden_new_periodic_orbit_low_states_mem_eleven⟩

theorem golden_periodic_orbit_low_arms_bounded_eleven :
    goldenPeriodicOrbitRepresentativesEleven.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  rw [goldenPeriodicOrbitRepresentativesEleven, List.forall_append]
  exact ⟨golden_periodic_orbit_low_arms_bounded_ten,
    golden_new_periodic_orbit_low_arms_bounded_eleven⟩

def goldenPeriodicOrbitMinimaEleven : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesEleven,
    GoldenOrbitMinimum orbit value}

theorem golden_periodic_orbit_minimum_exists_eleven (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesEleven) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp
    golden_periodic_orbit_low_states_mem_eleven orbit horbit
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

theorem golden_periodic_orbit_maximin_eleven :
    IsGreatest goldenPeriodicOrbitMinimaEleven goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesEleven,
      goldenPeriodicOrbitRepresentativesTen,
      D5.S0.Tower.GoldenPeriodic.EnumerationNine.goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem_eleven orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded_eleven orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.GoldenPeriodic.EnumerationEleven
