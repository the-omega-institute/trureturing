/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationTen
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationTen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-ten enumeration for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationTenFixed

namespace D5.S0.Tower.GoldenPeriodic.EnumerationTen

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTenFixed

/- Library-search audit (2026-08-17): the repository has the frozen P <= 9
certificate but no P = 10 extension; no pinned library theorem specializes the
finite-list and rational-arithmetic kernels to this golden transition. -/

def goldenPeriodicOrbitRepresentativesTen : List GoldenCodedOrbit :=
  goldenPeriodicOrbitRepresentativesNine ++
    goldenPeriodicOrbitRepresentativesExactlyTen

def goldenPeriodicPointCodesTen : Finset GoldenCodedState :=
  goldenPeriodicPointCodesNine ∪ (goldenFixedPointCodes 10).toFinset

theorem golden_fixed_point_code_count_exactly_ten :
    (goldenFixedPointCodes 10).length = 123 := by
  rw [golden_fixed_point_codes_ten_split]
  simp only [List.length_append]
  have hcounts := golden_fixed_point_block_counts_ten
  omega

theorem golden_closed_itinerary_denominators_exactly_ten :
    (goldenClosedItineraries 10).Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  simp [List.map_cons, List.map_nil, List.filterMap_nil,
    goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
    goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_periodic_point_enumeration_complete_exactly_ten
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[10]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesTen, state = decodeGoldenState code := by
  let steps := goldenActualSteps 10 state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries 10 := by
    exact golden_actual_steps_mem_closed hperiod
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp
      golden_closed_itinerary_denominators_exactly_ten (state.kind, steps) hitinerary
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[10]) state).coordinate :=
        golden_actual_steps_coordinate 10 state
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
  have hcode : code ∈ goldenPeriodicPointCodesTen := by
    rw [goldenPeriodicPointCodesTen, Finset.mem_union]
    right
    rw [List.mem_toFinset]
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

theorem golden_periodic_point_enumeration_complete_ten {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 10)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesTen, state = decodeGoldenState code := by
  by_cases hperiodNine : period ≤ 9
  · obtain ⟨code, hcode, hstate⟩ :=
      golden_periodic_point_enumeration_complete_nine
        hperiodPos hperiodNine state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hstate⟩
  · have hperiodTen : period = 10 := by omega
    subst period
    exact golden_periodic_point_enumeration_complete_exactly_ten state hperiod

theorem golden_periodic_orbit_representatives_valid_ten :
    goldenPeriodicOrbitRepresentativesTen.Forall goldenCodedOrbitValid := by
  rw [goldenPeriodicOrbitRepresentativesTen, List.forall_append]
  exact ⟨golden_periodic_orbit_representatives_valid_nine,
    golden_new_periodic_orbit_representatives_valid_ten⟩

def goldenEnumeratedOrbitStatesTen : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates).toFinset

theorem golden_periodic_orbit_state_codes_nodup_ten :
    (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates).Nodup := by
  rw [goldenPeriodicOrbitRepresentativesTen, List.flatMap_append,
    List.nodup_append']
  exact ⟨golden_periodic_orbit_state_codes_nodup_nine,
    golden_new_periodic_orbit_state_codes_nodup_ten,
    golden_old_new_periodic_orbit_state_codes_disjoint_ten⟩

theorem golden_inherited_point_codes_ten_subset_seven :
    goldenInheritedPointCodesTen ⊆ goldenPeriodicPointCodesSeven := by
  intro code hcode
  simp only [goldenInheritedPointCodesTen, List.mem_toFinset,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcode
  obtain ⟨period, hperiod, hcode⟩ := hcode
  rw [goldenPeriodicPointCodesSeven, List.mem_toFinset]
  simp only [List.mem_flatMap]
  rcases hperiod with rfl | rfl | rfl
  · exact ⟨0, List.mem_range.mpr (by omega), by simpa using hcode⟩
  · exact ⟨1, List.mem_range.mpr (by omega), by simpa using hcode⟩
  · exact ⟨4, List.mem_range.mpr (by omega), by simpa using hcode⟩

theorem golden_inherited_point_codes_ten_subset_nine :
    goldenInheritedPointCodesTen ⊆ goldenPeriodicPointCodesNine := by
  intro code hcode
  rw [goldenPeriodicPointCodesNine, Finset.mem_union]
  rw [goldenPeriodicPointCodesEight, Finset.mem_union]
  exact Or.inl (Or.inl (golden_inherited_point_codes_ten_subset_seven hcode))

theorem golden_prior_union_fixed_points_ten :
    goldenPeriodicPointCodesNine ∪ (goldenFixedPointCodes 10).toFinset =
      goldenPeriodicPointCodesNine ∪ goldenNewOrbitStatesTen := by
  rw [golden_fixed_point_codes_ten_decompose, goldenExpectedPointCodesTen]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (golden_inherited_point_codes_ten_subset_nine hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

theorem golden_enumerated_orbit_states_eq_fixed_points_ten :
    goldenEnumeratedOrbitStatesTen = goldenPeriodicPointCodesTen := by
  rw [goldenEnumeratedOrbitStatesTen, goldenPeriodicOrbitRepresentativesTen,
    List.flatMap_append, List.toFinset_append]
  change goldenEnumeratedOrbitStatesNine ∪ goldenNewOrbitStatesTen =
    goldenPeriodicPointCodesTen
  rw [golden_enumerated_orbit_states_eq_fixed_points_nine,
    goldenPeriodicPointCodesTen]
  exact golden_prior_union_fixed_points_ten.symm

theorem golden_periodic_point_code_count_ten :
    goldenPeriodicPointCodesTen.card = 282 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points_ten,
    goldenEnumeratedOrbitStatesTen,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup_ten]
  rw [goldenPeriodicOrbitRepresentativesTen, List.flatMap_append,
    List.length_append]
  have hold :
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates).length =
        172 := by
    rw [← List.toFinset_card_of_nodup
      golden_periodic_orbit_state_codes_nodup_nine]
    exact golden_periodic_code_partition_nine.2
  have hnew :
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap
        goldenOrbitStates).length = 110 := by
    norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenOrbitStates,
      goldenTraceCode]
  omega

theorem golden_periodic_code_partition_ten :
    goldenPeriodicOrbitRepresentativesTen.length = 36 ∧
      goldenEnumeratedOrbitStatesTen.card = 282 := by
  constructor
  · norm_num [goldenPeriodicOrbitRepresentativesTen,
      goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven,
      goldenPeriodicOrbitRepresentativesExactlyEight,
      D5.S0.Tower.GoldenPeriodic.EnumerationNineData.goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodicOrbitRepresentativesExactlyTen]
  · rw [golden_enumerated_orbit_states_eq_fixed_points_ten]
    exact golden_periodic_point_code_count_ten

theorem golden_periodic_orbit_enumeration_complete_ten {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 10)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesTen,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete_ten
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesTen := by
    rw [golden_enumerated_orbit_states_eq_fixed_points_ten]
    exact hcode
  rw [goldenEnumeratedOrbitStatesTen, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem golden_periodic_orbit_low_states_mem_ten :
    goldenPeriodicOrbitRepresentativesTen.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  rw [goldenPeriodicOrbitRepresentativesTen, List.forall_append]
  exact ⟨golden_periodic_orbit_low_states_mem_nine,
    golden_new_periodic_orbit_low_states_mem_ten⟩

theorem golden_periodic_orbit_low_arms_bounded_ten :
    goldenPeriodicOrbitRepresentativesTen.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  rw [goldenPeriodicOrbitRepresentativesTen, List.forall_append]
  exact ⟨golden_periodic_orbit_low_arms_bounded_nine,
    golden_new_periodic_orbit_low_arms_bounded_ten⟩

def goldenPeriodicOrbitMinimaTen : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesTen,
    GoldenOrbitMinimum orbit value}

theorem golden_periodic_orbit_minimum_exists_ten (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesTen) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp
    golden_periodic_orbit_low_states_mem_ten orbit horbit
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

theorem golden_periodic_orbit_maximin_ten :
    IsGreatest goldenPeriodicOrbitMinimaTen goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesTen,
      goldenPeriodicOrbitRepresentativesNine,
      goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem_ten orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded_ten orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.GoldenPeriodic.EnumerationTen
