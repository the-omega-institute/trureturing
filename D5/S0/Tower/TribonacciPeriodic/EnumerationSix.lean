/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSix
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-six Tribonacci enumeration with unchanged maximin. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSix

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicCompleteness
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "transition" => tribonacciPeriodicTransition
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

abbrev CodedState := TribonacciCodedState
abbrev PeriodicState := TribonacciPeriodicState
abbrev CodedOrbit := TribonacciCodedOrbit

def tribonacciInheritedPointCodesSix : Finset CodedState :=
  (tribonacciPeriodSixInheritedOrbits.flatMap orbitStates).toFinset

def tribonacciNewOrbitStatesSix : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesExactlySix.flatMap orbitStates).toFinset

theorem tribonacci_expected_point_codes_six_decompose :
    tribonacciExpectedPointCodesSix =
      tribonacciInheritedPointCodesSix ∪ tribonacciNewOrbitStatesSix := by
  rw [tribonacciExpectedPointCodesSix,
    tribonacciPeriodicOrbitRepresentativesAtSix, List.flatMap_append,
    List.toFinset_append]
  rfl

theorem tribonacci_inherited_point_codes_six_subset_five :
    tribonacciInheritedPointCodesSix ⊆ tribonacciPeriodicPointCodesFive := by
  intro code hcode
  rw [← tribonacci_enumerated_orbit_states_eq_fixed_points,
    tribonacciEnumeratedOrbitStatesFive]
  simp only [tribonacciInheritedPointCodesSix, List.mem_toFinset] at hcode ⊢
  simp only [tribonacciPeriodSixInheritedOrbits,
    tribonacciPeriodicOrbitRepresentativesFive, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.mem_append] at hcode ⊢
  tauto

theorem tribonacci_prior_union_fixed_points_six :
    tribonacciPeriodicPointCodesFive ∪
        (tribonacciFixedPointCodes 6).toFinset =
      tribonacciPeriodicPointCodesFive ∪ tribonacciNewOrbitStatesSix := by
  rw [tribonacci_fixed_point_codes_six_decompose,
    tribonacci_expected_point_codes_six_decompose]
  apply Finset.ext
  intro code
  simp only [Finset.mem_union]
  constructor
  · rintro (hprior | hinherited | hnew)
    · exact Or.inl hprior
    · exact Or.inl (tribonacci_inherited_point_codes_six_subset_five hinherited)
    · exact Or.inr hnew
  · rintro (hprior | hnew)
    · exact Or.inl hprior
    · exact Or.inr (Or.inr hnew)

/-- The fifteen explicit cycles contain exactly all fixed-point codes through
period six. -/
theorem tribonacci_enumerated_orbit_states_eq_fixed_points_six :
    tribonacciEnumeratedOrbitStatesSix = tribonacciPeriodicPointCodesSix := by
  rw [tribonacciEnumeratedOrbitStatesSix,
    tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.toFinset_append]
  change tribonacciEnumeratedOrbitStatesFive ∪ tribonacciNewOrbitStatesSix =
    tribonacciPeriodicPointCodesSix
  rw [tribonacci_enumerated_orbit_states_eq_fixed_points,
    tribonacciPeriodicPointCodesSix, tribonacci_prior_union_fixed_points_six]

theorem tribonacci_periodic_orbit_representatives_valid_six :
    tribonacciPeriodicOrbitRepresentativesSix.Forall
      tribonacciCodedOrbitValid := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_representatives_valid,
    tribonacci_new_periodic_orbit_representatives_valid_six⟩

theorem tribonacci_periodic_orbit_low_states_mem_six :
    tribonacciPeriodicOrbitRepresentativesSix.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem,
    tribonacci_new_periodic_orbit_low_states_mem_six⟩

theorem tribonacci_new_periodic_state_count_six :
    tribonacciNewOrbitStatesSix.card = 30 := by
  rw [tribonacciNewOrbitStatesSix,
    List.toFinset_card_of_nodup
      tribonacci_new_periodic_orbit_state_codes_nodup_six]
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode]

/-- Five new primitive cycles contribute thirty phases, for fifteen cycles
and sixty-seven distinct periodic phase states in total. -/
theorem tribonacci_periodic_code_partition_six :
    tribonacciPeriodicOrbitRepresentativesSix.length = 15 /\
      tribonacciEnumeratedOrbitStatesSix.card = 67 := by
  constructor
  · norm_num [tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive,
      tribonacciPeriodicOrbitRepresentativesExactlySix]
  · rw [tribonacciEnumeratedOrbitStatesSix,
      List.toFinset_card_of_nodup
        tribonacci_periodic_orbit_state_codes_nodup_six]
    rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
      List.length_append]
    have hold :
        (tribonacciPeriodicOrbitRepresentativesFive.flatMap orbitStates).length =
          37 := by
      rw [← List.toFinset_card_of_nodup
        tribonacci_periodic_orbit_state_codes_nodup]
      exact tribonacci_periodic_orbit_partition_five.2
    have hnew :
        (tribonacciPeriodicOrbitRepresentativesExactlySix.flatMap
          orbitStates).length = 30 := by
      rw [← List.toFinset_card_of_nodup
        tribonacci_new_periodic_orbit_state_codes_nodup_six]
      exact tribonacci_new_periodic_state_count_six
    omega

/-- Every real state fixed by a nonzero iterate of period at most six occurs
on one of the fifteen decoded cycles. -/
theorem tribonacci_periodic_orbit_enumeration_complete_six {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 6)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesSix,
      state ∈ decodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    tribonacci_periodic_point_enumeration_complete_six
      hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ tribonacciEnumeratedOrbitStatesSix := by
    rw [tribonacci_enumerated_orbit_states_eq_fixed_points_six]
    exact hcode
  rw [tribonacciEnumeratedOrbitStatesSix, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [tribonacciDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

theorem tribonacci_period_six_orbit_a_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSixOrbitA.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState tribonacciPeriodSixOrbitA.lowState).coordinate :=
      min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSixOrbitA, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget,
        tribonacciCodeDiv, tribonacciCodeInv, tribonacciCodeNorm,
        tribonacciCodeCofactorZero, tribonacciCodeCofactorOne,
        tribonacciCodeCofactorTwo, tribonacciCodeSub, tribonacciCodeNeg,
        tribonacciCodeAdd, tribonacciCodeMul, tribonacciCodeOne,
        tribonacciCodeZero, tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbit_b_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSixOrbitB.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState tribonacciPeriodSixOrbitB.lowState).coordinate :=
      min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSixOrbitB, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget,
        tribonacciCodeDiv, tribonacciCodeInv, tribonacciCodeNorm,
        tribonacciCodeCofactorZero, tribonacciCodeCofactorOne,
        tribonacciCodeCofactorTwo, tribonacciCodeSub, tribonacciCodeNeg,
        tribonacciCodeAdd, tribonacciCodeMul, tribonacciCodeOne,
        tribonacciCodeZero, tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbit_c_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSixOrbitC.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState tribonacciPeriodSixOrbitC.lowState).coordinate :=
      min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSixOrbitC, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget,
        tribonacciCodeDiv, tribonacciCodeInv, tribonacciCodeNorm,
        tribonacciCodeCofactorZero, tribonacciCodeCofactorOne,
        tribonacciCodeCofactorTwo, tribonacciCodeSub, tribonacciCodeNeg,
        tribonacciCodeAdd, tribonacciCodeMul, tribonacciCodeOne,
        tribonacciCodeZero, tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbit_d_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSixOrbitD.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSixOrbitD.lowState).kind -
        (decodeTribonacciState tribonacciPeriodSixOrbitD.lowState).coordinate :=
      min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSixOrbitD, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbit_e_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSixOrbitE.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSixOrbitE.lowState).kind -
        (decodeTribonacciState tribonacciPeriodSixOrbitE.lowState).coordinate :=
      min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSixOrbitE, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_new_periodic_orbit_low_arms_bounded_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlySix,
    List.forall_cons]
  exact ⟨tribonacci_period_six_orbit_a_low_arm,
    tribonacci_period_six_orbit_b_low_arm,
    tribonacci_period_six_orbit_c_low_arm,
    tribonacci_period_six_orbit_d_low_arm,
    tribonacci_period_six_orbit_e_low_arm, by simp⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_six :
    tribonacciPeriodicOrbitRepresentativesSix.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded,
    tribonacci_new_periodic_orbit_low_arms_bounded_six⟩

def tribonacciPeriodicOrbitMinimaSix : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesSix,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-six enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit. -/
theorem tribonacci_periodic_orbit_maximin_six :
    IsGreatest tribonacciPeriodicOrbitMinimaSix (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_six orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_six orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodic.EnumerationSix
