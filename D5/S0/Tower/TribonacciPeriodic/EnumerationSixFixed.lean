/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSixFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-six generator equations equal the inherited and five new orbit states. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint

local notation "fixedPointCodes" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciFixedPointCodes
local notation "closedFrom" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedFrom
local notation "orbitStates" => tribonacciOrbitStates
local notation "makeOrbit" => tribonacciMakeOrbit
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition

abbrev Code :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciCubicCode

abbrev Affine :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciAffineCode

abbrev Step :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicStep

abbrev CodedState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciCodedState

abbrev PeriodicState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen reverse branch-word theorem and the
     exact cubic generator through period five.
   * Pinned mathlib supplies finite unions and function iteration. The common
     multiplier argument and the period-six finite equations are local. -/

def tribonacciMultiplyByRoot : Nat -> Code -> Code
  | 0, code => code
  | period + 1, code =>
      tribonacciMultiplyByRoot period
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeMul
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot
          code)

theorem tribonacci_path_affine_multiplier_aux (steps : List Step)
    (affine : Affine) :
    (steps.foldl (fun current step =>
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine
          step) current) affine).multiplier =
      tribonacciMultiplyByRoot steps.length affine.multiplier := by
  induction steps generalizing affine with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.foldl_cons, List.length_cons, tribonacciMultiplyByRoot]
      rw [ih]
      cases step <;> rfl

theorem tribonacci_closed_itinerary_denominator_six (steps : List Step)
    (hlength : steps.length = 6) :
    Ne (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNorm
      (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeSub
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine
          steps).multiplier)) 0 := by
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    tribonacci_path_affine_multiplier_aux, hlength]
  norm_num [tribonacciMultiplyByRoot,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNorm,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorZero,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorOne,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorTwo,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeSub,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNeg,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeAdd,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeMul,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeZero,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

theorem tribonacci_fixed_point_code_count_exactly_six :
    (fixedPointCodes 6).length = 39 := by
  decide

def tribonacciPeriodicPointCodesSix : Finset CodedState :=
  tribonacciPeriodicPointCodesFive ∪ (fixedPointCodes 6).toFinset

theorem tribonacci_periodic_point_enumeration_complete_exactly_six
    (state : PeriodicState) (hperiod : (transition^[6]) state = state) :
    ∃ code, code ∈ (fixedPointCodes 6).toFinset /\
      state =
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          code := by
  have hlength :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_actual_steps_length
      6 state
  have hnorm := tribonacci_closed_itinerary_denominator_six
    (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciActualSteps
      6 state) hlength
  obtain ⟨code, hcode, hdecode⟩ :=
    tribonacci_periodic_point_enumeration_complete state hperiod hnorm
  exact ⟨code, List.mem_toFinset.mpr hcode, hdecode⟩

theorem tribonacci_periodic_point_enumeration_complete_six {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period <= 6)
    (state : PeriodicState) (hperiod : (transition^[period]) state = state) :
    ∃ code, code ∈ tribonacciPeriodicPointCodesSix /\
      state =
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          code := by
  rcases lt_or_eq_of_le hperiodBound with hprior | rfl
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_five hperiodPos
        (by omega) state hperiod
    exact ⟨code, Finset.mem_union_left _ hcode, hdecode⟩
  · obtain ⟨code, hcode, hdecode⟩ :=
      tribonacci_periodic_point_enumeration_complete_exactly_six state hperiod
    exact ⟨code, Finset.mem_union_right _ hcode, hdecode⟩

def tribonacciPeriodSixInheritedOrbits : List TribonacciCodedOrbit :=
  [makeOrbit .large [.largeLeft] [], tribonacciChampionPeriodicOrbit,
    makeOrbit .small [.smallThrough, .largeRight, .combinedRight] [],
    makeOrbit .combined [.combinedLeft, .largeLeft, .largeRight] []]

def tribonacciPeriodicOrbitRepresentativesAtSix : List TribonacciCodedOrbit :=
  tribonacciPeriodSixInheritedOrbits ++
    tribonacciPeriodicOrbitRepresentativesExactlySix

def tribonacciExpectedPointCodesSix : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesAtSix.flatMap orbitStates).toFinset

theorem tribonacci_period_six_inherited_state_codes_nodup :
    (tribonacciPeriodSixInheritedOrbits.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodSixInheritedOrbits, tribonacciChampionPeriodicOrbit,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_six_inherited_new_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodSixInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodicOrbitRepresentativesExactlySix.flatMap orbitStates) := by
  rw [List.disjoint_left]
  intro code hinherited hnew
  have hold : code ∈
      (tribonacciPeriodicOrbitRepresentativesFive.flatMap orbitStates) := by
    simp only [tribonacciPeriodSixInheritedOrbits,
      tribonacciPeriodicOrbitRepresentativesFive, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_append] at hinherited ⊢
    tauto
  exact (List.disjoint_left.mp
    tribonacci_old_new_periodic_orbit_state_codes_disjoint_six hold) hnew

theorem tribonacci_period_six_expected_state_codes_nodup :
    (tribonacciPeriodicOrbitRepresentativesAtSix.flatMap orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesAtSix, List.flatMap_append,
    List.nodup_append']
  exact ⟨tribonacci_period_six_inherited_state_codes_nodup,
    tribonacci_new_periodic_orbit_state_codes_nodup_six,
    tribonacci_period_six_inherited_new_state_codes_disjoint⟩

theorem tribonacci_period_six_expected_point_code_count :
    tribonacciExpectedPointCodesSix.card = 39 := by
  rw [tribonacciExpectedPointCodesSix,
    List.toFinset_card_of_nodup
      tribonacci_period_six_expected_state_codes_nodup]
  norm_num [tribonacciPeriodicOrbitRepresentativesAtSix,
    tribonacciPeriodSixInheritedOrbits,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciChampionPeriodicOrbit,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode]

theorem tribonacci_inherited_orbit_states_subset_fixed_points_six :
    (tribonacciPeriodSixInheritedOrbits.flatMap orbitStates).toFinset ⊆
      (fixedPointCodes 6).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset] at hcode ⊢
  simp [tribonacciPeriodSixInheritedOrbits, tribonacciChampionPeriodicOrbit,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciFixedPointCodes, tribonacciClosedItineraries,
    tribonacciClosedFrom, tribonacciPathsFrom] at hcode ⊢
  norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot] at hcode ⊢
  tauto

set_option maxHeartbeats 800000 in
theorem tribonacci_orbit_states_subset_fixed_points_ab_six :
    (orbitStates tribonacciPeriodSixOrbitA).toFinset ⊆
        (fixedPointCodes 6).toFinset /\
      (orbitStates tribonacciPeriodSixOrbitB).toFinset ⊆
        (fixedPointCodes 6).toFinset := by
  constructor <;> intro code hcode <;>
    simp only [List.mem_toFinset] at hcode ⊢ <;>
    simp [tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
      tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
      tribonacciFixedPointCodes, tribonacciClosedItineraries,
      tribonacciClosedFrom, tribonacciPathsFrom] at hcode ⊢ <;>
    norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
      tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
      tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
      tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
      tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
      tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
      tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
      tribonacciCodeRoot] at hcode ⊢ <;>
    tauto

theorem tribonacci_orbit_states_subset_fixed_points_c_six :
    (orbitStates tribonacciPeriodSixOrbitC).toFinset ⊆
      (fixedPointCodes 6).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset] at hcode ⊢
  simp [tribonacciPeriodSixOrbitC, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciFixedPointCodes,
    tribonacciClosedItineraries, tribonacciClosedFrom,
    tribonacciPathsFrom] at hcode ⊢
  norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot] at hcode ⊢
  tauto

theorem tribonacci_orbit_states_subset_fixed_points_d_six :
    (orbitStates tribonacciPeriodSixOrbitD).toFinset ⊆
      (fixedPointCodes 6).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset] at hcode ⊢
  simp [tribonacciPeriodSixOrbitD, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciFixedPointCodes,
    tribonacciClosedItineraries, tribonacciClosedFrom,
    tribonacciPathsFrom] at hcode ⊢
  norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot] at hcode ⊢
  tauto

theorem tribonacci_orbit_states_subset_fixed_points_e_six :
    (orbitStates tribonacciPeriodSixOrbitE).toFinset ⊆
      (fixedPointCodes 6).toFinset := by
  intro code hcode
  simp only [List.mem_toFinset] at hcode ⊢
  simp [tribonacciPeriodSixOrbitE, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciFixedPointCodes,
    tribonacciClosedItineraries, tribonacciClosedFrom,
    tribonacciPathsFrom] at hcode ⊢
  norm_num [tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot] at hcode ⊢
  tauto

theorem tribonacci_new_orbit_states_subset_fixed_points_six :
    (tribonacciPeriodicOrbitRepresentativesExactlySix.flatMap
      orbitStates).toFinset ⊆ (fixedPointCodes 6).toFinset := by
  simpa only [tribonacciPeriodicOrbitRepresentativesExactlySix,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toFinset_append, Finset.union_subset_iff] using
      ⟨tribonacci_orbit_states_subset_fixed_points_ab_six.1,
        tribonacci_orbit_states_subset_fixed_points_ab_six.2,
        tribonacci_orbit_states_subset_fixed_points_c_six,
        tribonacci_orbit_states_subset_fixed_points_d_six,
        tribonacci_orbit_states_subset_fixed_points_e_six⟩

theorem tribonacci_expected_point_codes_subset_fixed_points_six :
    tribonacciExpectedPointCodesSix ⊆ (fixedPointCodes 6).toFinset := by
  rw [tribonacciExpectedPointCodesSix,
    tribonacciPeriodicOrbitRepresentativesAtSix, List.flatMap_append,
    List.toFinset_append, Finset.union_subset_iff]
  exact ⟨tribonacci_inherited_orbit_states_subset_fixed_points_six,
    tribonacci_new_orbit_states_subset_fixed_points_six⟩

theorem tribonacci_fixed_point_codes_six_decompose :
    (fixedPointCodes 6).toFinset = tribonacciExpectedPointCodesSix := by
  symm
  apply Finset.eq_of_subset_of_card_le
    tribonacci_expected_point_codes_subset_fixed_points_six
  calc
    (fixedPointCodes 6).toFinset.card ≤ (fixedPointCodes 6).length :=
      List.toFinset_card_le _
    _ = 39 := tribonacci_fixed_point_code_count_exactly_six
    _ = tribonacciExpectedPointCodesSix.card :=
      tribonacci_period_six_expected_point_code_count.symm

end D5.S0.Tower.TribonacciPeriodic.EnumerationSixFixed
