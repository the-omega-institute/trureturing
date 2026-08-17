/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The complete finite Tribonacci enumeration has the champion period-two maximin. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicCompleteness

namespace D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "representatives" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive
local notation "championOrbit" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit
local notation "decodedOrbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciDecodedOrbitStates
local notation "orbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates
local notation "championValue" =>
  D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue
local notation "makeOrbit" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit
local notation "traceCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode
local notation "applyStepsCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode
local notation "applyStepCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode
local notation "inversePolynomial" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial
local notation "gapLength" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength
local notation "decodeState" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState

abbrev PeriodicState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState

abbrev CodedOrbit :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.TribonacciCodedOrbit

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen champion value and its period-two
     real-line realization. The imported enumeration supplies all ten finite
     cycles and selected low states.
   * Pinned mathlib supplies finite minima and elementary real inequalities;
     no external Tribonacci maximin theorem is used. -/

noncomputable def tribonacciPeriodicStateArm (state : PeriodicState) : Real :=
  min state.coordinate (gapLength state.kind - state.coordinate)

def TribonacciOrbitMinimum (orbit : CodedOrbit) (value : Real) : Prop :=
  (∀ state ∈ decodedOrbitStates orbit, value ≤ tribonacciPeriodicStateArm state) ∧
    ∃ state ∈ decodedOrbitStates orbit, tribonacciPeriodicStateArm state = value

def tribonacciPeriodicOrbitMinimaFive : Set Real :=
  {value | ∃ orbit ∈ representatives, TribonacciOrbitMinimum orbit value}

theorem tribonacci_periodic_orbit_low_states_mem :
    (representatives).Forall fun orbit => orbit.lowState ∈ orbitStates orbit := by
  norm_num [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode]

set_option maxHeartbeats 1000000 in
-- The ten selected low-arm comparisons expand exact cubic coordinates.
/-- Every selected low state has arm at most the frozen champion value. -/
theorem tribonacci_periodic_orbit_low_arms_bounded :
    (representatives).Forall fun orbit =>
      tribonacciPeriodicStateArm
          (decodeState orbit.lowState) ≤ championValue t := by
  rw [D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue_tribonacciConstant,
    inversePolynomial]
  norm_num [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    tribonacciPeriodicStateArm,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeDiv,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeInv,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
    min_def, inversePolynomial]
  repeat' apply And.intro
  all_goals try split_ifs with h
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_champion_decoded_orbit_states :
    decodedOrbitStates championOrbit =
      [⟨.large, (t ^ 2 - t) / 2⟩, ⟨.combined, (t - 1) / 2⟩] := by
  norm_num [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciDecodedOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeDiv,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeInv,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
    inversePolynomial]
  constructor <;>
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]

/-- The `(ba)^infinity` period-two orbit attains the frozen champion value as
its minimum arm. -/
theorem tribonacci_champion_periodic_orbit_minimum :
    TribonacciOrbitMinimum championOrbit (championValue t) := by
  rw [TribonacciOrbitMinimum, tribonacci_champion_decoded_orbit_states,
    D5.S0.Tower.DBonacciGeneral.ChampionValue.championValue_tribonacciConstant,
    inversePolynomial]
  constructor
  · intro state hstate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstate
    rcases hstate with rfl | rfl
    · norm_num [tribonacciPeriodicStateArm,
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
        min_def, inversePolynomial]
      try split_ifs with h
      all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant]
    · norm_num [tribonacciPeriodicStateArm,
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
        min_def, inversePolynomial]
      try split_ifs with h
      all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant]
  · refine ⟨⟨.large, (t ^ 2 - t) / 2⟩, by simp, ?_⟩
    norm_num [tribonacciPeriodicStateArm,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      min_def, inversePolynomial]
    try split_ifs with h
    all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
      D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant]

/-- The complete P-at-most-five enumeration has maximin exactly the frozen
`championValue t = (1 - t^-1)/2`, attained by `(ba)^infinity`. -/
theorem tribonacci_periodic_orbit_maximin_five :
    IsGreatest tribonacciPeriodicOrbitMinimaFive (championValue t) := by
  constructor
  · refine ⟨championOrbit, ?_, tribonacci_champion_periodic_orbit_minimum⟩
    simp [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem orbit horbit
    have hlowDecoded :
        decodeState orbit.lowState ∈ decodedOrbitStates orbit := by
      rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciDecodedOrbitStates,
        List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
