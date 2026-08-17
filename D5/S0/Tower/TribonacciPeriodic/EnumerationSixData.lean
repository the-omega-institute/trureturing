/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSixData
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSixData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five exact primitive period-six Tribonacci orbit certificates. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSixData

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

local notation "makeOrbit" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit
local notation "orbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates
local notation "traceCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode
local notation "applyStepsCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode
local notation "applyStepCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode
local notation "codedOrbitValid" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedOrbitValid
local notation "codedTraceValid" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedTraceValid
local notation "codedStateInGap" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStateInGap
local notation "codedStepValid" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStepValid
local notation "oldRepresentatives" =>
  tribonacciPeriodicOrbitRepresentativesFive
local notation "inversePolynomial" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial

abbrev CodedOrbit :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.TribonacciCodedOrbit

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen complete Tribonacci enumeration through
     period five and the incremental golden certificates on `harness/r105a`.
   * Pinned mathlib supplies finite-list disjointness and exact real
     inequalities. No existing theorem specializes them to period six here.
   * The five words below are the primitive rotation classes among the thirty
     new phase-marked solutions of the thirty-nine period-six equations. -/

def tribonacciPeriodSixOrbitA : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    []

def tribonacciPeriodSixOrbitB : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough]
    []

def tribonacciPeriodSixOrbitC : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft]
    []

def tribonacciPeriodSixOrbitD : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough]
    [.largeLeft]

def tribonacciPeriodSixOrbitE : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft]
    [.largeLeft]

def tribonacciPeriodicOrbitRepresentativesExactlySix : List CodedOrbit :=
  [tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE]

def tribonacciPeriodicOrbitRepresentativesSix : List CodedOrbit :=
  oldRepresentatives ++ tribonacciPeriodicOrbitRepresentativesExactlySix

theorem tribonacci_new_periodic_orbit_count_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.length = 5 := by
  rfl

theorem tribonacci_new_periodic_orbit_lengths_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.map
      (fun orbit => orbit.steps.length) = [6, 6, 6, 6, 6] := by
  rfl

theorem tribonacci_new_periodic_orbit_codes_close_and_are_nodup_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.Forall fun orbit =>
      applyStepsCode orbit.start orbit.steps = orbit.start /\
        (orbitStates orbit).Nodup := by
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

theorem tribonacci_new_periodic_orbit_low_states_mem_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode]

theorem tribonacci_period_six_orbits_ab_valid :
    codedOrbitValid tribonacciPeriodSixOrbitA /\
      codedOrbitValid tribonacciPeriodSixOrbitB := by
  norm_num [tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedOrbitValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedTraceValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStateInGap,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStepValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbits_cd_valid :
    codedOrbitValid tribonacciPeriodSixOrbitC /\
      codedOrbitValid tribonacciPeriodSixOrbitD := by
  norm_num [tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedOrbitValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedTraceValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStateInGap,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStepValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_six_orbit_e_valid :
    codedOrbitValid tribonacciPeriodSixOrbitE := by
  norm_num [tribonacciPeriodSixOrbitE,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedOrbitValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedTraceValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStateInGap,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciCodedStepValid,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_new_periodic_orbit_representatives_valid_six :
    tribonacciPeriodicOrbitRepresentativesExactlySix.Forall codedOrbitValid := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlySix, List.forall_cons]
  exact ⟨tribonacci_period_six_orbits_ab_valid.1,
    tribonacci_period_six_orbits_ab_valid.2,
    tribonacci_period_six_orbits_cd_valid.1,
    tribonacci_period_six_orbits_cd_valid.2,
    tribonacci_period_six_orbit_e_valid, by simp⟩

theorem tribonacci_new_periodic_orbit_state_codes_nodup_six :
    (tribonacciPeriodicOrbitRepresentativesExactlySix.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

def tribonacciEnumeratedOrbitStatesSix :=
  (tribonacciPeriodicOrbitRepresentativesSix.flatMap orbitStates).toFinset

end D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
