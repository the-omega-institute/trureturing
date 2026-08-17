/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ten exact primitive period-seven Tribonacci orbit certificates. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSix

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData

local notation "makeOrbit" => tribonacciMakeOrbit
local notation "orbitStates" => tribonacciOrbitStates
local notation "codedOrbitValid" => tribonacciCodedOrbitValid
local notation "oldRepresentatives" => tribonacciPeriodicOrbitRepresentativesSix

abbrev CodedOrbit := TribonacciCodedOrbit

/- The ten words below are the primitive rotation classes among the seventy
   new phase-marked solutions of the seventy-one period-seven equations. -/

def tribonacciPeriodSevenOrbitA : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodSevenOrbitB : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight]

def tribonacciPeriodSevenOrbitC : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight]

def tribonacciPeriodSevenOrbitD : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight]

def tribonacciPeriodSevenOrbitE : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodSevenOrbitF : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodSevenOrbitG : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodSevenOrbitH : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight]

def tribonacciPeriodSevenOrbitI : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft]

def tribonacciPeriodSevenOrbitJ : CodedOrbit :=
  makeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft]

def tribonacciPeriodicOrbitRepresentativesExactlySeven : List CodedOrbit :=
  [tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
    tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ]

def tribonacciPeriodicOrbitRepresentativesSeven : List CodedOrbit :=
  oldRepresentatives ++ tribonacciPeriodicOrbitRepresentativesExactlySeven

theorem tribonacci_new_periodic_orbit_count_seven :
    tribonacciPeriodicOrbitRepresentativesExactlySeven.length = 10 := by
  rfl

theorem tribonacci_new_periodic_orbit_lengths_seven :
    tribonacciPeriodicOrbitRepresentativesExactlySeven.map
      (fun orbit => orbit.steps.length) = [7, 7, 7, 7, 7, 7, 7, 7, 7, 7] := by
  rfl

theorem tribonacci_period_seven_orbits_ab_valid_and_nodup :
    (codedOrbitValid tribonacciPeriodSevenOrbitA /\
        (orbitStates tribonacciPeriodSevenOrbitA).Nodup) /\
      (codedOrbitValid tribonacciPeriodSevenOrbitB /\
        (orbitStates tribonacciPeriodSevenOrbitB).Nodup) := by
  norm_num [tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciMakeOrbit, tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode,
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
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbits_cd_valid_and_nodup :
    (codedOrbitValid tribonacciPeriodSevenOrbitC /\
        (orbitStates tribonacciPeriodSevenOrbitC).Nodup) /\
      (codedOrbitValid tribonacciPeriodSevenOrbitD /\
        (orbitStates tribonacciPeriodSevenOrbitD).Nodup) := by
  norm_num [tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciMakeOrbit, tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode,
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
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbits_ef_valid_and_nodup :
    (codedOrbitValid tribonacciPeriodSevenOrbitE /\
        (orbitStates tribonacciPeriodSevenOrbitE).Nodup) /\
      (codedOrbitValid tribonacciPeriodSevenOrbitF /\
        (orbitStates tribonacciPeriodSevenOrbitF).Nodup) := by
  norm_num [tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciMakeOrbit, tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode,
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
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbits_gh_valid_and_nodup :
    (codedOrbitValid tribonacciPeriodSevenOrbitG /\
        (orbitStates tribonacciPeriodSevenOrbitG).Nodup) /\
      (codedOrbitValid tribonacciPeriodSevenOrbitH /\
        (orbitStates tribonacciPeriodSevenOrbitH).Nodup) := by
  norm_num [tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
    tribonacciMakeOrbit, tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode,
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
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbits_ij_valid_and_nodup :
    (codedOrbitValid tribonacciPeriodSevenOrbitI /\
        (orbitStates tribonacciPeriodSevenOrbitI).Nodup) /\
      (codedOrbitValid tribonacciPeriodSevenOrbitJ /\
        (orbitStates tribonacciPeriodSevenOrbitJ).Nodup) := by
  norm_num [tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode,
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
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_new_periodic_orbit_representatives_valid_seven :
    tribonacciPeriodicOrbitRepresentativesExactlySeven.Forall
      codedOrbitValid := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    List.forall_cons]
  exact ⟨tribonacci_period_seven_orbits_ab_valid_and_nodup.1.1,
    tribonacci_period_seven_orbits_ab_valid_and_nodup.2.1,
    tribonacci_period_seven_orbits_cd_valid_and_nodup.1.1,
    tribonacci_period_seven_orbits_cd_valid_and_nodup.2.1,
    tribonacci_period_seven_orbits_ef_valid_and_nodup.1.1,
    tribonacci_period_seven_orbits_ef_valid_and_nodup.2.1,
    tribonacci_period_seven_orbits_gh_valid_and_nodup.1.1,
    tribonacci_period_seven_orbits_gh_valid_and_nodup.2.1,
    tribonacci_period_seven_orbits_ij_valid_and_nodup.1.1,
    tribonacci_period_seven_orbits_ij_valid_and_nodup.2.1, by simp⟩

theorem tribonacci_new_periodic_orbit_low_states_mem_seven :
    tribonacciPeriodicOrbitRepresentativesExactlySeven.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
    tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepsCode, tribonacciApplyStepCode]

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
