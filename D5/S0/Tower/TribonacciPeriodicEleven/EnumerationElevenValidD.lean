/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidD
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidD
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven orbits 59 through 74 are valid coded orbits with distinct states. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidC

/- Library-search audit trail (2026-08-18):
   * The tactic closure is the one the shorter levels use, reused verbatim.
   * The coded representation carries no Decidable instance, so `decide` is
     unavailable. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidD

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidA
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidB
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidC


theorem tribonacci_period_eleven_orbits_59_60_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit59 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit59).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit60 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit60).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit59, tribonacciPeriodElevenOrbit60,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_61_62_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit61 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit61).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit62 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit62).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit61, tribonacciPeriodElevenOrbit62,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_63_64_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit63 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit63).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit64 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit64).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit63, tribonacciPeriodElevenOrbit64,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_65_66_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit65 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit65).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit66 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit66).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit65, tribonacciPeriodElevenOrbit66,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_67_68_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit67 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit67).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit68 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit68).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit67, tribonacciPeriodElevenOrbit68,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_69_70_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit69 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit69).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit70 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit70).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit69, tribonacciPeriodElevenOrbit70,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_71_72_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit71 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit71).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit72 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit72).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit71, tribonacciPeriodElevenOrbit72,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_eleven_orbits_73_74_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit73 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit73).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodElevenOrbit74 /\
        (tribonacciOrbitStates tribonacciPeriodElevenOrbit74).Nodup) := by
  norm_num [tribonacciPeriodElevenOrbit73, tribonacciPeriodElevenOrbit74,
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
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

/-- All seventy-four primitive period-eleven representatives are valid. -/
theorem tribonacci_period_eleven_representatives_valid :
    tribonacciPeriodElevenOrbitRepresentatives.Forall tribonacciCodedOrbitValid := by
  simp only [tribonacciPeriodElevenOrbitRepresentatives, List.forall_cons]
  exact ⟨
    tribonacci_period_eleven_orbits_01_02_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_01_02_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_03_04_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_03_04_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_05_06_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_05_06_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_07_08_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_07_08_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_09_10_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_09_10_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_11_12_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_11_12_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_13_14_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_13_14_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_15_16_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_15_16_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_17_18_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_17_18_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_19_20_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_19_20_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_21_22_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_21_22_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_23_24_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_23_24_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_25_26_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_25_26_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_27_28_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_27_28_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_29_30_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_29_30_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_31_32_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_31_32_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_33_34_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_33_34_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_35_36_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_35_36_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_37_38_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_37_38_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_39_40_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_39_40_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_41_42_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_41_42_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_43_44_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_43_44_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_45_46_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_45_46_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_47_48_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_47_48_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_49_50_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_49_50_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_51_52_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_51_52_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_53_54_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_53_54_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_55_56_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_55_56_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_57_58_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_57_58_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_59_60_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_59_60_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_61_62_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_61_62_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_63_64_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_63_64_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_65_66_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_65_66_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_67_68_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_67_68_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_69_70_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_69_70_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_71_72_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_71_72_valid_and_nodup.2.1,
    tribonacci_period_eleven_orbits_73_74_valid_and_nodup.1.1,
    tribonacci_period_eleven_orbits_73_74_valid_and_nodup.2.1, trivial⟩

end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenValidD