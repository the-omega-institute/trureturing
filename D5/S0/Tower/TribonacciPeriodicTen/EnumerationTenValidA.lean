/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidA
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-ten orbits 01 through 22 are valid coded orbits with distinct states. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData

/- Library-search audit trail (2026-08-18):
   * The tactic closure is the one the period-eight and period-nine certificates
     use, reused verbatim rather than re-derived.
   * The coded representation carries no Decidable instance, so `decide` is
     unavailable and the arithmetic is discharged by `norm_num` plus the same
     `nlinarith` closure. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidA

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData


theorem tribonacci_period_ten_orbits_01_02_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit01 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit01).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit02 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit02).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02,
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

theorem tribonacci_period_ten_orbits_03_04_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit03 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit03).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit04 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit04).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit03, tribonacciPeriodTenOrbit04,
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

theorem tribonacci_period_ten_orbits_05_06_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit05 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit05).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit06 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit06).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit06,
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

theorem tribonacci_period_ten_orbits_07_08_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit07 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit07).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit08 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit08).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
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

theorem tribonacci_period_ten_orbits_09_10_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit09 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit09).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit10 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit10).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10,
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

theorem tribonacci_period_ten_orbits_11_12_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit11 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit11).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit12 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit12).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12,
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

theorem tribonacci_period_ten_orbits_13_14_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit13 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit13).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit14 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit14).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit13, tribonacciPeriodTenOrbit14,
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

theorem tribonacci_period_ten_orbits_15_16_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit15 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit15).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit16 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit16).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit16,
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

theorem tribonacci_period_ten_orbits_17_18_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit17 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit17).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit18 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit18).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
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

theorem tribonacci_period_ten_orbits_19_20_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit19 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit19).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit20 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit20).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20,
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

theorem tribonacci_period_ten_orbits_21_22_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit21 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit21).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit22 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit22).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22,
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

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidA