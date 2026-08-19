/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-ten orbits 23 through 42 are valid coded orbits with distinct states. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidA

/- Library-search audit trail (2026-08-18):
   * The tactic closure is the one the period-eight and period-nine certificates
     use, reused verbatim rather than re-derived.
   * The coded representation carries no Decidable instance, so `decide` is
     unavailable and the arithmetic is discharged by `norm_num` plus the same
     `nlinarith` closure. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidB

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidA


theorem tribonacci_period_ten_orbits_23_24_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit23 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit23).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit24 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit24).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
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

theorem tribonacci_period_ten_orbits_25_26_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit25 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit25).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit26 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit26).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit26,
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

theorem tribonacci_period_ten_orbits_27_28_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit27 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit27).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit28 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit28).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
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

theorem tribonacci_period_ten_orbits_29_30_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit29 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit29).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit30 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit30).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30,
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

theorem tribonacci_period_ten_orbits_31_32_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit31 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit31).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit32 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit32).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32,
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

theorem tribonacci_period_ten_orbits_33_34_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit33 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit33).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit34 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit34).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit33, tribonacciPeriodTenOrbit34,
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

theorem tribonacci_period_ten_orbits_35_36_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit35 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit35).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit36 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit36).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit35, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_orbits_37_38_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit37 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit37).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit38 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit38).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38,
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

theorem tribonacci_period_ten_orbits_39_40_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit39 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit39).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit40 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit40).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit39, tribonacciPeriodTenOrbit40,
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

theorem tribonacci_period_ten_orbits_41_42_valid_and_nodup :
    (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit41 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit41).Nodup) /\
      (tribonacciCodedOrbitValid tribonacciPeriodTenOrbit42 /\
        (tribonacciOrbitStates tribonacciPeriodTenOrbit42).Nodup) := by
  norm_num [tribonacciPeriodTenOrbit41, tribonacciPeriodTenOrbit42,
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

/-- All forty-two primitive period-ten representatives are valid coded orbits. -/
theorem tribonacci_period_ten_representatives_valid :
    tribonacciPeriodTenOrbitRepresentatives.Forall tribonacciCodedOrbitValid := by
  simp only [tribonacciPeriodTenOrbitRepresentatives, List.forall_cons]
  exact ⟨
    tribonacci_period_ten_orbits_01_02_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_01_02_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_03_04_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_03_04_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_05_06_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_05_06_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_07_08_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_07_08_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_09_10_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_09_10_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_11_12_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_11_12_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_13_14_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_13_14_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_15_16_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_15_16_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_17_18_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_17_18_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_19_20_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_19_20_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_21_22_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_21_22_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_23_24_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_23_24_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_25_26_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_25_26_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_27_28_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_27_28_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_29_30_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_29_30_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_31_32_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_31_32_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_33_34_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_33_34_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_35_36_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_35_36_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_37_38_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_37_38_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_39_40_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_39_40_valid_and_nodup.2.1,
    tribonacci_period_ten_orbits_41_42_valid_and_nodup.1.1,
    tribonacci_period_ten_orbits_41_42_valid_and_nodup.2.1, trivial⟩

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenValidB