/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinC
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven orbits 31 through 45 have a low arm at or below the champion. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinB

/- Library-search audit trail (2026-08-18):
   * Two proof shapes are needed, and the split was measured for this level:
     thirty-nine low states sit on the left branch of the arm minimum and
     thirty-five on the right.  The split differs at every level, so the sets
     from period nine and period ten are not reusable here. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinC

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant


theorem tribonacci_period_eleven_orbit_31_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit31.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit31.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit31, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_32_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit32.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit32.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit32, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_33_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit33.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit33.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit33.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit33, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_34_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit34.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit34.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit34.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit34, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_35_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit35.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit35.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit35.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit35, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_36_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit36.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit36.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit36, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_37_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit37.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit37.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit37, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_38_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit38.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit38.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit38.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit38, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_39_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit39.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit39.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit39, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_40_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit40.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit40.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit40, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_41_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit41.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit41.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit41.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit41, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_42_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit42.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit42.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit42.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit42, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_43_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit43.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit43.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit43, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_44_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit44.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit44.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit44, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


theorem tribonacci_period_eleven_orbit_45_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit45.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit45.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit45, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot, tribonacciPeriodicGapLength]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]


end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinC