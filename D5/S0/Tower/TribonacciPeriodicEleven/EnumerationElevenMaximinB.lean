/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven orbits 16 through 30 have a low arm at or below the champion. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinA

/- Library-search audit trail (2026-08-18):
   * Two proof shapes are needed, and the split was measured for this level:
     thirty-nine low states sit on the left branch of the arm minimum and
     thirty-five on the right.  The split differs at every level, so the sets
     from period nine and period ten are not reusable here. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinB

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant


theorem tribonacci_period_eleven_orbit_16_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit16.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit16.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit16, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_17_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit17.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit17.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit17, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_18_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit18.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit18.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit18, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_19_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit19.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit19.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit19, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_20_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit20.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit20.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit20, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_21_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit21.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit21.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit21, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_22_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit22.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit22.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit22, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_23_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit23.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit23.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit23, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_24_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit24.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit24.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit24, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_25_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit25.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit25.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit25, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_26_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit26.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit26.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit26, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_27_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit27.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit27.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit27, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_28_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit28.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit28.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit28, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_29_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit29.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit29.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit29, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_30_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit30.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit30.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit30.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit30, tribonacciMakeOrbit,
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


end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinB