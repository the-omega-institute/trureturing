/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinE
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinE
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven orbits 61 through 74 have a low arm at or below the champion. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinD

/- Library-search audit trail (2026-08-18):
   * Two proof shapes are needed, and the split was measured for this level:
     thirty-nine low states sit on the left branch of the arm minimum and
     thirty-five on the right.  The split differs at every level, so the sets
     from period nine and period ten are not reusable here. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinE

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinA
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinB
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinC
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinD

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant


theorem tribonacci_period_eleven_orbit_61_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit61.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit61.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit61.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit61, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_62_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit62.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit62.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit62.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit62, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_63_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit63.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit63.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit63.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit63, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_64_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit64.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit64.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit64.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit64, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_65_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit65.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodElevenOrbit65.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit65, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_66_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit66.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit66.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit66.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit66, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_67_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit67.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit67.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit67.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit67, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_68_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit68.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit68.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit68.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit68, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_69_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit69.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit69.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit69.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit69, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_70_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit70.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit70.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit70.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit70, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_71_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit71.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit71.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit71.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit71, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_72_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit72.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit72.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit72.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit72, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_73_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit73.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit73.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit73.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit73, tribonacciMakeOrbit,
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


theorem tribonacci_period_eleven_orbit_74_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodElevenOrbit74.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodElevenOrbit74.lowState).kind -
      (decodeTribonacciState tribonacciPeriodElevenOrbit74.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodElevenOrbit74, tribonacciMakeOrbit,
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


/-- Every period-eleven representative has a low state whose arm lies at or
below the champion value. -/
theorem tribonacci_period_eleven_low_arms_bounded :
    tribonacciPeriodElevenOrbitRepresentatives.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodElevenOrbitRepresentatives, List.forall_cons]
  exact ⟨
    tribonacci_period_eleven_orbit_01_low_arm,
    tribonacci_period_eleven_orbit_02_low_arm,
    tribonacci_period_eleven_orbit_03_low_arm,
    tribonacci_period_eleven_orbit_04_low_arm,
    tribonacci_period_eleven_orbit_05_low_arm,
    tribonacci_period_eleven_orbit_06_low_arm,
    tribonacci_period_eleven_orbit_07_low_arm,
    tribonacci_period_eleven_orbit_08_low_arm,
    tribonacci_period_eleven_orbit_09_low_arm,
    tribonacci_period_eleven_orbit_10_low_arm,
    tribonacci_period_eleven_orbit_11_low_arm,
    tribonacci_period_eleven_orbit_12_low_arm,
    tribonacci_period_eleven_orbit_13_low_arm,
    tribonacci_period_eleven_orbit_14_low_arm,
    tribonacci_period_eleven_orbit_15_low_arm,
    tribonacci_period_eleven_orbit_16_low_arm,
    tribonacci_period_eleven_orbit_17_low_arm,
    tribonacci_period_eleven_orbit_18_low_arm,
    tribonacci_period_eleven_orbit_19_low_arm,
    tribonacci_period_eleven_orbit_20_low_arm,
    tribonacci_period_eleven_orbit_21_low_arm,
    tribonacci_period_eleven_orbit_22_low_arm,
    tribonacci_period_eleven_orbit_23_low_arm,
    tribonacci_period_eleven_orbit_24_low_arm,
    tribonacci_period_eleven_orbit_25_low_arm,
    tribonacci_period_eleven_orbit_26_low_arm,
    tribonacci_period_eleven_orbit_27_low_arm,
    tribonacci_period_eleven_orbit_28_low_arm,
    tribonacci_period_eleven_orbit_29_low_arm,
    tribonacci_period_eleven_orbit_30_low_arm,
    tribonacci_period_eleven_orbit_31_low_arm,
    tribonacci_period_eleven_orbit_32_low_arm,
    tribonacci_period_eleven_orbit_33_low_arm,
    tribonacci_period_eleven_orbit_34_low_arm,
    tribonacci_period_eleven_orbit_35_low_arm,
    tribonacci_period_eleven_orbit_36_low_arm,
    tribonacci_period_eleven_orbit_37_low_arm,
    tribonacci_period_eleven_orbit_38_low_arm,
    tribonacci_period_eleven_orbit_39_low_arm,
    tribonacci_period_eleven_orbit_40_low_arm,
    tribonacci_period_eleven_orbit_41_low_arm,
    tribonacci_period_eleven_orbit_42_low_arm,
    tribonacci_period_eleven_orbit_43_low_arm,
    tribonacci_period_eleven_orbit_44_low_arm,
    tribonacci_period_eleven_orbit_45_low_arm,
    tribonacci_period_eleven_orbit_46_low_arm,
    tribonacci_period_eleven_orbit_47_low_arm,
    tribonacci_period_eleven_orbit_48_low_arm,
    tribonacci_period_eleven_orbit_49_low_arm,
    tribonacci_period_eleven_orbit_50_low_arm,
    tribonacci_period_eleven_orbit_51_low_arm,
    tribonacci_period_eleven_orbit_52_low_arm,
    tribonacci_period_eleven_orbit_53_low_arm,
    tribonacci_period_eleven_orbit_54_low_arm,
    tribonacci_period_eleven_orbit_55_low_arm,
    tribonacci_period_eleven_orbit_56_low_arm,
    tribonacci_period_eleven_orbit_57_low_arm,
    tribonacci_period_eleven_orbit_58_low_arm,
    tribonacci_period_eleven_orbit_59_low_arm,
    tribonacci_period_eleven_orbit_60_low_arm,
    tribonacci_period_eleven_orbit_61_low_arm,
    tribonacci_period_eleven_orbit_62_low_arm,
    tribonacci_period_eleven_orbit_63_low_arm,
    tribonacci_period_eleven_orbit_64_low_arm,
    tribonacci_period_eleven_orbit_65_low_arm,
    tribonacci_period_eleven_orbit_66_low_arm,
    tribonacci_period_eleven_orbit_67_low_arm,
    tribonacci_period_eleven_orbit_68_low_arm,
    tribonacci_period_eleven_orbit_69_low_arm,
    tribonacci_period_eleven_orbit_70_low_arm,
    tribonacci_period_eleven_orbit_71_low_arm,
    tribonacci_period_eleven_orbit_72_low_arm,
    tribonacci_period_eleven_orbit_73_low_arm,
    tribonacci_period_eleven_orbit_74_low_arm, trivial⟩

end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinE