/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-ten orbits 29 through 42 have a low arm at or below the champion. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinB

/- Library-search audit trail (2026-08-18):
   * Two proof shapes are needed, as at period nine, but the split is different:
     here twenty-two low states sit on the left branch of the arm minimum and
     twenty on the right.  The right-branch set was measured for this level and
     is not the period-nine set; carrying that one over would leave several
     cases unprovable. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinA
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinB

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant


theorem tribonacci_period_ten_orbit_29_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit29.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit29.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit29.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit29, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_30_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit30.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit30.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit30.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit30, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_31_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit31.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit31.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit31.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit31, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_32_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit32.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit32.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit32.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit32, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_33_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit33.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodTenOrbit33.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit33, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_34_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit34.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit34.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit34.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit34, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_35_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit35.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit35.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit35.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit35, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_36_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit36.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit36.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit36.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit36, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_37_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit37.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit37.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit37.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit37, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_38_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit38.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit38.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit38.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit38, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_39_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit39.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit39.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit39.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit39, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_40_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit40.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit40.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit40.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit40, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_41_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit41.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit41.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit41.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit41, tribonacciMakeOrbit,
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


theorem tribonacci_period_ten_orbit_42_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodTenOrbit42.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
        (decodeTribonacciState tribonacciPeriodTenOrbit42.lowState).kind -
      (decodeTribonacciState tribonacciPeriodTenOrbit42.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodTenOrbit42, tribonacciMakeOrbit,
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


/-- Every period-ten representative has a low state whose arm lies at or below
the champion value, so none of them is a strict survivor. -/
theorem tribonacci_period_ten_low_arms_bounded :
    tribonacciPeriodTenOrbitRepresentatives.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodTenOrbitRepresentatives, List.forall_cons]
  exact ⟨
    tribonacci_period_ten_orbit_01_low_arm,
    tribonacci_period_ten_orbit_02_low_arm,
    tribonacci_period_ten_orbit_03_low_arm,
    tribonacci_period_ten_orbit_04_low_arm,
    tribonacci_period_ten_orbit_05_low_arm,
    tribonacci_period_ten_orbit_06_low_arm,
    tribonacci_period_ten_orbit_07_low_arm,
    tribonacci_period_ten_orbit_08_low_arm,
    tribonacci_period_ten_orbit_09_low_arm,
    tribonacci_period_ten_orbit_10_low_arm,
    tribonacci_period_ten_orbit_11_low_arm,
    tribonacci_period_ten_orbit_12_low_arm,
    tribonacci_period_ten_orbit_13_low_arm,
    tribonacci_period_ten_orbit_14_low_arm,
    tribonacci_period_ten_orbit_15_low_arm,
    tribonacci_period_ten_orbit_16_low_arm,
    tribonacci_period_ten_orbit_17_low_arm,
    tribonacci_period_ten_orbit_18_low_arm,
    tribonacci_period_ten_orbit_19_low_arm,
    tribonacci_period_ten_orbit_20_low_arm,
    tribonacci_period_ten_orbit_21_low_arm,
    tribonacci_period_ten_orbit_22_low_arm,
    tribonacci_period_ten_orbit_23_low_arm,
    tribonacci_period_ten_orbit_24_low_arm,
    tribonacci_period_ten_orbit_25_low_arm,
    tribonacci_period_ten_orbit_26_low_arm,
    tribonacci_period_ten_orbit_27_low_arm,
    tribonacci_period_ten_orbit_28_low_arm,
    tribonacci_period_ten_orbit_29_low_arm,
    tribonacci_period_ten_orbit_30_low_arm,
    tribonacci_period_ten_orbit_31_low_arm,
    tribonacci_period_ten_orbit_32_low_arm,
    tribonacci_period_ten_orbit_33_low_arm,
    tribonacci_period_ten_orbit_34_low_arm,
    tribonacci_period_ten_orbit_35_low_arm,
    tribonacci_period_ten_orbit_36_low_arm,
    tribonacci_period_ten_orbit_37_low_arm,
    tribonacci_period_ten_orbit_38_low_arm,
    tribonacci_period_ten_orbit_39_low_arm,
    tribonacci_period_ten_orbit_40_low_arm,
    tribonacci_period_ten_orbit_41_low_arm,
    tribonacci_period_ten_orbit_42_low_arm, trivial⟩

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC