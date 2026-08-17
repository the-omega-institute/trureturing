/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All ten period-seven orbits have a low arm below the champion. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenFixed

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenMaximinA

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant

theorem tribonacci_period_seven_orbit_a_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitA.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodSevenOrbitA.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitA, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_b_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitB.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodSevenOrbitB.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitB, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_c_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitC.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodSevenOrbitC.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitC, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_d_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitD.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodSevenOrbitD.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitD, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_e_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitE.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSevenOrbitE.lowState).kind -
        (decodeTribonacciState
          tribonacciPeriodSevenOrbitE.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitE, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_f_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitF.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSevenOrbitF.lowState).kind -
        (decodeTribonacciState
          tribonacciPeriodSevenOrbitF.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitF, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_g_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitG.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSevenOrbitG.lowState).kind -
        (decodeTribonacciState
          tribonacciPeriodSevenOrbitG.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitG, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_h_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitH.lowState) ≤
      championValue t := by
  calc
    _ ≤ (decodeTribonacciState
        tribonacciPeriodSevenOrbitH.lowState).coordinate := min_le_left _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitH, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciCodeValue,
        tribonacciPathCandidateCode, tribonacciPathAffine,
        tribonacciAffineCompose, tribonacciStepAffine,
        tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
        tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_i_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitI.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSevenOrbitI.lowState).kind -
        (decodeTribonacciState
          tribonacciPeriodSevenOrbitI.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitI, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

theorem tribonacci_period_seven_orbit_j_low_arm :
    tribonacciPeriodicStateArm
        (decodeTribonacciState tribonacciPeriodSevenOrbitJ.lowState) ≤
      championValue t := by
  calc
    _ ≤ tribonacciPeriodicGapLength
          (decodeTribonacciState tribonacciPeriodSevenOrbitJ.lowState).kind -
        (decodeTribonacciState
          tribonacciPeriodSevenOrbitJ.lowState).coordinate := min_le_right _ _
    _ ≤ championValue t := by
      rw [championValue_tribonacciConstant, tribonacci_inverse_polynomial]
      norm_num [tribonacciPeriodSevenOrbitJ, tribonacciMakeOrbit,
        tribonacciApplyStepsCode, tribonacciApplyStepCode,
        decodeTribonacciState, tribonacciPeriodicGapLength,
        tribonacciCodeValue, tribonacciPathCandidateCode,
        tribonacciPathAffine, tribonacciAffineCompose,
        tribonacciStepAffine, tribonacciIdentityAffine,
        tribonacciStepTarget, tribonacciCodeDiv, tribonacciCodeInv,
        tribonacciCodeNorm, tribonacciCodeCofactorZero,
        tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
        tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
        tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
        tribonacciCodeRoot]
      nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
        D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenMaximinA
