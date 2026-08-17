/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDistinct
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The seventy new period-seven Tribonacci phase codes are distinct. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData

local notation "orbitStates" => tribonacciOrbitStates

def tribonacciPeriodSevenOrbitsFirst : List TribonacciCodedOrbit :=
  [tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE]

def tribonacciPeriodSevenOrbitsLast : List TribonacciCodedOrbit :=
  [tribonacciPeriodSevenOrbitF, tribonacciPeriodSevenOrbitG,
    tribonacciPeriodSevenOrbitH, tribonacciPeriodSevenOrbitI,
    tribonacciPeriodSevenOrbitJ]

theorem tribonacci_period_seven_first_state_codes_nodup :
    (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_last_state_codes_nodup :
    (tribonacciPeriodSevenOrbitsLast.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodSevenOrbitsLast,
    tribonacciPeriodSevenOrbitF, tribonacciPeriodSevenOrbitG,
    tribonacciPeriodSevenOrbitH, tribonacciPeriodSevenOrbitI,
    tribonacciPeriodSevenOrbitJ, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepCode,
    tribonacciPathCandidateCode, tribonacciPathAffine,
    tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_disjoint_f :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitF) := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_disjoint_g :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitG) := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitG,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_disjoint_h :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitH) := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitH,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_disjoint_i :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitI) := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitI,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_disjoint_j :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitJ) := by
  norm_num [tribonacciPeriodSevenOrbitsFirst,
    tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
    tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
    tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_period_seven_first_last_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodSevenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodSevenOrbitsLast.flatMap orbitStates) := by
  simpa only [tribonacciPeriodSevenOrbitsLast, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_right] using
      ⟨tribonacci_period_seven_first_disjoint_f,
        tribonacci_period_seven_first_disjoint_g,
        tribonacci_period_seven_first_disjoint_h,
        tribonacci_period_seven_first_disjoint_i,
        tribonacci_period_seven_first_disjoint_j⟩

theorem tribonacci_new_periodic_orbit_state_codes_nodup_seven :
    (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
      orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    show [tribonacciPeriodSevenOrbitA, tribonacciPeriodSevenOrbitB,
      tribonacciPeriodSevenOrbitC, tribonacciPeriodSevenOrbitD,
      tribonacciPeriodSevenOrbitE, tribonacciPeriodSevenOrbitF,
      tribonacciPeriodSevenOrbitG, tribonacciPeriodSevenOrbitH,
      tribonacciPeriodSevenOrbitI, tribonacciPeriodSevenOrbitJ] =
        tribonacciPeriodSevenOrbitsFirst ++ tribonacciPeriodSevenOrbitsLast by
          rfl,
    List.flatMap_append, List.nodup_append']
  exact ⟨tribonacci_period_seven_first_state_codes_nodup,
    tribonacci_period_seven_last_state_codes_nodup,
    tribonacci_period_seven_first_last_state_codes_disjoint⟩

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct
