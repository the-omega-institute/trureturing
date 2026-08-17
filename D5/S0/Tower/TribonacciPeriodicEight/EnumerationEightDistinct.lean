/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDistinct
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEightDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The one hundred twenty new period-eight Tribonacci phase codes are distinct. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData

local notation "orbitStates" => tribonacciOrbitStates

def tribonacciPeriodEightOrbitsFirst : List TribonacciCodedOrbit :=
  [tribonacciPeriodEightOrbitA, tribonacciPeriodEightOrbitB,
    tribonacciPeriodEightOrbitC, tribonacciPeriodEightOrbitD,
    tribonacciPeriodEightOrbitE]

def tribonacciPeriodEightOrbitsMiddle : List TribonacciCodedOrbit :=
  [tribonacciPeriodEightOrbitF, tribonacciPeriodEightOrbitG,
    tribonacciPeriodEightOrbitH, tribonacciPeriodEightOrbitI,
    tribonacciPeriodEightOrbitJ]

def tribonacciPeriodEightOrbitsLast : List TribonacciCodedOrbit :=
  [tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
    tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
    tribonacciPeriodEightOrbitO]

theorem tribonacci_period_eight_first_state_codes_nodup :
    (tribonacciPeriodEightOrbitsFirst.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodEightOrbitsFirst,
    tribonacciPeriodEightOrbitA, tribonacciPeriodEightOrbitB,
    tribonacciPeriodEightOrbitC, tribonacciPeriodEightOrbitD,
    tribonacciPeriodEightOrbitE, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_eight_middle_state_codes_nodup :
    (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodEightOrbitsMiddle,
    tribonacciPeriodEightOrbitF, tribonacciPeriodEightOrbitG,
    tribonacciPeriodEightOrbitH, tribonacciPeriodEightOrbitI,
    tribonacciPeriodEightOrbitJ, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_eight_last_state_codes_nodup :
    (tribonacciPeriodEightOrbitsLast.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodEightOrbitsLast,
    tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
    tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
    tribonacciPeriodEightOrbitO, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_eight_first_middle_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodEightOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightOrbitsFirst,
    tribonacciPeriodEightOrbitsMiddle, tribonacciPeriodEightOrbitA,
    tribonacciPeriodEightOrbitB, tribonacciPeriodEightOrbitC,
    tribonacciPeriodEightOrbitD, tribonacciPeriodEightOrbitE,
    tribonacciPeriodEightOrbitF, tribonacciPeriodEightOrbitG,
    tribonacciPeriodEightOrbitH, tribonacciPeriodEightOrbitI,
    tribonacciPeriodEightOrbitJ, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_eight_first_last_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodEightOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsLast.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightOrbitsFirst,
    tribonacciPeriodEightOrbitsLast, tribonacciPeriodEightOrbitA,
    tribonacciPeriodEightOrbitB, tribonacciPeriodEightOrbitC,
    tribonacciPeriodEightOrbitD, tribonacciPeriodEightOrbitE,
    tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
    tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
    tribonacciPeriodEightOrbitO, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_eight_middle_last_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsLast.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightOrbitsMiddle,
    tribonacciPeriodEightOrbitsLast, tribonacciPeriodEightOrbitF,
    tribonacciPeriodEightOrbitG, tribonacciPeriodEightOrbitH,
    tribonacciPeriodEightOrbitI, tribonacciPeriodEightOrbitJ,
    tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
    tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
    tribonacciPeriodEightOrbitO, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_new_periodic_orbit_state_codes_nodup_eight :
    (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
      orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesExactlyEight,
    show [tribonacciPeriodEightOrbitA, tribonacciPeriodEightOrbitB,
      tribonacciPeriodEightOrbitC, tribonacciPeriodEightOrbitD,
      tribonacciPeriodEightOrbitE, tribonacciPeriodEightOrbitF,
      tribonacciPeriodEightOrbitG, tribonacciPeriodEightOrbitH,
      tribonacciPeriodEightOrbitI, tribonacciPeriodEightOrbitJ,
      tribonacciPeriodEightOrbitK, tribonacciPeriodEightOrbitL,
      tribonacciPeriodEightOrbitM, tribonacciPeriodEightOrbitN,
      tribonacciPeriodEightOrbitO] =
        tribonacciPeriodEightOrbitsFirst ++
          tribonacciPeriodEightOrbitsMiddle ++
            tribonacciPeriodEightOrbitsLast by rfl,
    List.flatMap_append, List.nodup_append']
  have hfirstmiddle :
      (tribonacciPeriodEightOrbitsFirst ++
        tribonacciPeriodEightOrbitsMiddle).flatMap orbitStates |>.Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨tribonacci_period_eight_first_state_codes_nodup,
      tribonacci_period_eight_middle_state_codes_nodup,
      tribonacci_period_eight_first_middle_state_codes_disjoint⟩
  have hfirstmiddlelast : List.Disjoint
      ((tribonacciPeriodEightOrbitsFirst ++
        tribonacciPeriodEightOrbitsMiddle).flatMap orbitStates)
      (tribonacciPeriodEightOrbitsLast.flatMap orbitStates) := by
    rw [List.flatMap_append, List.disjoint_append_left]
    exact ⟨tribonacci_period_eight_first_last_state_codes_disjoint,
      tribonacci_period_eight_middle_last_state_codes_disjoint⟩
  exact ⟨hfirstmiddle, tribonacci_period_eight_last_state_codes_nodup,
    hfirstmiddlelast⟩

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct
