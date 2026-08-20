/- GID: D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The one hundred twenty new period-eight phases are distinct from the eleven inherited phases. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct

namespace D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDisjoint

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDistinct

local notation "orbitStates" => tribonacciOrbitStates

local macro "old_defs" : tactic => `(tactic|
  norm_num [tribonacciPeriodEightInheritedOrbits,
    tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightInheritedOrbitD,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot])

theorem tribonacci_period_eight_inherited_state_codes_nodup :
    (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates).Nodup := by
  old_defs

theorem tribonacci_inherited_first_new_state_codes_disjoint_eight :
    List.Disjoint (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsFirst.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightInheritedOrbits,
    tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightInheritedOrbitD,
    tribonacciChampionPeriodicOrbit, tribonacciPeriodEightOrbitsFirst,
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

theorem tribonacci_inherited_middle_new_state_codes_disjoint_eight :
    List.Disjoint (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightInheritedOrbits,
    tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightInheritedOrbitD,
    tribonacciChampionPeriodicOrbit, tribonacciPeriodEightOrbitsMiddle,
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

theorem tribonacci_inherited_last_new_state_codes_disjoint_eight :
    List.Disjoint (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodEightOrbitsLast.flatMap orbitStates) := by
  norm_num [tribonacciPeriodEightInheritedOrbits,
    tribonacciPeriodEightInheritedOrbitA,
    tribonacciPeriodEightInheritedOrbitB,
    tribonacciPeriodEightInheritedOrbitC,
    tribonacciPeriodEightInheritedOrbitD,
    tribonacciChampionPeriodicOrbit, tribonacciPeriodEightOrbitsLast,
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

theorem tribonacci_inherited_new_state_codes_disjoint_eight :
    List.Disjoint (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates)
      (tribonacciPeriodicOrbitRepresentativesExactlyEight.flatMap
        orbitStates) := by
  change List.Disjoint
    (tribonacciPeriodEightInheritedOrbits.flatMap orbitStates)
    ((tribonacciPeriodEightOrbitsFirst.flatMap orbitStates) ++
      (tribonacciPeriodEightOrbitsMiddle.flatMap orbitStates) ++
      tribonacciPeriodEightOrbitsLast.flatMap orbitStates)
  rw [List.disjoint_append_right]
  constructor
  · rw [List.disjoint_append_right]
    exact ⟨tribonacci_inherited_first_new_state_codes_disjoint_eight,
      tribonacci_inherited_middle_new_state_codes_disjoint_eight⟩
  · exact tribonacci_inherited_last_new_state_codes_disjoint_eight

theorem tribonacci_period_eight_expected_state_codes_nodup :
    (tribonacciPeriodicOrbitRepresentativesAtEight.flatMap
      orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesAtEight, List.flatMap_append,
    List.nodup_append']
  exact ⟨tribonacci_period_eight_inherited_state_codes_nodup,
    tribonacci_new_periodic_orbit_state_codes_nodup_eight,
    tribonacci_inherited_new_state_codes_disjoint_eight⟩

end D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightDisjoint
