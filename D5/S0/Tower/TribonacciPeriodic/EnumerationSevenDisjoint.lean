/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The seventy new period-seven phases are distinct from the prior sixty-seven. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDistinct

local notation "priorFive" => tribonacciPeriodicOrbitRepresentativesFive
local notation "periodSix" => tribonacciPeriodicOrbitRepresentativesExactlySix
local notation "priorSix" => tribonacciPeriodicOrbitRepresentativesSix
local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_old_periodic_state_codes_disjoint_seven_a :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitA) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitA,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_b :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitB) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitB,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_c :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitC) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitC,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_d :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitD) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitD,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_e :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitE) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitE,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_f :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitF) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitF,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_g :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitG) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitG,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_h :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitH) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitH,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_i :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitI) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitI,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_periodic_state_codes_disjoint_seven_j :
    List.Disjoint ((priorSix).flatMap orbitStates)
      (orbitStates tribonacciPeriodSevenOrbitJ) := by
  rw [tribonacciPeriodicOrbitRepresentativesSix, List.flatMap_append,
    List.disjoint_append_left]
  constructor <;> norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit,
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    tribonacciPeriodSixOrbitA, tribonacciPeriodSixOrbitB,
    tribonacciPeriodSixOrbitC, tribonacciPeriodSixOrbitD,
    tribonacciPeriodSixOrbitE, tribonacciPeriodSevenOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo,
    tribonacciCodeSub, tribonacciCodeNeg, tribonacciCodeAdd,
    tribonacciCodeMul, tribonacciCodeOne, tribonacciCodeZero,
    tribonacciCodeRoot]

theorem tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven :
    List.Disjoint
      (tribonacciPeriodicOrbitRepresentativesSix.flatMap orbitStates)
      (tribonacciPeriodicOrbitRepresentativesExactlySeven.flatMap
        orbitStates) := by
  simpa only [tribonacciPeriodicOrbitRepresentativesExactlySeven,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨tribonacci_old_periodic_state_codes_disjoint_seven_a,
        tribonacci_old_periodic_state_codes_disjoint_seven_b,
        tribonacci_old_periodic_state_codes_disjoint_seven_c,
        tribonacci_old_periodic_state_codes_disjoint_seven_d,
        tribonacci_old_periodic_state_codes_disjoint_seven_e,
        tribonacci_old_periodic_state_codes_disjoint_seven_f,
        tribonacci_old_periodic_state_codes_disjoint_seven_g,
        tribonacci_old_periodic_state_codes_disjoint_seven_h,
        tribonacci_old_periodic_state_codes_disjoint_seven_i,
        tribonacci_old_periodic_state_codes_disjoint_seven_j⟩

theorem tribonacci_periodic_orbit_state_codes_nodup_seven :
    (tribonacciPeriodicOrbitRepresentativesSeven.flatMap
      orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesSeven, List.flatMap_append,
    List.nodup_append']
  exact ⟨tribonacci_periodic_orbit_state_codes_nodup_six,
    tribonacci_new_periodic_orbit_state_codes_nodup_seven,
    tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven⟩

end D5.S0.Tower.TribonacciPeriodic.EnumerationSevenDisjoint
