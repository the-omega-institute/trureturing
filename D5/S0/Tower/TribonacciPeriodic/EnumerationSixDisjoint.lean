/- GID: D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The thirty new period-six phase codes are distinct from the prior thirty-seven. -/

import D5.S0.Tower.TribonacciPeriodic.EnumerationSixData

namespace D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData

local notation "oldRepresentatives" =>
  tribonacciPeriodicOrbitRepresentativesFive
local notation "orbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates
local notation "newRepresentatives" =>
  D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesExactlySix

/- Each comparison theorem expands at most two new cycles. This keeps the
   decidable separation checks isolated rather than one monolithic tactic. -/

theorem tribonacci_old_new_periodic_orbit_state_codes_disjoint_ab_six :
    List.Disjoint ((oldRepresentatives).flatMap orbitStates)
        (orbitStates
          D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitA) /\
      List.Disjoint ((oldRepresentatives).flatMap orbitStates)
        (orbitStates
          D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitB) := by
  constructor <;> norm_num [
    tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitA,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitB,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

theorem tribonacci_old_new_periodic_orbit_state_codes_disjoint_cd_six :
    List.Disjoint ((oldRepresentatives).flatMap orbitStates)
        (orbitStates
          D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitC) /\
      List.Disjoint ((oldRepresentatives).flatMap orbitStates)
        (orbitStates
          D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitD) := by
  constructor <;> norm_num [
    tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitC,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitD,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

theorem tribonacci_old_new_periodic_orbit_state_codes_disjoint_e_six :
    List.Disjoint ((oldRepresentatives).flatMap orbitStates)
      (orbitStates
        D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitE) := by
  norm_num [
    tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodSixOrbitE,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]

theorem tribonacci_old_new_periodic_orbit_state_codes_disjoint_six :
    List.Disjoint ((oldRepresentatives).flatMap orbitStates)
      ((newRepresentatives).flatMap orbitStates) := by
  simpa only [
    tribonacciPeriodicOrbitRepresentativesExactlySix,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨tribonacci_old_new_periodic_orbit_state_codes_disjoint_ab_six.1,
        tribonacci_old_new_periodic_orbit_state_codes_disjoint_ab_six.2,
        tribonacci_old_new_periodic_orbit_state_codes_disjoint_cd_six.1,
        tribonacci_old_new_periodic_orbit_state_codes_disjoint_cd_six.2,
        tribonacci_old_new_periodic_orbit_state_codes_disjoint_e_six⟩

theorem tribonacci_periodic_orbit_state_codes_nodup_six :
    (tribonacciPeriodicOrbitRepresentativesSix.flatMap orbitStates).Nodup := by
  rw [tribonacciPeriodicOrbitRepresentativesSix,
    List.flatMap_append, List.nodup_append']
  exact ⟨
    tribonacci_periodic_orbit_state_codes_nodup,
    tribonacci_new_periodic_orbit_state_codes_nodup_six,
    tribonacci_old_new_periodic_orbit_state_codes_disjoint_six⟩

end D5.S0.Tower.TribonacciPeriodic.EnumerationSixDisjoint
