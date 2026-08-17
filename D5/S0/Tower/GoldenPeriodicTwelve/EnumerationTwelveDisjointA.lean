/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointA
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Old-new state separation certificates for period-twelve golden orbits A through M. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDistinct

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointA

open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTen
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenDisjoint
open D5.S0.Tower.GoldenPeriodic.EnumerationEleven
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDistinct

theorem golden_disjoint_from_periods_through_eleven
    {states : List GoldenCodedState}
    (hTen : List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates) states)
    (hEleven : List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates) states) :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      states := by
  rw [goldenPeriodicOrbitRepresentativesEleven, List.flatMap_append,
    List.disjoint_append_left]
  exact ⟨hTen, hEleven⟩

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_a_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitA) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitA,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitA,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_a_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitA) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitA, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_a_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitA) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_a_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_a_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_b_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitB) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitB,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitB,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_b_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitB) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitB, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_b_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitB) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_b_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_b_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_c_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitC) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitC,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitC,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_c_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitC) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitC, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_c_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitC) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_c_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_c_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_d_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitD) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitD,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitD,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_d_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitD) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitD, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_d_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitD) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_d_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_d_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_e_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitE) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitE,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitE,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_e_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitE) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitE, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_e_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitE) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_e_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_e_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_f_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitF) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitF,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitF,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_f_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitF) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitF, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_f_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitF) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_f_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_f_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_g_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitG) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitG,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitG,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_g_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitG) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitG, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_g_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitG) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_g_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_g_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_h_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitH) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitH,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitH,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_h_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitH) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitH, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_h_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitH) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_h_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_h_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_i_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitI) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitI,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitI,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_i_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitI) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitI, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_i_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitI) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_i_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_i_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_j_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitJ) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitJ,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitJ,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_j_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitJ) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitJ, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_j_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitJ) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_j_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_j_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_k_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitK) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitK,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitK,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_k_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitK) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitK, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_k_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitK) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_k_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_k_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_l_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitL) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitL,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitL,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_l_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitL) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitL, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_l_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitL) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_l_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_l_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_m_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitM) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitM,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitM,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_m_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitM) := by
  apply golden_disjoint_from_exact_period_eleven_groups <;>
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
      goldenPeriodTwelveOrbitM, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_m_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitM) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_m_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_m_twelve

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointA
