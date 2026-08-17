/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Old-new state separation certificates for period-twelve golden orbits N through Y. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointA

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointB

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
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointA

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_n_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitN) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitN,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitN,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_n_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitN) := by
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
      goldenPeriodTwelveOrbitN, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_n_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitN) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_n_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_n_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_o_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitO) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitO,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitO,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_o_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitO) := by
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
      goldenPeriodTwelveOrbitO, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_o_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitO) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_o_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_o_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_p_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitP) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitP,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitP,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_p_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitP) := by
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
      goldenPeriodTwelveOrbitP, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_p_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitP) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_p_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_p_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_q_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitQ) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitQ,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitQ,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_q_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitQ) := by
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
      goldenPeriodTwelveOrbitQ, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_q_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitQ) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_q_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_q_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_r_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitR) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitR,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitR,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_r_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitR) := by
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
      goldenPeriodTwelveOrbitR, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_r_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitR) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_r_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_r_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_s_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitS) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitS,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitS,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_s_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitS) := by
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
      goldenPeriodTwelveOrbitS, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_s_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitS) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_s_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_s_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_t_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitT) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitT,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitT,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_t_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitT) := by
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
      goldenPeriodTwelveOrbitT, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_t_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitT) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_t_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_t_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_u_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitU) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitU,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitU,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_u_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitU) := by
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
      goldenPeriodTwelveOrbitU, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_u_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitU) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_u_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_u_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_v_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitV) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitV,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitV,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_v_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitV) := by
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
      goldenPeriodTwelveOrbitV, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_v_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitV) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_v_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_v_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_w_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitW) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitW,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitW,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_w_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitW) := by
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
      goldenPeriodTwelveOrbitW, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_w_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitW) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_w_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_w_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_x_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitX) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitX,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitX,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_x_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitX) := by
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
      goldenPeriodTwelveOrbitX, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_x_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitX) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_x_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_x_twelve

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_y_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitY) := by
  apply golden_disjoint_from_periods_through_ten
  · apply golden_disjoint_from_periods_through_nine <;>
      norm_num [goldenPeriodicOrbitRepresentativesEight,
      goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
      goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
      goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
      goldenPeriodEightOrbitE, goldenPeriodicOrbitRepresentativesExactlyNine,
      goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
      goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
      goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTwelveOrbitY,
        goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
      goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
      goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
      goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
      goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenPeriodTwelveOrbitY,
      goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_eleven_periodic_orbit_state_codes_disjoint_y_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitY) := by
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
      goldenPeriodTwelveOrbitY, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_y_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTwelveOrbitY) :=
  golden_disjoint_from_periods_through_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_y_twelve
    golden_old_eleven_periodic_orbit_state_codes_disjoint_y_twelve

theorem golden_old_new_periodic_orbit_state_codes_disjoint_twelve :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEleven.flatMap goldenOrbitStates)
      (goldenPeriodicOrbitRepresentativesExactlyTwelve.flatMap
        goldenOrbitStates) := by
  simpa only [goldenPeriodicOrbitRepresentativesExactlyTwelve,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨golden_old_new_periodic_orbit_state_codes_disjoint_a_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_b_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_c_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_d_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_e_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_f_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_g_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_h_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_i_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_j_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_k_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_l_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_m_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_n_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_o_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_p_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_q_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_r_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_s_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_t_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_u_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_v_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_w_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_x_twelve,
        golden_old_new_periodic_orbit_state_codes_disjoint_y_twelve⟩

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDisjointB
