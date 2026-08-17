/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Old-new state separation certificates for the period-eleven golden orbits. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationElevenDistinct

namespace D5.S0.Tower.GoldenPeriodic.EnumerationElevenDisjoint

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTen
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData

theorem golden_disjoint_from_periods_through_ten
    {states : List GoldenCodedState}
    (hNine : List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates) states)
    (hTen : List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates) states) :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates) states := by
  rw [goldenPeriodicOrbitRepresentativesTen, List.flatMap_append,
    List.disjoint_append_left]
  exact ⟨hNine, hTen⟩

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_a_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitA) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitA, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_a_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitA) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitA, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_a_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitA) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_a_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_a_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_b_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitB) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitB, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_b_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitB) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitB, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_b_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitB) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_b_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_b_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_c_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitC) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitC, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_c_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitC) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitC, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_c_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitC) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_c_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_c_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_d_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitD) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitD, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_d_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitD) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitD, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_d_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitD) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_d_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_d_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_e_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitE) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitE, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_e_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitE) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitE, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_e_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitE) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_e_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_e_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_f_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitF) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitF, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_f_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitF) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitF, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_f_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitF) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_f_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_f_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_g_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitG) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitG, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_g_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitG) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitG, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_g_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitG) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_g_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_g_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_h_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitH) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitH, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_h_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitH) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitH, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_h_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitH) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_h_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_h_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_i_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitI) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitI, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_i_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitI) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitI, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_i_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitI) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_i_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_i_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_j_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitJ) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitJ, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_j_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitJ) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitJ, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_j_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitJ) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_j_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_j_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_k_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitK) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitK, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_k_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitK) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitK, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_k_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitK) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_k_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_k_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_l_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitL) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitL, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_l_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitL) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitL, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_l_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitL) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_l_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_l_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_m_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitM) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitM, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_m_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitM) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitM, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_m_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitM) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_m_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_m_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_n_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitN) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitN, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_n_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitN) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitN, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_n_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitN) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_n_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_n_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_o_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitO) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitO, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_o_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitO) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitO, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_o_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitO) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_o_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_o_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_p_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitP) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitP, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_p_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitP) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitP, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_p_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitP) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_p_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_p_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_q_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitQ) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitQ, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_q_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitQ) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitQ, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_q_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitQ) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_q_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_q_eleven

theorem golden_old_nine_periodic_orbit_state_codes_disjoint_r_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitR) := by
  apply golden_disjoint_from_periods_through_nine <;>
    norm_num [goldenPeriodicOrbitRepresentativesEight, goldenPeriodicOrbitRepresentativesSeven,
      goldenChampionPeriodicOrbit, goldenPeriodicOrbitRepresentativesExactlyEight,
      goldenPeriodEightOrbitA, goldenPeriodEightOrbitB, goldenPeriodEightOrbitC,
      goldenPeriodEightOrbitD, goldenPeriodEightOrbitE,
      goldenPeriodicOrbitRepresentativesExactlyNine, goldenPeriodNineOrbitA,
      goldenPeriodNineOrbitB, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
      goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenPeriodNineOrbitG,
      goldenPeriodNineOrbitH, goldenPeriodElevenOrbitR, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero,
      goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_ten_periodic_orbit_state_codes_disjoint_r_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitR) := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenPeriodTenOrbitK, goldenPeriodElevenOrbitR, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenCodeAdd, goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne,
    goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_r_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodElevenOrbitR) :=
  golden_disjoint_from_periods_through_ten
    golden_old_nine_periodic_orbit_state_codes_disjoint_r_eleven
    golden_old_ten_periodic_orbit_state_codes_disjoint_r_eleven

theorem golden_old_new_periodic_orbit_state_codes_disjoint_eleven :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesTen.flatMap goldenOrbitStates)
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap goldenOrbitStates) := by
  simpa only [goldenPeriodicOrbitRepresentativesExactlyEleven,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨golden_old_new_periodic_orbit_state_codes_disjoint_a_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_b_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_c_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_d_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_e_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_f_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_g_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_h_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_i_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_j_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_k_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_l_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_m_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_n_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_o_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_p_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_q_eleven,
        golden_old_new_periodic_orbit_state_codes_disjoint_r_eleven⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationElevenDisjoint
