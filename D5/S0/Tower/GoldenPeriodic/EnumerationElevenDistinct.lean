/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise distinctness of the exact primitive period-eleven orbit states. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationElevenData

namespace D5.S0.Tower.GoldenPeriodic.EnumerationElevenDistinct

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTen
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData

theorem golden_period_eleven_orbits_ad_nodup :
    (goldenPeriodElevenOrbitsAD.flatMap goldenOrbitStates).Nodup := by
    norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitA,
      goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC,
      goldenPeriodElevenOrbitD, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
    decide
theorem golden_period_eleven_orbits_eh_nodup :
    (goldenPeriodElevenOrbitsEH.flatMap goldenOrbitStates).Nodup := by
    norm_num [goldenPeriodElevenOrbitsEH, goldenPeriodElevenOrbitE,
      goldenPeriodElevenOrbitF, goldenPeriodElevenOrbitG,
      goldenPeriodElevenOrbitH, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
    decide
theorem golden_period_eleven_orbits_im_nodup :
    (goldenPeriodElevenOrbitsIM.flatMap goldenOrbitStates).Nodup := by
    norm_num [goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitI,
      goldenPeriodElevenOrbitJ, goldenPeriodElevenOrbitK,
      goldenPeriodElevenOrbitL, goldenPeriodElevenOrbitM, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
      goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
      goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
    decide
theorem golden_period_eleven_orbits_nr_nodup :
    (goldenPeriodElevenOrbitsNR.flatMap goldenOrbitStates).Nodup := by
    norm_num [goldenPeriodElevenOrbitsNR, goldenPeriodElevenOrbitN,
      goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
      goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
      goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
      goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
    decide
theorem golden_period_eleven_orbits_ad_eh_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsAD.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsEH.flatMap goldenOrbitStates) := by
    simp only [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.disjoint_append_left, List.disjoint_append_right]
    repeat' apply And.intro
    all_goals norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsEH,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH, goldenOrbitStates,
      goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
      goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
      goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_period_eleven_orbits_ad_im_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsAD.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsIM.flatMap goldenOrbitStates) := by
    simp only [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsIM,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.disjoint_append_left, List.disjoint_append_right]
    repeat' apply And.intro
    all_goals norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsIM,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_period_eleven_orbits_ad_nr_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsAD.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsNR.flatMap goldenOrbitStates) := by
    simp only [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsNR,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.disjoint_append_left, List.disjoint_append_right]
    repeat' apply And.intro
    all_goals norm_num [goldenPeriodElevenOrbitsAD, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
      goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD,
      goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
      goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ,
      goldenPeriodElevenOrbitR, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_period_eleven_orbits_eh_im_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsEH.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsIM.flatMap goldenOrbitStates) := by
    simp only [goldenPeriodElevenOrbitsEH, goldenPeriodElevenOrbitsIM,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.disjoint_append_left, List.disjoint_append_right]
    repeat' apply And.intro
    all_goals norm_num [goldenPeriodElevenOrbitsEH, goldenPeriodElevenOrbitsIM,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
      goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
      goldenPeriodElevenOrbitM, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_period_eleven_orbits_eh_nr_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsEH.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsNR.flatMap goldenOrbitStates) := by
    simp only [goldenPeriodElevenOrbitsEH, goldenPeriodElevenOrbitsNR,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.disjoint_append_left, List.disjoint_append_right]
    repeat' apply And.intro
    all_goals norm_num [goldenPeriodElevenOrbitsEH, goldenPeriodElevenOrbitsNR,
      goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
      goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH,
      goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
      goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ,
      goldenPeriodElevenOrbitR, goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_period_eleven_orbits_im_nr_disjoint : List.Disjoint
      (goldenPeriodElevenOrbitsIM.flatMap goldenOrbitStates)
      (goldenPeriodElevenOrbitsNR.flatMap goldenOrbitStates) := by
  norm_num [goldenPeriodElevenOrbitsIM, goldenPeriodElevenOrbitsNR,
    goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
    goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
theorem golden_new_periodic_orbit_state_codes_nodup_eleven :
    (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
      goldenOrbitStates).Nodup := by
  have hLeft : ((goldenPeriodElevenOrbitsAD ++ goldenPeriodElevenOrbitsEH).flatMap
      goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨golden_period_eleven_orbits_ad_nodup,
      golden_period_eleven_orbits_eh_nodup,
      golden_period_eleven_orbits_ad_eh_disjoint⟩
  have hRight : ((goldenPeriodElevenOrbitsIM ++ goldenPeriodElevenOrbitsNR).flatMap
      goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨golden_period_eleven_orbits_im_nodup,
      golden_period_eleven_orbits_nr_nodup,
      golden_period_eleven_orbits_im_nr_disjoint⟩
  change ((((goldenPeriodElevenOrbitsAD ++ goldenPeriodElevenOrbitsEH) ++
    (goldenPeriodElevenOrbitsIM ++ goldenPeriodElevenOrbitsNR)).flatMap
      goldenOrbitStates).Nodup)
  rw [List.flatMap_append, List.nodup_append']
  refine ⟨hLeft, hRight, ?_⟩
  rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_left,
    List.disjoint_append_right, List.disjoint_append_right]
  exact ⟨⟨golden_period_eleven_orbits_ad_im_disjoint,
    golden_period_eleven_orbits_ad_nr_disjoint⟩,
    golden_period_eleven_orbits_eh_im_disjoint,
    golden_period_eleven_orbits_eh_nr_disjoint⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationElevenDistinct
