/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise distinctness of the exact primitive period-twelve orbit states. -/

import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDistinct

open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationElevenData
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData

theorem golden_period_twelve_orbits_ad_nodup :
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsAD,
    goldenPeriodTwelveOrbitA,
    goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC,
    goldenPeriodTwelveOrbitD,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_eh_nodup :
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsEH,
    goldenPeriodTwelveOrbitE,
    goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG,
    goldenPeriodTwelveOrbitH,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_il_nodup :
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsIL,
    goldenPeriodTwelveOrbitI,
    goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK,
    goldenPeriodTwelveOrbitL,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_mp_nodup :
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsMP,
    goldenPeriodTwelveOrbitM,
    goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO,
    goldenPeriodTwelveOrbitP,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_qs_nodup :
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsQS,
    goldenPeriodTwelveOrbitQ,
    goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_tv_nodup :
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsTV,
    goldenPeriodTwelveOrbitT,
    goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_wy_nodup :
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodTwelveOrbitsWY,
    goldenPeriodTwelveOrbitW,
    goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_period_twelve_orbits_ad_eh_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsEH, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ad_il_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsIL, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ad_mp_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsMP, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ad_qs_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsQS, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ad_tv_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsTV, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ad_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsAD, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_eh_il_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsEH, goldenPeriodTwelveOrbitsIL, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_eh_mp_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsEH, goldenPeriodTwelveOrbitsMP, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_eh_qs_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsEH, goldenPeriodTwelveOrbitsQS, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_eh_tv_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsEH, goldenPeriodTwelveOrbitsTV, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_eh_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsEH, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_il_mp_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsIL, goldenPeriodTwelveOrbitsMP, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_il_qs_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsIL, goldenPeriodTwelveOrbitsQS, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_il_tv_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsIL, goldenPeriodTwelveOrbitsTV, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_il_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsIL, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_mp_qs_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsMP, goldenPeriodTwelveOrbitsQS, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_mp_tv_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsMP, goldenPeriodTwelveOrbitsTV, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_mp_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsMP, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_qs_tv_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsQS, goldenPeriodTwelveOrbitsTV, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitT,
    goldenPeriodTwelveOrbitU, goldenPeriodTwelveOrbitV,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_qs_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsQS.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsQS, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitW,
    goldenPeriodTwelveOrbitX, goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_tv_wy_disjoint : List.Disjoint
    (goldenPeriodTwelveOrbitsTV.flatMap goldenOrbitStates)
    (goldenPeriodTwelveOrbitsWY.flatMap goldenOrbitStates) := by
  simp only [goldenPeriodTwelveOrbitsTV, goldenPeriodTwelveOrbitsWY, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.disjoint_append_left,
    List.disjoint_append_right]
  repeat' apply And.intro
  all_goals norm_num [
    goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV, goldenPeriodTwelveOrbitW,
    goldenPeriodTwelveOrbitX, goldenPeriodTwelveOrbitY,
    goldenOrbitStates, goldenTraceCode,
      goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
      goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
      goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_new_periodic_orbit_state_codes_nodup_twelve :
    (goldenPeriodicOrbitRepresentativesExactlyTwelve.flatMap
      goldenOrbitStates).Nodup := by
  have hFirstTwo :
      ((goldenPeriodTwelveOrbitsAD ++ goldenPeriodTwelveOrbitsEH).flatMap
        goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨golden_period_twelve_orbits_ad_nodup,
      golden_period_twelve_orbits_eh_nodup,
      golden_period_twelve_orbits_ad_eh_disjoint⟩
  have hSecondTwo :
      ((goldenPeriodTwelveOrbitsIL ++ goldenPeriodTwelveOrbitsMP).flatMap
        goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨golden_period_twelve_orbits_il_nodup,
      golden_period_twelve_orbits_mp_nodup,
      golden_period_twelve_orbits_il_mp_disjoint⟩
  have hFirstFour :
      (((goldenPeriodTwelveOrbitsAD ++ goldenPeriodTwelveOrbitsEH) ++
        (goldenPeriodTwelveOrbitsIL ++ goldenPeriodTwelveOrbitsMP)).flatMap
          goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    refine ⟨hFirstTwo, hSecondTwo, ?_⟩
    rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_left,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨⟨golden_period_twelve_orbits_ad_il_disjoint,
      golden_period_twelve_orbits_ad_mp_disjoint⟩,
      golden_period_twelve_orbits_eh_il_disjoint,
      golden_period_twelve_orbits_eh_mp_disjoint⟩
  have hLastTwo :
      ((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV).flatMap
        goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    exact ⟨golden_period_twelve_orbits_qs_nodup,
      golden_period_twelve_orbits_tv_nodup,
      golden_period_twelve_orbits_qs_tv_disjoint⟩
  have hLastThree :
      (((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
        goldenPeriodTwelveOrbitsWY).flatMap goldenOrbitStates).Nodup := by
    rw [List.flatMap_append, List.nodup_append']
    refine ⟨hLastTwo, golden_period_twelve_orbits_wy_nodup, ?_⟩
    rw [List.flatMap_append, List.disjoint_append_left]
    exact ⟨golden_period_twelve_orbits_qs_wy_disjoint,
      golden_period_twelve_orbits_tv_wy_disjoint⟩
  have hADLast : List.Disjoint
      (goldenPeriodTwelveOrbitsAD.flatMap goldenOrbitStates)
      (((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
        goldenPeriodTwelveOrbitsWY).flatMap goldenOrbitStates) := by
    rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨⟨golden_period_twelve_orbits_ad_qs_disjoint,
      golden_period_twelve_orbits_ad_tv_disjoint⟩,
      golden_period_twelve_orbits_ad_wy_disjoint⟩
  have hEHLast : List.Disjoint
      (goldenPeriodTwelveOrbitsEH.flatMap goldenOrbitStates)
      (((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
        goldenPeriodTwelveOrbitsWY).flatMap goldenOrbitStates) := by
    rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨⟨golden_period_twelve_orbits_eh_qs_disjoint,
      golden_period_twelve_orbits_eh_tv_disjoint⟩,
      golden_period_twelve_orbits_eh_wy_disjoint⟩
  have hILLast : List.Disjoint
      (goldenPeriodTwelveOrbitsIL.flatMap goldenOrbitStates)
      (((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
        goldenPeriodTwelveOrbitsWY).flatMap goldenOrbitStates) := by
    rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨⟨golden_period_twelve_orbits_il_qs_disjoint,
      golden_period_twelve_orbits_il_tv_disjoint⟩,
      golden_period_twelve_orbits_il_wy_disjoint⟩
  have hMPLast : List.Disjoint
      (goldenPeriodTwelveOrbitsMP.flatMap goldenOrbitStates)
      (((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
        goldenPeriodTwelveOrbitsWY).flatMap goldenOrbitStates) := by
    rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨⟨golden_period_twelve_orbits_mp_qs_disjoint,
      golden_period_twelve_orbits_mp_tv_disjoint⟩,
      golden_period_twelve_orbits_mp_wy_disjoint⟩
  change (((((goldenPeriodTwelveOrbitsAD ++ goldenPeriodTwelveOrbitsEH) ++
    (goldenPeriodTwelveOrbitsIL ++ goldenPeriodTwelveOrbitsMP)) ++
    ((goldenPeriodTwelveOrbitsQS ++ goldenPeriodTwelveOrbitsTV) ++
      goldenPeriodTwelveOrbitsWY)).flatMap goldenOrbitStates).Nodup)
  rw [List.flatMap_append, List.nodup_append']
  refine ⟨hFirstFour, hLastThree, ?_⟩
  rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_left]
  constructor
  · rw [List.flatMap_append, List.disjoint_append_left]
    exact ⟨hADLast, hEHLast⟩
  · rw [List.flatMap_append, List.disjoint_append_left]
    exact ⟨hILLast, hMPLast⟩

theorem golden_disjoint_from_exact_period_eleven_groups
    {states : List GoldenCodedState}
    (hAD : List.Disjoint
      (goldenPeriodElevenOrbitsAD.flatMap goldenOrbitStates) states)
    (hEH : List.Disjoint
      (goldenPeriodElevenOrbitsEH.flatMap goldenOrbitStates) states)
    (hIM : List.Disjoint
      (goldenPeriodElevenOrbitsIM.flatMap goldenOrbitStates) states)
    (hNR : List.Disjoint
      (goldenPeriodElevenOrbitsNR.flatMap goldenOrbitStates) states) :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyEleven.flatMap
        goldenOrbitStates) states := by
  change List.Disjoint
    ((((goldenPeriodElevenOrbitsAD ++ goldenPeriodElevenOrbitsEH) ++
      (goldenPeriodElevenOrbitsIM ++ goldenPeriodElevenOrbitsNR)).flatMap
        goldenOrbitStates)) states
  rw [List.flatMap_append, List.flatMap_append, List.disjoint_append_left]
  constructor
  · rw [List.disjoint_append_left]
    exact ⟨hAD, hEH⟩
  · rw [List.flatMap_append, List.disjoint_append_left]
    exact ⟨hIM, hNR⟩

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveDistinct
