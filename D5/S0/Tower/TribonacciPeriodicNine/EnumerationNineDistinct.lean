/- GID: D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-nine phase codes: nodup in each group, disjoint across groups. -/

import D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineMaximinB

/- Library-search audit trail (2026-08-18):
   * The grouping and tactic are the ones the period-eight distinctness file
     uses, reused rather than re-derived.
   * Grouping is needed because the normalisation blows up on the full list;
     the period-eight file groups by five for the same reason.
   * Scope: the six within-group statements and the fifteen across-group
     statements are proved.  Assembling them into a single nodup over the whole
     representative list is not done here; the anonymous-constructor shape after
     `List.nodup_append` does not match a flat tuple and the assembly was left
     rather than forced.  The twenty-one components carry the content; the
     assembly is bookkeeping and is stated as remaining work. -/

namespace D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineDistinct

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData

local notation "orbitStates" => tribonacciOrbitStates

def tribonacciPeriodNineOrbitsFirst : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
    tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE]

theorem tribonacci_period_nine_first_state_codes_nodup :
    (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsFirst,
    tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

def tribonacciPeriodNineOrbitsSecond : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
    tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ]

theorem tribonacci_period_nine_second_state_codes_nodup :
    (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsSecond,
    tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
      tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

def tribonacciPeriodNineOrbitsThird : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM,
    tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO]

theorem tribonacci_period_nine_third_state_codes_nodup :
    (tribonacciPeriodNineOrbitsThird.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsThird,
    tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM,
      tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

def tribonacciPeriodNineOrbitsFourth : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
    tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT]

theorem tribonacci_period_nine_fourth_state_codes_nodup :
    (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsFourth,
    tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
      tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

def tribonacciPeriodNineOrbitsFifth : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitU, tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW,
    tribonacciPeriodNineOrbitX, tribonacciPeriodNineOrbitY]

theorem tribonacci_period_nine_fifth_state_codes_nodup :
    (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsFifth,
    tribonacciPeriodNineOrbitU, tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW,
      tribonacciPeriodNineOrbitX, tribonacciPeriodNineOrbitY,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

def tribonacciPeriodNineOrbitsSixth : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitZ]

theorem tribonacci_period_nine_sixth_state_codes_nodup :
    (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodNineOrbitsSixth,
    tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_first_second_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFirst, tribonacciPeriodNineOrbitsSecond,
      tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitF,
      tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH, tribonacciPeriodNineOrbitI,
      tribonacciPeriodNineOrbitJ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_first_third_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsThird.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFirst, tribonacciPeriodNineOrbitsThird,
      tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitK,
      tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM, tribonacciPeriodNineOrbitN,
      tribonacciPeriodNineOrbitO,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_first_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFirst, tribonacciPeriodNineOrbitsFourth,
      tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitP,
      tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR, tribonacciPeriodNineOrbitS,
      tribonacciPeriodNineOrbitT,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_first_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFirst, tribonacciPeriodNineOrbitsFifth,
      tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitU,
      tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
      tribonacciPeriodNineOrbitY,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_first_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFirst, tribonacciPeriodNineOrbitsSixth,
      tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
      tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_second_third_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsThird.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsSecond, tribonacciPeriodNineOrbitsThird,
      tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
      tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitK,
      tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM, tribonacciPeriodNineOrbitN,
      tribonacciPeriodNineOrbitO,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_second_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsSecond, tribonacciPeriodNineOrbitsFourth,
      tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
      tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitP,
      tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR, tribonacciPeriodNineOrbitS,
      tribonacciPeriodNineOrbitT,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_second_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsSecond, tribonacciPeriodNineOrbitsFifth,
      tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
      tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitU,
      tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
      tribonacciPeriodNineOrbitY,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_second_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsSecond, tribonacciPeriodNineOrbitsSixth,
      tribonacciPeriodNineOrbitF, tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH,
      tribonacciPeriodNineOrbitI, tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_third_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsThird, tribonacciPeriodNineOrbitsFourth,
      tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM,
      tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO, tribonacciPeriodNineOrbitP,
      tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR, tribonacciPeriodNineOrbitS,
      tribonacciPeriodNineOrbitT,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_third_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsThird, tribonacciPeriodNineOrbitsFifth,
      tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM,
      tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO, tribonacciPeriodNineOrbitU,
      tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
      tribonacciPeriodNineOrbitY,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_third_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsThird, tribonacciPeriodNineOrbitsSixth,
      tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL, tribonacciPeriodNineOrbitM,
      tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO, tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_fourth_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFourth, tribonacciPeriodNineOrbitsFifth,
      tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
      tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT, tribonacciPeriodNineOrbitU,
      tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
      tribonacciPeriodNineOrbitY,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_fourth_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFourth, tribonacciPeriodNineOrbitsSixth,
      tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
      tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT, tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_nine_fifth_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodNineOrbitsFifth.flatMap orbitStates)
      (tribonacciPeriodNineOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodNineOrbitsFifth, tribonacciPeriodNineOrbitsSixth,
      tribonacciPeriodNineOrbitU, tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW,
      tribonacciPeriodNineOrbitX, tribonacciPeriodNineOrbitY, tribonacciPeriodNineOrbitZ,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineDistinct