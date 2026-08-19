/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctA
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-ten phase codes: no duplicates inside each group of five. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC

/- Library-search audit trail (2026-08-18):
   * The grouping and tactics are the ones the period-eight and period-nine
     distinctness files use, reused rather than re-derived.
   * Grouping by five is forced by normalisation cost, not chosen for style.
   * Scope: the within-group and across-group statements are proved; assembling
     them into one nodup over the whole list is not done, for the same reason it
     was left at period nine, and is stated as remaining work. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctA

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData

local notation "orbitStates" => tribonacciOrbitStates

def tribonacciPeriodTenOrbitsFirst : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
    tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05]

def tribonacciPeriodTenOrbitsSecond : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
    tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10]

def tribonacciPeriodTenOrbitsThird : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
    tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15]

def tribonacciPeriodTenOrbitsFourth : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
    tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20]

def tribonacciPeriodTenOrbitsFifth : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
    tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25]

def tribonacciPeriodTenOrbitsSixth : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
    tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30]

def tribonacciPeriodTenOrbitsSeventh : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
    tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35]

def tribonacciPeriodTenOrbitsEighth : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit36, tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38,
    tribonacciPeriodTenOrbit39, tribonacciPeriodTenOrbit40]

def tribonacciPeriodTenOrbitsNinth : List TribonacciCodedOrbit :=
  [tribonacciPeriodTenOrbit41, tribonacciPeriodTenOrbit42]

theorem tribonacci_period_ten_first_state_codes_nodup :
    (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsFirst,
    tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_state_codes_nodup :
    (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsSecond,
    tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_third_state_codes_nodup :
    (tribonacciPeriodTenOrbitsThird.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsThird,
    tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_fourth_state_codes_nodup :
    (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsFourth,
    tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_fifth_state_codes_nodup :
    (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsFifth,
    tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
      tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_sixth_state_codes_nodup :
    (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsSixth,
    tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
      tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_seventh_state_codes_nodup :
    (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsSeventh,
    tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
      tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_eighth_state_codes_nodup :
    (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsEighth,
    tribonacciPeriodTenOrbit36, tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38,
      tribonacciPeriodTenOrbit39, tribonacciPeriodTenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_ninth_state_codes_nodup :
    (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates).Nodup := by
  norm_num [tribonacciPeriodTenOrbitsNinth,
    tribonacciPeriodTenOrbit41, tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_second_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsSecond,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit06,
      tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08, tribonacciPeriodTenOrbit09,
      tribonacciPeriodTenOrbit10,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_third_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsThird.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsThird,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit11,
      tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13, tribonacciPeriodTenOrbit14,
      tribonacciPeriodTenOrbit15,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsFourth,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit16,
      tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18, tribonacciPeriodTenOrbit19,
      tribonacciPeriodTenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsFifth,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit21,
      tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
      tribonacciPeriodTenOrbit25,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsSixth,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit26,
      tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28, tribonacciPeriodTenOrbit29,
      tribonacciPeriodTenOrbit30,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit31,
      tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33, tribonacciPeriodTenOrbit34,
      tribonacciPeriodTenOrbit35,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit36,
      tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38, tribonacciPeriodTenOrbit39,
      tribonacciPeriodTenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_first_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFirst.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFirst, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
      tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_third_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsThird.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsThird,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit11,
      tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13, tribonacciPeriodTenOrbit14,
      tribonacciPeriodTenOrbit15,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsFourth,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit16,
      tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18, tribonacciPeriodTenOrbit19,
      tribonacciPeriodTenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsFifth,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit21,
      tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
      tribonacciPeriodTenOrbit25,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsSixth,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit26,
      tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28, tribonacciPeriodTenOrbit29,
      tribonacciPeriodTenOrbit30,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit31,
      tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33, tribonacciPeriodTenOrbit34,
      tribonacciPeriodTenOrbit35,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit36,
      tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38, tribonacciPeriodTenOrbit39,
      tribonacciPeriodTenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_second_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSecond.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSecond, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit06, tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08,
      tribonacciPeriodTenOrbit09, tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_third_fourth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsFourth,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit16,
      tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18, tribonacciPeriodTenOrbit19,
      tribonacciPeriodTenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_third_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsFifth,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit21,
      tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
      tribonacciPeriodTenOrbit25,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_third_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsSixth,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit26,
      tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28, tribonacciPeriodTenOrbit29,
      tribonacciPeriodTenOrbit30,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctA