/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-ten phase codes: the remaining group pairs share no code. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctA

/- Library-search audit trail (2026-08-18):
   * The grouping and tactics are the ones the period-eight and period-nine
     distinctness files use, reused rather than re-derived.
   * Grouping by five is forced by normalisation cost, not chosen for style.
   * Scope: the within-group and across-group statements are proved; assembling
     them into one nodup over the whole list is not done, for the same reason it
     was left at period nine, and is stated as remaining work. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctB

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctA

local notation "orbitStates" => tribonacciOrbitStates

theorem tribonacci_period_ten_third_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit31,
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

theorem tribonacci_period_ten_third_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_third_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsThird.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsThird, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12, tribonacciPeriodTenOrbit13,
      tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_fourth_fifth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFourth, tribonacciPeriodTenOrbitsFifth,
      tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit21,
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

theorem tribonacci_period_ten_fourth_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFourth, tribonacciPeriodTenOrbitsSixth,
      tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit26,
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

theorem tribonacci_period_ten_fourth_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFourth, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit31,
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

theorem tribonacci_period_ten_fourth_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFourth, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_fourth_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFourth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFourth, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
      tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_fifth_sixth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFifth, tribonacciPeriodTenOrbitsSixth,
      tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
      tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit26,
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

theorem tribonacci_period_ten_fifth_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFifth, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
      tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit31,
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

theorem tribonacci_period_ten_fifth_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFifth, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
      tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_fifth_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsFifth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsFifth, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit21, tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23,
      tribonacciPeriodTenOrbit24, tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_sixth_seventh_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSixth, tribonacciPeriodTenOrbitsSeventh,
      tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
      tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30, tribonacciPeriodTenOrbit31,
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

theorem tribonacci_period_ten_sixth_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSixth, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
      tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_sixth_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSixth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSixth, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27, tribonacciPeriodTenOrbit28,
      tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_seventh_eighth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSeventh, tribonacciPeriodTenOrbitsEighth,
      tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
      tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35, tribonacciPeriodTenOrbit36,
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

theorem tribonacci_period_ten_seventh_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsSeventh, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
      tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem tribonacci_period_ten_eighth_ninth_state_codes_disjoint :
    List.Disjoint (tribonacciPeriodTenOrbitsEighth.flatMap orbitStates)
      (tribonacciPeriodTenOrbitsNinth.flatMap orbitStates) := by
  norm_num [
    tribonacciPeriodTenOrbitsEighth, tribonacciPeriodTenOrbitsNinth,
      tribonacciPeriodTenOrbit36, tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38,
      tribonacciPeriodTenOrbit39, tribonacciPeriodTenOrbit40, tribonacciPeriodTenOrbit41,
      tribonacciPeriodTenOrbit42,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctB