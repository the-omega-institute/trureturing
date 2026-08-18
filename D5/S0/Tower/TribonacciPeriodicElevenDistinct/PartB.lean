/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartB
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartB
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part B: across-group statements, block 1. -/

import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

/- Library-search audit trail (2026-08-18):
   * Grouping is by four here, not by five as at the shorter levels.  Five was
     tried first and every across-group statement hit the default heartbeat
     budget; a probe showed three and four both clear it, and four gives the
     fewest pairs among the workable sizes.  The budget was not raised.
   * A separate directory is used because the period-eleven directory is at ten
     of twelve entries.
   * Scope: within-group and across-group statements are proved; assembling them
     into one nodup over the whole list is not done, as at the shorter levels. -/

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartB

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

local notation "orbitStates" => tribonacciOrbitStates

theorem eleven_g01_g02_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG02.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG02, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g03_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG03.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG03, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g04_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG04.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG04, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g05_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG05.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG05, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g06_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG06.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG06, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG07, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG08, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG09, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG10, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG11, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG12, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG13, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG14, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG15, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG16, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit61,
      tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
      tribonacciPeriodElevenOrbit64,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG17, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit65,
      tribonacciPeriodElevenOrbit66, tribonacciPeriodElevenOrbit67,
      tribonacciPeriodElevenOrbit68,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG18, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit69,
      tribonacciPeriodElevenOrbit70, tribonacciPeriodElevenOrbit71,
      tribonacciPeriodElevenOrbit72,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g01_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG01.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG01, elevenOrbitsG19, tribonacciPeriodElevenOrbit01,
      tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
      tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g03_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG03.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG03, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g04_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG04.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG04, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g05_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG05.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG05, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g06_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG06.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG06, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG07, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG08, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG09, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG10, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG11, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG12, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG13, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG14, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG15, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG16, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit61,
      tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
      tribonacciPeriodElevenOrbit64,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG17, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit65,
      tribonacciPeriodElevenOrbit66, tribonacciPeriodElevenOrbit67,
      tribonacciPeriodElevenOrbit68,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG18, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit69,
      tribonacciPeriodElevenOrbit70, tribonacciPeriodElevenOrbit71,
      tribonacciPeriodElevenOrbit72,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG02.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG02, elevenOrbitsG19, tribonacciPeriodElevenOrbit05,
      tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
      tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartB