/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartC
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part C: across-group statements, block 2. -/

import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartB

/- Library-search audit trail (2026-08-18):
   * Grouping is by four here, not by five as at the shorter levels.  Five was
     tried first and every across-group statement hit the default heartbeat
     budget; a probe showed three and four both clear it, and four gives the
     fewest pairs among the workable sizes.  The budget was not raised.
   * A separate directory is used because the period-eleven directory is at ten
     of twelve entries.
   * Scope: within-group and across-group statements are proved; assembling them
     into one nodup over the whole list is not done, as at the shorter levels. -/

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartC

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

local notation "orbitStates" => tribonacciOrbitStates

theorem eleven_g03_g04_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG04.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG04, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit13,
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

theorem eleven_g03_g05_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG05.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG05, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit17,
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

theorem eleven_g03_g06_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG06.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG06, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit21,
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

theorem eleven_g03_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG07, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit25,
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

theorem eleven_g03_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG08, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit29,
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

theorem eleven_g03_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG09, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit33,
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

theorem eleven_g03_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG10, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g03_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG11, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g03_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG12, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g03_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG13, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g03_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG14, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g03_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG15, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g03_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG16, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g03_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG17, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g03_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG18, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g03_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG03.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG03, elevenOrbitsG19, tribonacciPeriodElevenOrbit09,
      tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
      tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g04_g05_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG05.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG05, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit17,
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

theorem eleven_g04_g06_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG06.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG06, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit21,
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

theorem eleven_g04_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG07, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit25,
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

theorem eleven_g04_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG08, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit29,
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

theorem eleven_g04_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG09, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit33,
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

theorem eleven_g04_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG10, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g04_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG11, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g04_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG12, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g04_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG13, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g04_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG14, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g04_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG15, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g04_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG16, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g04_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG17, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g04_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG18, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g04_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG04.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG04, elevenOrbitsG19, tribonacciPeriodElevenOrbit13,
      tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
      tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g05_g06_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG06.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG06, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit21,
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

theorem eleven_g05_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG07, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit25,
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

theorem eleven_g05_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG08, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit29,
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

theorem eleven_g05_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG09, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit33,
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

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartC