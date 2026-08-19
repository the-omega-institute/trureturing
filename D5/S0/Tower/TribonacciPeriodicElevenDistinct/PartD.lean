/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartD
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartD
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part D: across-group statements, block 3. -/

import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartC

/- Library-search audit trail (2026-08-18):
   * Grouping is by four here, not by five as at the shorter levels.  Five was
     tried first and every across-group statement hit the default heartbeat
     budget; a probe showed three and four both clear it, and four gives the
     fewest pairs among the workable sizes.  The budget was not raised.
   * A separate directory is used because the period-eleven directory is at ten
     of twelve entries.
   * Scope: within-group and across-group statements are proved; assembling them
     into one nodup over the whole list is not done, as at the shorter levels. -/

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartD

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

local notation "orbitStates" => tribonacciOrbitStates

theorem eleven_g05_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG10, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g05_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG11, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g05_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG12, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g05_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG13, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g05_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG14, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g05_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG15, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g05_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG16, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g05_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG17, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g05_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG18, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g05_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG05.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG05, elevenOrbitsG19, tribonacciPeriodElevenOrbit17,
      tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
      tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g06_g07_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG07.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG07, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit25,
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

theorem eleven_g06_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG08, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit29,
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

theorem eleven_g06_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG09, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit33,
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

theorem eleven_g06_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG10, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g06_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG11, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g06_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG12, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g06_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG13, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g06_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG14, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g06_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG15, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g06_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG16, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g06_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG17, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g06_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG18, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g06_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG06.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG06, elevenOrbitsG19, tribonacciPeriodElevenOrbit21,
      tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
      tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g07_g08_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG08.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG08, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit29,
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

theorem eleven_g07_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG09, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit33,
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

theorem eleven_g07_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG10, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g07_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG11, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g07_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG12, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g07_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG13, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g07_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG14, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g07_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG15, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g07_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG16, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g07_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG17, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g07_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG18, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g07_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG07.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG07, elevenOrbitsG19, tribonacciPeriodElevenOrbit25,
      tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
      tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartD