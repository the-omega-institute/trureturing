/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartE
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartE
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part E: across-group statements, block 4. -/

import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartD

/- Library-search audit trail (2026-08-18):
   * Grouping is by four here, not by five as at the shorter levels.  Five was
     tried first and every across-group statement hit the default heartbeat
     budget; a probe showed three and four both clear it, and four gives the
     fewest pairs among the workable sizes.  The budget was not raised.
   * A separate directory is used because the period-eleven directory is at ten
     of twelve entries.
   * Scope: within-group and across-group statements are proved; assembling them
     into one nodup over the whole list is not done, as at the shorter levels. -/

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartE

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

local notation "orbitStates" => tribonacciOrbitStates

theorem eleven_g08_g09_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG09.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG09, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit33,
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

theorem eleven_g08_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG10, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g08_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG11, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g08_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG12, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g08_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG13, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g08_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG14, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g08_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG15, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g08_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG16, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g08_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG17, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g08_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG18, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g08_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG08.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG08, elevenOrbitsG19, tribonacciPeriodElevenOrbit29,
      tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
      tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g09_g10_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG10.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG10, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit37,
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

theorem eleven_g09_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG11, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g09_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG12, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g09_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG13, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g09_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG14, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g09_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG15, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g09_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG16, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g09_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG17, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g09_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG18, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g09_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG09.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG09, elevenOrbitsG19, tribonacciPeriodElevenOrbit33,
      tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
      tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g10_g11_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG11.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG11, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit41,
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

theorem eleven_g10_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG12, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g10_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG13, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g10_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG14, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g10_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG15, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g10_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG16, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g10_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG17, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g10_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG18, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g10_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG10.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG10, elevenOrbitsG19, tribonacciPeriodElevenOrbit37,
      tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
      tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g11_g12_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG12.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG12, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit45,
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

theorem eleven_g11_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG13, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g11_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG14, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g11_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG15, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g11_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG16, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit61,
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

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartE