/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartF
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartF
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part F: across-group statements, block 5. -/

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

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartF

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

local notation "orbitStates" => tribonacciOrbitStates

theorem eleven_g11_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG17, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g11_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG18, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g11_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG11.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG11, elevenOrbitsG19, tribonacciPeriodElevenOrbit41,
      tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
      tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g12_g13_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG13.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG13, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit49,
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

theorem eleven_g12_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG14, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g12_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG15, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g12_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG16, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g12_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG17, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g12_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG18, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g12_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG12.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG12, elevenOrbitsG19, tribonacciPeriodElevenOrbit45,
      tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
      tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g13_g14_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG14.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG14, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit53,
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

theorem eleven_g13_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG15, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g13_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG16, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g13_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG17, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g13_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG18, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g13_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG13.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG13, elevenOrbitsG19, tribonacciPeriodElevenOrbit49,
      tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
      tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g14_g15_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG14.flatMap orbitStates)
      (elevenOrbitsG15.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG14, elevenOrbitsG15, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit57,
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

theorem eleven_g14_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG14.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG14, elevenOrbitsG16, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g14_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG14.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG14, elevenOrbitsG17, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g14_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG14.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG14, elevenOrbitsG18, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g14_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG14.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG14, elevenOrbitsG19, tribonacciPeriodElevenOrbit53,
      tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
      tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g15_g16_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG15.flatMap orbitStates)
      (elevenOrbitsG16.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG15, elevenOrbitsG16, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60, tribonacciPeriodElevenOrbit61,
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

theorem eleven_g15_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG15.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG15, elevenOrbitsG17, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g15_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG15.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG15, elevenOrbitsG18, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g15_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG15.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG15, elevenOrbitsG19, tribonacciPeriodElevenOrbit57,
      tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
      tribonacciPeriodElevenOrbit60, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g16_g17_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG16.flatMap orbitStates)
      (elevenOrbitsG17.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG16, elevenOrbitsG17, tribonacciPeriodElevenOrbit61,
      tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
      tribonacciPeriodElevenOrbit64, tribonacciPeriodElevenOrbit65,
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

theorem eleven_g16_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG16.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG16, elevenOrbitsG18, tribonacciPeriodElevenOrbit61,
      tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
      tribonacciPeriodElevenOrbit64, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g16_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG16.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG16, elevenOrbitsG19, tribonacciPeriodElevenOrbit61,
      tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
      tribonacciPeriodElevenOrbit64, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g17_g18_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG17.flatMap orbitStates)
      (elevenOrbitsG18.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG17, elevenOrbitsG18, tribonacciPeriodElevenOrbit65,
      tribonacciPeriodElevenOrbit66, tribonacciPeriodElevenOrbit67,
      tribonacciPeriodElevenOrbit68, tribonacciPeriodElevenOrbit69,
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

theorem eleven_g17_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG17.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG17, elevenOrbitsG19, tribonacciPeriodElevenOrbit65,
      tribonacciPeriodElevenOrbit66, tribonacciPeriodElevenOrbit67,
      tribonacciPeriodElevenOrbit68, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g18_g19_state_codes_disjoint :
    List.Disjoint (elevenOrbitsG18.flatMap orbitStates)
      (elevenOrbitsG19.flatMap orbitStates) := by
  norm_num [
    elevenOrbitsG18, elevenOrbitsG19, tribonacciPeriodElevenOrbit69,
      tribonacciPeriodElevenOrbit70, tribonacciPeriodElevenOrbit71,
      tribonacciPeriodElevenOrbit72, tribonacciPeriodElevenOrbit73,
      tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartF