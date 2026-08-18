/- GID: D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartA
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicElevenDistinct/PartA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period-eleven phase codes, part A: group definitions and within-group nodup. -/

import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenMaximinE

/- Library-search audit trail (2026-08-18):
   * Grouping is by four here, not by five as at the shorter levels.  Five was
     tried first and every across-group statement hit the default heartbeat
     budget; a probe showed three and four both clear it, and four gives the
     fewest pairs among the workable sizes.  The budget was not raised.
   * A separate directory is used because the period-eleven directory is at ten
     of twelve entries.
   * Scope: within-group and across-group statements are proved; assembling them
     into one nodup over the whole list is not done, as at the shorter levels. -/

namespace D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData

local notation "orbitStates" => tribonacciOrbitStates

def elevenOrbitsG01 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit01, tribonacciPeriodElevenOrbit02,
    tribonacciPeriodElevenOrbit03, tribonacciPeriodElevenOrbit04]

def elevenOrbitsG02 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit05, tribonacciPeriodElevenOrbit06,
    tribonacciPeriodElevenOrbit07, tribonacciPeriodElevenOrbit08]

def elevenOrbitsG03 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit09, tribonacciPeriodElevenOrbit10,
    tribonacciPeriodElevenOrbit11, tribonacciPeriodElevenOrbit12]

def elevenOrbitsG04 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit13, tribonacciPeriodElevenOrbit14,
    tribonacciPeriodElevenOrbit15, tribonacciPeriodElevenOrbit16]

def elevenOrbitsG05 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit17, tribonacciPeriodElevenOrbit18,
    tribonacciPeriodElevenOrbit19, tribonacciPeriodElevenOrbit20]

def elevenOrbitsG06 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit21, tribonacciPeriodElevenOrbit22,
    tribonacciPeriodElevenOrbit23, tribonacciPeriodElevenOrbit24]

def elevenOrbitsG07 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit25, tribonacciPeriodElevenOrbit26,
    tribonacciPeriodElevenOrbit27, tribonacciPeriodElevenOrbit28]

def elevenOrbitsG08 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit29, tribonacciPeriodElevenOrbit30,
    tribonacciPeriodElevenOrbit31, tribonacciPeriodElevenOrbit32]

def elevenOrbitsG09 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit33, tribonacciPeriodElevenOrbit34,
    tribonacciPeriodElevenOrbit35, tribonacciPeriodElevenOrbit36]

def elevenOrbitsG10 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit37, tribonacciPeriodElevenOrbit38,
    tribonacciPeriodElevenOrbit39, tribonacciPeriodElevenOrbit40]

def elevenOrbitsG11 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit41, tribonacciPeriodElevenOrbit42,
    tribonacciPeriodElevenOrbit43, tribonacciPeriodElevenOrbit44]

def elevenOrbitsG12 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit45, tribonacciPeriodElevenOrbit46,
    tribonacciPeriodElevenOrbit47, tribonacciPeriodElevenOrbit48]

def elevenOrbitsG13 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit49, tribonacciPeriodElevenOrbit50,
    tribonacciPeriodElevenOrbit51, tribonacciPeriodElevenOrbit52]

def elevenOrbitsG14 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit53, tribonacciPeriodElevenOrbit54,
    tribonacciPeriodElevenOrbit55, tribonacciPeriodElevenOrbit56]

def elevenOrbitsG15 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit57, tribonacciPeriodElevenOrbit58,
    tribonacciPeriodElevenOrbit59, tribonacciPeriodElevenOrbit60]

def elevenOrbitsG16 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit61, tribonacciPeriodElevenOrbit62,
    tribonacciPeriodElevenOrbit63, tribonacciPeriodElevenOrbit64]

def elevenOrbitsG17 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit65, tribonacciPeriodElevenOrbit66,
    tribonacciPeriodElevenOrbit67, tribonacciPeriodElevenOrbit68]

def elevenOrbitsG18 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit69, tribonacciPeriodElevenOrbit70,
    tribonacciPeriodElevenOrbit71, tribonacciPeriodElevenOrbit72]

def elevenOrbitsG19 : List TribonacciCodedOrbit :=
  [tribonacciPeriodElevenOrbit73, tribonacciPeriodElevenOrbit74]

theorem eleven_g01_state_codes_nodup :
    (elevenOrbitsG01.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG01,
    tribonacciPeriodElevenOrbit01, tribonacciPeriodElevenOrbit02,
      tribonacciPeriodElevenOrbit03, tribonacciPeriodElevenOrbit04,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g02_state_codes_nodup :
    (elevenOrbitsG02.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG02,
    tribonacciPeriodElevenOrbit05, tribonacciPeriodElevenOrbit06,
      tribonacciPeriodElevenOrbit07, tribonacciPeriodElevenOrbit08,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g03_state_codes_nodup :
    (elevenOrbitsG03.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG03,
    tribonacciPeriodElevenOrbit09, tribonacciPeriodElevenOrbit10,
      tribonacciPeriodElevenOrbit11, tribonacciPeriodElevenOrbit12,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g04_state_codes_nodup :
    (elevenOrbitsG04.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG04,
    tribonacciPeriodElevenOrbit13, tribonacciPeriodElevenOrbit14,
      tribonacciPeriodElevenOrbit15, tribonacciPeriodElevenOrbit16,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g05_state_codes_nodup :
    (elevenOrbitsG05.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG05,
    tribonacciPeriodElevenOrbit17, tribonacciPeriodElevenOrbit18,
      tribonacciPeriodElevenOrbit19, tribonacciPeriodElevenOrbit20,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g06_state_codes_nodup :
    (elevenOrbitsG06.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG06,
    tribonacciPeriodElevenOrbit21, tribonacciPeriodElevenOrbit22,
      tribonacciPeriodElevenOrbit23, tribonacciPeriodElevenOrbit24,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g07_state_codes_nodup :
    (elevenOrbitsG07.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG07,
    tribonacciPeriodElevenOrbit25, tribonacciPeriodElevenOrbit26,
      tribonacciPeriodElevenOrbit27, tribonacciPeriodElevenOrbit28,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g08_state_codes_nodup :
    (elevenOrbitsG08.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG08,
    tribonacciPeriodElevenOrbit29, tribonacciPeriodElevenOrbit30,
      tribonacciPeriodElevenOrbit31, tribonacciPeriodElevenOrbit32,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g09_state_codes_nodup :
    (elevenOrbitsG09.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG09,
    tribonacciPeriodElevenOrbit33, tribonacciPeriodElevenOrbit34,
      tribonacciPeriodElevenOrbit35, tribonacciPeriodElevenOrbit36,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g10_state_codes_nodup :
    (elevenOrbitsG10.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG10,
    tribonacciPeriodElevenOrbit37, tribonacciPeriodElevenOrbit38,
      tribonacciPeriodElevenOrbit39, tribonacciPeriodElevenOrbit40,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g11_state_codes_nodup :
    (elevenOrbitsG11.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG11,
    tribonacciPeriodElevenOrbit41, tribonacciPeriodElevenOrbit42,
      tribonacciPeriodElevenOrbit43, tribonacciPeriodElevenOrbit44,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g12_state_codes_nodup :
    (elevenOrbitsG12.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG12,
    tribonacciPeriodElevenOrbit45, tribonacciPeriodElevenOrbit46,
      tribonacciPeriodElevenOrbit47, tribonacciPeriodElevenOrbit48,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g13_state_codes_nodup :
    (elevenOrbitsG13.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG13,
    tribonacciPeriodElevenOrbit49, tribonacciPeriodElevenOrbit50,
      tribonacciPeriodElevenOrbit51, tribonacciPeriodElevenOrbit52,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g14_state_codes_nodup :
    (elevenOrbitsG14.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG14,
    tribonacciPeriodElevenOrbit53, tribonacciPeriodElevenOrbit54,
      tribonacciPeriodElevenOrbit55, tribonacciPeriodElevenOrbit56,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g15_state_codes_nodup :
    (elevenOrbitsG15.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG15,
    tribonacciPeriodElevenOrbit57, tribonacciPeriodElevenOrbit58,
      tribonacciPeriodElevenOrbit59, tribonacciPeriodElevenOrbit60,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g16_state_codes_nodup :
    (elevenOrbitsG16.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG16,
    tribonacciPeriodElevenOrbit61, tribonacciPeriodElevenOrbit62,
      tribonacciPeriodElevenOrbit63, tribonacciPeriodElevenOrbit64,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g17_state_codes_nodup :
    (elevenOrbitsG17.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG17,
    tribonacciPeriodElevenOrbit65, tribonacciPeriodElevenOrbit66,
      tribonacciPeriodElevenOrbit67, tribonacciPeriodElevenOrbit68,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g18_state_codes_nodup :
    (elevenOrbitsG18.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG18,
    tribonacciPeriodElevenOrbit69, tribonacciPeriodElevenOrbit70,
      tribonacciPeriodElevenOrbit71, tribonacciPeriodElevenOrbit72,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

theorem eleven_g19_state_codes_nodup :
    (elevenOrbitsG19.flatMap orbitStates).Nodup := by
  norm_num [elevenOrbitsG19,
    tribonacciPeriodElevenOrbit73, tribonacciPeriodElevenOrbit74,
    tribonacciMakeOrbit, tribonacciOrbitStates,
    tribonacciTraceCode, tribonacciApplyStepCode, tribonacciPathCandidateCode,
    tribonacciPathAffine, tribonacciAffineCompose, tribonacciStepAffine,
    tribonacciIdentityAffine, tribonacciStepTarget, tribonacciCodeDiv,
    tribonacciCodeInv, tribonacciCodeNorm, tribonacciCodeCofactorZero,
    tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo, tribonacciCodeSub,
    tribonacciCodeNeg, tribonacciCodeAdd, tribonacciCodeMul,
    tribonacciCodeOne, tribonacciCodeZero, tribonacciCodeRoot]

end D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA