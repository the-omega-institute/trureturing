/- GID: D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact primitive period-twelve orbit certificates for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationEleven

namespace D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration

def goldenPeriodTwelveOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (9 / 20) (-11 / 40)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .left, .left, .left,
      .right, .through],
    ⟨.small, qphi (9 / 20) (-11 / 40)⟩⟩
def goldenPeriodTwelveOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (5 / 8) (-3 / 8)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .left, .right, .through,
      .right, .through],
    ⟨.small, qphi (5 / 8) (-3 / 8)⟩⟩
def goldenPeriodTwelveOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 20) (-1 / 5)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .right, .through, .left,
      .right, .through],
    ⟨.small, qphi (7 / 20) (-1 / 5)⟩⟩
def goldenPeriodTwelveOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (21 / 40) (-3 / 10)⟩,
    [.left, .left, .left, .left, .left, .left, .right, .through, .left, .left,
      .right, .through],
    ⟨.small, qphi (21 / 40) (-3 / 10)⟩⟩
def goldenPeriodTwelveOrbitE : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 10) (-2 / 5)⟩,
    [.left, .left, .left, .left, .left, .left, .right, .through, .right,
      .through, .right, .through],
    ⟨.small, qphi (7 / 10) (-2 / 5)⟩⟩
def goldenPeriodTwelveOrbitF : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (17 / 40) (-9 / 40)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .left, .left, .left,
      .right, .through],
    ⟨.small, qphi (17 / 40) (-9 / 40)⟩⟩
def goldenPeriodTwelveOrbitG : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (3 / 5) (-13 / 40)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .left, .right,
      .through, .right, .through],
    ⟨.small, qphi (3 / 5) (-13 / 40)⟩⟩
def goldenPeriodTwelveOrbitH : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (13 / 40) (-3 / 20)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .right, .through,
      .left, .right, .through],
    ⟨.small, qphi (13 / 40) (-3 / 20)⟩⟩
def goldenPeriodTwelveOrbitI : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (27 / 40) (-7 / 20)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .left, .right,
      .through, .right, .through],
    ⟨.small, qphi (27 / 40) (-7 / 20)⟩⟩
def goldenPeriodTwelveOrbitJ : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (2 / 5) (-7 / 40)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .right, .through,
      .left, .right, .through],
    ⟨.small, qphi (2 / 5) (-7 / 40)⟩⟩
def goldenPeriodTwelveOrbitK : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (23 / 40) (-11 / 40)⟩,
    [.left, .left, .left, .left, .right, .through, .right, .through, .left,
      .left, .right, .through],
    ⟨.small, qphi (23 / 40) (-11 / 40)⟩⟩
def goldenPeriodTwelveOrbitL : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (3 / 4) (-3 / 8)⟩,
    [.left, .left, .left, .left, .right, .through, .right, .through, .right,
      .through, .right, .through],
    ⟨.large, qphi (3 / 8) (3 / 8)⟩⟩
def goldenPeriodTwelveOrbitM : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (13 / 20) (-3 / 10)⟩,
    [.left, .left, .left, .right, .through, .left, .left, .left, .right,
      .through, .right, .through],
    ⟨.small, qphi (13 / 20) (-3 / 10)⟩⟩
def goldenPeriodTwelveOrbitN : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (3 / 8) (-1 / 8)⟩,
    [.left, .left, .left, .right, .through, .left, .left, .right, .through,
      .left, .right, .through],
    ⟨.small, qphi (3 / 8) (-1 / 8)⟩⟩
def goldenPeriodTwelveOrbitO : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (11 / 20) (-9 / 40)⟩,
    [.left, .left, .left, .right, .through, .left, .right, .through, .left,
      .left, .right, .through],
    ⟨.small, qphi (11 / 20) (-9 / 40)⟩⟩
def goldenPeriodTwelveOrbitP : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (29 / 40) (-13 / 40)⟩,
    [.left, .left, .left, .right, .through, .left, .right, .through, .right,
      .through, .right, .through],
    ⟨.large, qphi (1 / 40) (23 / 40)⟩⟩
def goldenPeriodTwelveOrbitQ : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (5 / 8) (-1 / 4)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .left, .right,
      .through, .right, .through],
    ⟨.large, qphi (1 / 8) (1 / 2)⟩⟩
def goldenPeriodTwelveOrbitR : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 20) (-3 / 40)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .right, .through,
      .left, .right, .through],
    ⟨.large, qphi (1 / 5) (19 / 40)⟩⟩
def goldenPeriodTwelveOrbitS : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (31 / 40) (-3 / 10)⟩,
    [.left, .left, .right, .through, .left, .left, .right, .through, .right,
      .through, .right, .through],
    ⟨.large, qphi (19 / 40) (3 / 10)⟩⟩
def goldenPeriodTwelveOrbitT : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (27 / 40) (-9 / 40)⟩,
    [.left, .left, .right, .through, .left, .right, .through, .left, .right,
      .through, .right, .through],
    ⟨.large, qphi (1 / 20) (21 / 40)⟩⟩
def goldenPeriodTwelveOrbitU : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (2 / 5) (-1 / 20)⟩,
    [.left, .left, .right, .through, .left, .right, .through, .right, .through,
      .left, .right, .through],
    ⟨.large, qphi (-1 / 20) (3 / 5)⟩⟩
def goldenPeriodTwelveOrbitV : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (19 / 40) (-3 / 40)⟩,
    [.left, .left, .right, .through, .right, .through, .left, .right, .through,
      .left, .right, .through],
    ⟨.large, qphi (2 / 5) (13 / 40)⟩⟩
def goldenPeriodTwelveOrbitW : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (33 / 40) (-11 / 40)⟩,
    [.left, .left, .right, .through, .right, .through, .right, .through,
      .right, .through, .right, .through],
    ⟨.large, qphi (11 / 20) (11 / 40)⟩⟩
def goldenPeriodTwelveOrbitX : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (17 / 20) (-1 / 5)⟩,
    [.left, .right, .through, .left, .right, .through, .right, .through,
      .right, .through, .right, .through],
    ⟨.large, qphi (1 / 10) (11 / 20)⟩⟩
def goldenPeriodTwelveOrbitY : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (33 / 40) (-3 / 20)⟩,
    [.left, .right, .through, .right, .through, .left, .right, .through,
      .right, .through, .right, .through],
    ⟨.large, qphi (-3 / 40) (13 / 20)⟩⟩

def goldenPeriodTwelveOrbitsAD : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD]
def goldenPeriodTwelveOrbitsEH : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH]
def goldenPeriodTwelveOrbitsIL : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL]
def goldenPeriodTwelveOrbitsMP : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP]
def goldenPeriodTwelveOrbitsQS : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR, goldenPeriodTwelveOrbitS]
def goldenPeriodTwelveOrbitsTV : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU, goldenPeriodTwelveOrbitV]
def goldenPeriodTwelveOrbitsWY : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX, goldenPeriodTwelveOrbitY]

def goldenPeriodicOrbitRepresentativesExactlyTwelve : List GoldenCodedOrbit :=
  [goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB, goldenPeriodTwelveOrbitC,
    goldenPeriodTwelveOrbitD, goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH, goldenPeriodTwelveOrbitI,
    goldenPeriodTwelveOrbitJ, goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN, goldenPeriodTwelveOrbitO,
    goldenPeriodTwelveOrbitP, goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV, goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY]

theorem golden_new_periodic_orbit_count_twelve :
    goldenPeriodicOrbitRepresentativesExactlyTwelve.length = 25 := by
  rfl

theorem golden_new_periodic_orbit_lengths_twelve :
    goldenPeriodicOrbitRepresentativesExactlyTwelve.map
      (fun orbit => orbit.steps.length) =
        [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
          12, 12, 12, 12, 12, 12, 12, 12, 12] := by
  rfl

theorem golden_new_periodic_orbit_low_states_mem_twelve :
    goldenPeriodicOrbitRepresentativesExactlyTwelve.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTwelve,
    goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB, goldenPeriodTwelveOrbitC,
    goldenPeriodTwelveOrbitD, goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH, goldenPeriodTwelveOrbitI,
    goldenPeriodTwelveOrbitJ, goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN, goldenPeriodTwelveOrbitO,
    goldenPeriodTwelveOrbitP, goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitT, goldenPeriodTwelveOrbitU,
    goldenPeriodTwelveOrbitV, goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenPeriodTwelveOrbitY, goldenOrbitStates, goldenTraceCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_twelve_orbits_ab_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitA ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitB := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitA, goldenPeriodTwelveOrbitB,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_cd_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitC ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitD := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitC, goldenPeriodTwelveOrbitD,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_ef_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitE ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitF := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitE, goldenPeriodTwelveOrbitF,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_gh_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitG ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitH := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitG, goldenPeriodTwelveOrbitH,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_ij_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitI ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitJ := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitI, goldenPeriodTwelveOrbitJ,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_kl_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitK ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitL := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitK, goldenPeriodTwelveOrbitL,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_mn_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitM ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitN := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitM, goldenPeriodTwelveOrbitN,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_op_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitO ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitP := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitO, goldenPeriodTwelveOrbitP,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_qr_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitQ ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitR := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitQ, goldenPeriodTwelveOrbitR,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_st_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitS ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitT := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitS, goldenPeriodTwelveOrbitT,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_uv_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitU ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitV := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitU, goldenPeriodTwelveOrbitV,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbits_wx_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitW ∧
      goldenCodedOrbitValid goldenPeriodTwelveOrbitX := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitW, goldenPeriodTwelveOrbitX,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_twelve_orbit_y_valid :
    goldenCodedOrbitValid goldenPeriodTwelveOrbitY := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTwelveOrbitY, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource,
    goldenStepTarget, goldenStepAffine, goldenIdentityAffine, goldenCodeValue,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi,
    goldenCodeNeg, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_new_periodic_orbit_representatives_valid_twelve :
    goldenPeriodicOrbitRepresentativesExactlyTwelve.Forall
      goldenCodedOrbitValid := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyTwelve, List.forall_cons]
  exact ⟨golden_period_twelve_orbits_ab_valid.1,
    golden_period_twelve_orbits_ab_valid.2, golden_period_twelve_orbits_cd_valid.1,
    golden_period_twelve_orbits_cd_valid.2, golden_period_twelve_orbits_ef_valid.1,
    golden_period_twelve_orbits_ef_valid.2, golden_period_twelve_orbits_gh_valid.1,
    golden_period_twelve_orbits_gh_valid.2, golden_period_twelve_orbits_ij_valid.1,
    golden_period_twelve_orbits_ij_valid.2, golden_period_twelve_orbits_kl_valid.1,
    golden_period_twelve_orbits_kl_valid.2, golden_period_twelve_orbits_mn_valid.1,
    golden_period_twelve_orbits_mn_valid.2, golden_period_twelve_orbits_op_valid.1,
    golden_period_twelve_orbits_op_valid.2, golden_period_twelve_orbits_qr_valid.1,
    golden_period_twelve_orbits_qr_valid.2, golden_period_twelve_orbits_st_valid.1,
    golden_period_twelve_orbits_st_valid.2, golden_period_twelve_orbits_uv_valid.1,
    golden_period_twelve_orbits_uv_valid.2, golden_period_twelve_orbits_wx_valid.1,
    golden_period_twelve_orbits_wx_valid.2, golden_period_twelve_orbit_y_valid,
    by simp⟩

end D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelveData
