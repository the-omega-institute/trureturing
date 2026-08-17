/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationElevenData
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationElevenData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact primitive period-eleven orbit certificates for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationTen

namespace D5.S0.Tower.GoldenPeriodic.EnumerationElevenData

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationNine
open D5.S0.Tower.GoldenPeriodic.EnumerationTenData
open D5.S0.Tower.GoldenPeriodic.EnumerationTen

def goldenPeriodElevenOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (89 / 199) (-54 / 199)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .left, .left, .right,
      .through],
    ⟨.small, qphi (89 / 199) (-54 / 199)⟩⟩
def goldenPeriodElevenOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (124 / 199) (-73 / 199)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .right, .through, .right,
      .through],
    ⟨.small, qphi (124 / 199) (-73 / 199)⟩⟩
def goldenPeriodElevenOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (70 / 199) (-38 / 199)⟩,
    [.left, .left, .left, .left, .left, .left, .right, .through, .left, .right,
      .through],
    ⟨.small, qphi (70 / 199) (-38 / 199)⟩⟩
def goldenPeriodElevenOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (105 / 199) (-57 / 199)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .left, .left, .right,
      .through],
    ⟨.small, qphi (105 / 199) (-57 / 199)⟩⟩
def goldenPeriodElevenOrbitE : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (140 / 199) (-76 / 199)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .right, .through,
      .right, .through],
    ⟨.large, qphi (40 / 199) (92 / 199)⟩⟩
def goldenPeriodElevenOrbitF : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (86 / 199) (-41 / 199)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .left, .left, .right,
      .through],
    ⟨.small, qphi (86 / 199) (-41 / 199)⟩⟩
def goldenPeriodElevenOrbitG : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (121 / 199) (-60 / 199)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .right, .through,
      .right, .through],
    ⟨.small, qphi (121 / 199) (-60 / 199)⟩⟩
def goldenPeriodElevenOrbitH : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (67 / 199) (-25 / 199)⟩,
    [.left, .left, .left, .left, .right, .through, .right, .through, .left,
      .right, .through],
    ⟨.small, qphi (67 / 199) (-25 / 199)⟩⟩
def goldenPeriodElevenOrbitI : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (137 / 199) (-63 / 199)⟩,
    [.left, .left, .left, .right, .through, .left, .left, .right, .through,
      .right, .through],
    ⟨.small, qphi (137 / 199) (-63 / 199)⟩⟩
def goldenPeriodElevenOrbitJ : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (83 / 199) (-28 / 199)⟩,
    [.left, .left, .left, .right, .through, .left, .right, .through, .left,
      .right, .through],
    ⟨.small, qphi (83 / 199) (-28 / 199)⟩⟩
def goldenPeriodElevenOrbitK : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (118 / 199) (-47 / 199)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .left, .left,
      .right, .through],
    ⟨.large, qphi (24 / 199) (95 / 199)⟩⟩
def goldenPeriodElevenOrbitL : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (153 / 199) (-66 / 199)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .right, .through,
      .right, .through],
    ⟨.large, qphi (21 / 199) (108 / 199)⟩⟩
def goldenPeriodElevenOrbitM : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (80 / 199) (-15 / 199)⟩,
    [.left, .left, .right, .through, .left, .left, .right, .through, .left,
      .right, .through],
    ⟨.small, qphi (80 / 199) (-15 / 199)⟩⟩
def goldenPeriodElevenOrbitN : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (150 / 199) (-53 / 199)⟩,
    [.left, .left, .right, .through, .left, .right, .through, .right, .through,
      .right, .through],
    ⟨.large, qphi (-14 / 199) (127 / 199)⟩⟩
def goldenPeriodElevenOrbitO : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (131 / 199) (-37 / 199)⟩,
    [.left, .left, .right, .through, .right, .through, .left, .right, .through,
      .right, .through],
    ⟨.large, qphi (94 / 199) (57 / 199)⟩⟩
def goldenPeriodElevenOrbitP : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (77 / 199) (-2 / 199)⟩,
    [.left, .left, .right, .through, .right, .through, .right, .through, .left,
      .right, .through],
    ⟨.large, qphi (75 / 199) (73 / 199)⟩⟩
def goldenPeriodElevenOrbitQ : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (144 / 199) (-27 / 199)⟩,
    [.left, .right, .through, .left, .right, .through, .left, .right, .through,
      .right, .through],
    ⟨.large, qphi (5 / 199) (111 / 199)⟩⟩
def goldenPeriodElevenOrbitR : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (176 / 199) (-33 / 199)⟩,
    [.left, .right, .through, .right, .through, .right, .through, .right,
      .through, .right, .through],
    ⟨.large, qphi (-33 / 199) (143 / 199)⟩⟩

def goldenPeriodElevenOrbitsAD : List GoldenCodedOrbit :=
  [goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB,
    goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD]

def goldenPeriodElevenOrbitsEH : List GoldenCodedOrbit :=
  [goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH]

def goldenPeriodElevenOrbitsIM : List GoldenCodedOrbit :=
  [goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ,
    goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenPeriodElevenOrbitM]

def goldenPeriodElevenOrbitsNR : List GoldenCodedOrbit :=
  [goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
    goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ,
    goldenPeriodElevenOrbitR]

def goldenPeriodicOrbitRepresentativesExactlyEleven : List GoldenCodedOrbit :=
  [goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC,
    goldenPeriodElevenOrbitD, goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI,
    goldenPeriodElevenOrbitJ, goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
    goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR]

theorem golden_new_periodic_orbit_count_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.length = 18 := by
  rfl

theorem golden_new_periodic_orbit_lengths_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.map
      (fun orbit => orbit.steps.length) =
        [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
          11, 11] := by
  rfl

theorem golden_new_periodic_orbit_codes_close_and_are_nodup_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.Forall fun orbit =>
      goldenApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (goldenOrbitStates orbit).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyEleven,
    goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC,
    goldenPeriodElevenOrbitD, goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI,
    goldenPeriodElevenOrbitJ, goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
    goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenApplyStepsCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenOrbitStates, goldenTraceCode, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_new_periodic_orbit_low_states_mem_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyEleven,
    goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB, goldenPeriodElevenOrbitC,
    goldenPeriodElevenOrbitD, goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF,
    goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH, goldenPeriodElevenOrbitI,
    goldenPeriodElevenOrbitJ, goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN, goldenPeriodElevenOrbitO,
    goldenPeriodElevenOrbitP, goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_eleven_orbits_ab_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitA ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitB := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitA, goldenPeriodElevenOrbitB, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_cd_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitC ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitD := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitC, goldenPeriodElevenOrbitD, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_ef_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitE ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitF := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitE, goldenPeriodElevenOrbitF, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_gh_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitG ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitH := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitG, goldenPeriodElevenOrbitH, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_ij_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitI ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitJ := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitI, goldenPeriodElevenOrbitJ, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_kl_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitK ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitL := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitK, goldenPeriodElevenOrbitL,
    goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_mn_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitM ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitN := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitM, goldenPeriodElevenOrbitN,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, goldenOrbitStates,
    goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_op_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitO ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitP := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitO, goldenPeriodElevenOrbitP,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, goldenOrbitStates,
    goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_eleven_orbits_qr_valid :
    goldenCodedOrbitValid goldenPeriodElevenOrbitQ ∧
      goldenCodedOrbitValid goldenPeriodElevenOrbitR := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodElevenOrbitQ, goldenPeriodElevenOrbitR,
    goldenCodedOrbitValid, goldenCodedTraceValid, goldenCodedStateInUnit,
    goldenCodedStepValid, goldenApplyStepsCode, goldenApplyStepCode,
    goldenStepSource, goldenStepTarget, goldenStepAffine, goldenIdentityAffine,
    goldenCodeValue, goldenCodeAdd, goldenCodeMul, goldenCodeOne,
    goldenCodeZero, goldenCodePhi, goldenCodeNeg, goldenOrbitStates,
    goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_new_periodic_orbit_representatives_valid_eleven :
    goldenPeriodicOrbitRepresentativesExactlyEleven.Forall goldenCodedOrbitValid := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyEleven, List.forall_cons]
  exact ⟨golden_period_eleven_orbits_ab_valid.1,
    golden_period_eleven_orbits_ab_valid.2, golden_period_eleven_orbits_cd_valid.1,
    golden_period_eleven_orbits_cd_valid.2, golden_period_eleven_orbits_ef_valid.1,
    golden_period_eleven_orbits_ef_valid.2, golden_period_eleven_orbits_gh_valid.1,
    golden_period_eleven_orbits_gh_valid.2, golden_period_eleven_orbits_ij_valid.1,
    golden_period_eleven_orbits_ij_valid.2, golden_period_eleven_orbits_kl_valid.1,
    golden_period_eleven_orbits_kl_valid.2, golden_period_eleven_orbits_mn_valid.1,
    golden_period_eleven_orbits_mn_valid.2, golden_period_eleven_orbits_op_valid.1,
    golden_period_eleven_orbits_op_valid.2, golden_period_eleven_orbits_qr_valid.1,
    golden_period_eleven_orbits_qr_valid.2, by simp⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationElevenData
