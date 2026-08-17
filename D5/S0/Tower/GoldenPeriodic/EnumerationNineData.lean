/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationNineData
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationNineData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact primitive period-nine orbit certificates for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationEight

namespace D5.S0.Tower.GoldenPeriodic.EnumerationNineData

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight

def goldenPeriodNineOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (17 / 38) (-5 / 19)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .right, .through],
    ⟨.large, qphi (17 / 38) (-5 / 19)⟩⟩
def goldenPeriodNineOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (12 / 19) (-13 / 38)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .right, .through],
    ⟨.large, qphi (12 / 19) (-13 / 38)⟩⟩
def goldenPeriodNineOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 19) (-3 / 19)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .right, .through],
    ⟨.large, qphi (7 / 19) (-3 / 19)⟩⟩
def goldenPeriodNineOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (21 / 38) (-9 / 38)⟩,
    [.left, .left, .left, .right, .through, .left, .left, .right, .through],
    ⟨.large, qphi (21 / 38) (-9 / 38)⟩⟩
def goldenPeriodNineOrbitE : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (14 / 19) (-6 / 19)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .right, .through],
    ⟨.large, qphi (2 / 19) (10 / 19)⟩⟩
def goldenPeriodNineOrbitF : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (25 / 38) (-4 / 19)⟩,
    [.left, .left, .right, .through, .left, .right, .through, .right, .through],
    ⟨.large, qphi (-3 / 38) (23 / 38)⟩⟩
def goldenPeriodNineOrbitG : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (15 / 38) (-1 / 38)⟩,
    [.left, .left, .right, .through, .right, .through, .left, .right, .through],
    ⟨.large, qphi (7 / 19) (13 / 38)⟩⟩
def goldenPeriodNineOrbitH : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (33 / 38) (-3 / 19)⟩,
    [.left, .right, .through, .right, .through, .right, .through, .right, .through],
    ⟨.large, qphi (-3 / 19) (27 / 38)⟩⟩

def goldenPeriodicOrbitRepresentativesExactlyNine : List GoldenCodedOrbit :=
  [goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH]

theorem golden_new_periodic_orbit_count_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.length = 8 := by
  rfl

theorem golden_new_periodic_orbit_lengths_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.map
      (fun orbit => orbit.steps.length) = [9, 9, 9, 9, 9, 9, 9, 9] := by
  rfl

theorem golden_new_periodic_orbit_codes_close_and_are_nodup_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.Forall fun orbit =>
      goldenApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (goldenOrbitStates orbit).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenApplyStepsCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenOrbitStates, goldenTraceCode, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_new_periodic_orbit_low_states_mem_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_nine_orbits_ab_valid :
    goldenCodedOrbitValid goldenPeriodNineOrbitA ∧
      goldenCodedOrbitValid goldenPeriodNineOrbitB := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_nine_orbits_cd_valid :
    goldenCodedOrbitValid goldenPeriodNineOrbitC ∧
      goldenCodedOrbitValid goldenPeriodNineOrbitD := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodNineOrbitC, goldenPeriodNineOrbitD, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_nine_orbits_ef_valid :
    goldenCodedOrbitValid goldenPeriodNineOrbitE ∧
      goldenCodedOrbitValid goldenPeriodNineOrbitF := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodNineOrbitE, goldenPeriodNineOrbitF, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_nine_orbits_gh_valid :
    goldenCodedOrbitValid goldenPeriodNineOrbitG ∧
      goldenCodedOrbitValid goldenPeriodNineOrbitH := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_new_periodic_orbit_representatives_valid_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.Forall goldenCodedOrbitValid := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyNine, List.forall_cons]
  exact ⟨golden_period_nine_orbits_ab_valid.1,
    golden_period_nine_orbits_ab_valid.2, golden_period_nine_orbits_cd_valid.1,
    golden_period_nine_orbits_cd_valid.2, golden_period_nine_orbits_ef_valid.1,
    golden_period_nine_orbits_ef_valid.2, golden_period_nine_orbits_gh_valid.1,
    golden_period_nine_orbits_gh_valid.2, by simp⟩

theorem golden_new_periodic_orbit_state_codes_nodup_nine :
    (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ab_nine :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitA) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitB) := by
  constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodNineOrbitA, goldenPeriodNineOrbitB,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_cd_nine :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitC) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitD) := by
  constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodNineOrbitC, goldenPeriodNineOrbitD,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ef_nine :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitE) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitF) := by
  constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_gh_nine :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitG) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodNineOrbitH) := by
  constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodNineOrbitG, goldenPeriodNineOrbitH,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_nine :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
      (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates) := by
  simpa only [goldenPeriodicOrbitRepresentativesExactlyNine,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨golden_old_new_periodic_orbit_state_codes_disjoint_ab_nine.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_ab_nine.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_cd_nine.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_cd_nine.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_ef_nine.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_ef_nine.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_gh_nine.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_gh_nine.2⟩

theorem golden_period_nine_orbits_ab_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodNineOrbitA.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodNineOrbitB.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitA, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitB, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_nine_orbits_cd_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodNineOrbitC.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodNineOrbitD.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitC, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitD, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_nine_orbits_ef_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodNineOrbitE.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodNineOrbitF.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitE, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitF, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_nine_orbits_gh_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodNineOrbitG.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodNineOrbitH.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitG, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodNineOrbitH, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_new_periodic_orbit_low_arms_bounded_nine :
    goldenPeriodicOrbitRepresentativesExactlyNine.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyNine, List.forall_cons]
  exact ⟨golden_period_nine_orbits_ab_low_arms.1,
    golden_period_nine_orbits_ab_low_arms.2, golden_period_nine_orbits_cd_low_arms.1,
    golden_period_nine_orbits_cd_low_arms.2, golden_period_nine_orbits_ef_low_arms.1,
    golden_period_nine_orbits_ef_low_arms.2, golden_period_nine_orbits_gh_low_arms.1,
    golden_period_nine_orbits_gh_low_arms.2, by simp⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationNineData
