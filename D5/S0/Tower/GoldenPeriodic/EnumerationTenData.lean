/- GID: D5/S0/Tower/GoldenPeriodic/EnumerationTenData
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenPeriodic/EnumerationTenData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact primitive period-ten orbit certificates for the golden survivor map. -/

import D5.S0.Tower.GoldenPeriodic.EnumerationNine

namespace D5.S0.Tower.GoldenPeriodic.EnumerationTenData

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenPeriodicEnumeration
open D5.S0.Tower.GoldenPeriodic.EnumerationEight
open D5.S0.Tower.GoldenPeriodic.EnumerationNineData
open D5.S0.Tower.GoldenPeriodic.EnumerationNine

def goldenPeriodTenOrbitA : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (5 / 11) (-3 / 11)⟩,
    [.left, .left, .left, .left, .left, .left, .left, .left, .right, .through],
    ⟨.large, qphi (5 / 11) (-3 / 11)⟩⟩
def goldenPeriodTenOrbitB : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 11) (-4 / 11)⟩,
    [.left, .left, .left, .left, .left, .left, .right, .through, .right, .through],
    ⟨.large, qphi (7 / 11) (-4 / 11)⟩⟩
def goldenPeriodTenOrbitC : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (4 / 11) (-2 / 11)⟩,
    [.left, .left, .left, .left, .left, .right, .through, .left, .right, .through],
    ⟨.large, qphi (4 / 11) (-2 / 11)⟩⟩
def goldenPeriodTenOrbitD : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (6 / 11) (-3 / 11)⟩,
    [.left, .left, .left, .left, .right, .through, .left, .left, .right, .through],
    ⟨.large, qphi (6 / 11) (-3 / 11)⟩⟩
def goldenPeriodTenOrbitE : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (8 / 11) (-4 / 11)⟩,
    [.left, .left, .left, .left, .right, .through, .right, .through, .right,
      .through],
    ⟨.large, qphi (8 / 11) (-4 / 11)⟩⟩
def goldenPeriodTenOrbitF : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (7 / 11) (-3 / 11)⟩,
    [.left, .left, .left, .right, .through, .left, .right, .through, .right,
      .through],
    ⟨.large, qphi 0 (6 / 11)⟩⟩
def goldenPeriodTenOrbitG : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (4 / 11) (-1 / 11)⟩,
    [.left, .left, .left, .right, .through, .right, .through, .left, .right,
      .through],
    ⟨.large, qphi (2 / 11) (5 / 11)⟩⟩
def goldenPeriodTenOrbitH : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (8 / 11) (-3 / 11)⟩,
    [.left, .left, .right, .through, .left, .left, .right, .through, .right,
      .through],
    ⟨.large, qphi (5 / 11) (3 / 11)⟩⟩
def goldenPeriodTenOrbitI : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (5 / 11) (-1 / 11)⟩,
    [.left, .left, .right, .through, .left, .right, .through, .left, .right,
      .through],
    ⟨.small, qphi (5 / 11) (-1 / 11)⟩⟩
def goldenPeriodTenOrbitJ : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (9 / 11) (-3 / 11)⟩,
    [.left, .left, .right, .through, .right, .through, .right, .through, .right,
      .through],
    ⟨.large, qphi (6 / 11) (3 / 11)⟩⟩
def goldenPeriodTenOrbitK : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (9 / 11) (-2 / 11)⟩,
    [.left, .right, .through, .left, .right, .through, .right, .through, .right,
      .through],
    ⟨.large, qphi (1 / 11) (6 / 11)⟩⟩

def goldenPeriodicOrbitRepresentativesExactlyTen : List GoldenCodedOrbit :=
  [goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
    goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
    goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
    goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK]

theorem golden_new_periodic_orbit_count_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.length = 11 := by
  rfl

theorem golden_new_periodic_orbit_lengths_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.map
      (fun orbit => orbit.steps.length) = [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10] := by
  rfl

theorem golden_new_periodic_orbit_codes_close_and_are_nodup_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.Forall fun orbit =>
      goldenApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (goldenOrbitStates orbit).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
    goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
    goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
    goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
    goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenApplyStepsCode,
    goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine, goldenStepTarget,
    goldenOrbitStates, goldenTraceCode, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_new_periodic_orbit_low_states_mem_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
    goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
    goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
    goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
    goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_period_ten_orbits_ab_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitA ∧
      goldenCodedOrbitValid goldenPeriodTenOrbitB := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_ten_orbits_cd_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitC ∧
      goldenCodedOrbitValid goldenPeriodTenOrbitD := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitC, goldenPeriodTenOrbitD, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_ten_orbits_ef_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitE ∧
      goldenCodedOrbitValid goldenPeriodTenOrbitF := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitE, goldenPeriodTenOrbitF, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_ten_orbits_gh_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitG ∧
      goldenCodedOrbitValid goldenPeriodTenOrbitH := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_ten_orbits_ij_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitI ∧
      goldenCodedOrbitValid goldenPeriodTenOrbitJ := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_period_ten_orbit_k_valid :
    goldenCodedOrbitValid goldenPeriodTenOrbitK := by
  have hphiLower : (1 : Real) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hphiUpper : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hphiRadical : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodTenOrbitK, goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

theorem golden_new_periodic_orbit_representatives_valid_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.Forall goldenCodedOrbitValid := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyTen, List.forall_cons]
  exact ⟨golden_period_ten_orbits_ab_valid.1,
    golden_period_ten_orbits_ab_valid.2, golden_period_ten_orbits_cd_valid.1,
    golden_period_ten_orbits_cd_valid.2, golden_period_ten_orbits_ef_valid.1,
    golden_period_ten_orbits_ef_valid.2, golden_period_ten_orbits_gh_valid.1,
    golden_period_ten_orbits_gh_valid.2, golden_period_ten_orbits_ij_valid.1,
    golden_period_ten_orbits_ij_valid.2, golden_period_ten_orbit_k_valid, by simp⟩

theorem golden_new_periodic_orbit_state_codes_nodup_ten :
    (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesExactlyTen,
    goldenPeriodTenOrbitA, goldenPeriodTenOrbitB, goldenPeriodTenOrbitC,
    goldenPeriodTenOrbitD, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
    goldenPeriodTenOrbitG, goldenPeriodTenOrbitH, goldenPeriodTenOrbitI,
    goldenPeriodTenOrbitJ, goldenPeriodTenOrbitK, goldenOrbitStates,
    goldenTraceCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_disjoint_from_periods_through_nine
    {states : List GoldenCodedState}
    (hEight : List.Disjoint
      (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates) states)
    (hNine : List.Disjoint
      (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates) states) :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates) states := by
  rw [goldenPeriodicOrbitRepresentativesNine, List.flatMap_append,
    List.disjoint_append_left]
  exact ⟨hEight, hNine⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ab_ten :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitA) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitB) := by
  have hEight :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitA) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitB) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitA, goldenPeriodTenOrbitB,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  have hNine :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitA) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitB) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitA,
    goldenPeriodTenOrbitB,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  exact ⟨golden_disjoint_from_periods_through_nine hEight.1 hNine.1,
    golden_disjoint_from_periods_through_nine hEight.2 hNine.2⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_cd_ten :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitC) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitD) := by
  have hEight :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitC) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitD) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitC, goldenPeriodTenOrbitD,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  have hNine :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitC) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitD) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitC,
    goldenPeriodTenOrbitD,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  exact ⟨golden_disjoint_from_periods_through_nine hEight.1 hNine.1,
    golden_disjoint_from_periods_through_nine hEight.2 hNine.2⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ef_ten :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitE) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitF) := by
  have hEight :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitE) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitF) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitE, goldenPeriodTenOrbitF,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  have hNine :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitE) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitF) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitE,
    goldenPeriodTenOrbitF,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  exact ⟨golden_disjoint_from_periods_through_nine hEight.1 hNine.1,
    golden_disjoint_from_periods_through_nine hEight.2 hNine.2⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_gh_ten :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitG) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitH) := by
  have hEight :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitG) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitH) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitG, goldenPeriodTenOrbitH,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  have hNine :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitG) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitH) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitG,
    goldenPeriodTenOrbitH,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  exact ⟨golden_disjoint_from_periods_through_nine hEight.1 hNine.1,
    golden_disjoint_from_periods_through_nine hEight.2 hNine.2⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ij_ten :
    List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitI) ∧
      List.Disjoint
        (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
        (goldenOrbitStates goldenPeriodTenOrbitJ) := by
  have hEight :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitI) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesEight.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitJ) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitI, goldenPeriodTenOrbitJ,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  have hNine :
      List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitI) ∧
        List.Disjoint
          (goldenPeriodicOrbitRepresentativesExactlyNine.flatMap goldenOrbitStates)
          (goldenOrbitStates goldenPeriodTenOrbitJ) := by
    constructor <;> norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitI,
    goldenPeriodTenOrbitJ,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  exact ⟨golden_disjoint_from_periods_through_nine hEight.1 hNine.1,
    golden_disjoint_from_periods_through_nine hEight.2 hNine.2⟩

theorem golden_old_new_periodic_orbit_state_codes_disjoint_k_ten :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenOrbitStates goldenPeriodTenOrbitK) := by
  apply golden_disjoint_from_periods_through_nine
  · norm_num [goldenPeriodicOrbitRepresentativesEight,
    goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenPeriodicOrbitRepresentativesExactlyEight, goldenPeriodEightOrbitA,
    goldenPeriodEightOrbitB, goldenPeriodEightOrbitC, goldenPeriodEightOrbitD,
    goldenPeriodEightOrbitE, goldenPeriodTenOrbitK,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  · norm_num [goldenPeriodicOrbitRepresentativesExactlyNine,
    goldenPeriodNineOrbitA, goldenPeriodNineOrbitB, goldenPeriodNineOrbitC,
    goldenPeriodNineOrbitD, goldenPeriodNineOrbitE, goldenPeriodNineOrbitF,
    goldenPeriodNineOrbitG, goldenPeriodNineOrbitH, goldenPeriodTenOrbitK,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

theorem golden_old_new_periodic_orbit_state_codes_disjoint_ten :
    List.Disjoint
      (goldenPeriodicOrbitRepresentativesNine.flatMap goldenOrbitStates)
      (goldenPeriodicOrbitRepresentativesExactlyTen.flatMap goldenOrbitStates) := by
  simpa only [goldenPeriodicOrbitRepresentativesExactlyTen,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.disjoint_append_right] using
      ⟨golden_old_new_periodic_orbit_state_codes_disjoint_ab_ten.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_ab_ten.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_cd_ten.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_cd_ten.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_ef_ten.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_ef_ten.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_gh_ten.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_gh_ten.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_ij_ten.1,
        golden_old_new_periodic_orbit_state_codes_disjoint_ij_ten.2,
        golden_old_new_periodic_orbit_state_codes_disjoint_k_ten⟩

theorem golden_period_ten_orbits_ab_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitA.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTenOrbitB.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitA, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitB, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_ten_orbits_cd_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitC.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTenOrbitD.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitC, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitD, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_ten_orbits_ef_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitE.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTenOrbitF.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitE, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitF, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_ten_orbits_gh_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitG.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTenOrbitH.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitG, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitH, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_ten_orbits_ij_low_arms :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitI.lowState) ≤
        goldenThreshold ∧
      goldenStateArm (decodeGoldenState goldenPeriodTenOrbitJ.lowState) ≤
        goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  constructor
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitI, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]
  · rw [golden_threshold_eq, golden_inverse_sq]
    norm_num [goldenPeriodTenOrbitJ, goldenStateArm, decodeGoldenState,
      goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
    all_goals try split_ifs with h
    all_goals simp only [hsqrtForm] at *
    all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
      Real.goldenRatio_lt_two]

theorem golden_period_ten_orbit_k_low_arm :
    goldenStateArm (decodeGoldenState goldenPeriodTenOrbitK.lowState) ≤
      goldenThreshold := by
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * Real.goldenRatio := by
    linarith [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 from rfl]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodTenOrbitK, goldenStateArm, decodeGoldenState,
    goldenCodeValue, qphi, golden_inverse_eq_sub_one, min_def]
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

theorem golden_new_periodic_orbit_low_arms_bounded_ten :
    goldenPeriodicOrbitRepresentativesExactlyTen.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  simp only [goldenPeriodicOrbitRepresentativesExactlyTen, List.forall_cons]
  exact ⟨golden_period_ten_orbits_ab_low_arms.1,
    golden_period_ten_orbits_ab_low_arms.2, golden_period_ten_orbits_cd_low_arms.1,
    golden_period_ten_orbits_cd_low_arms.2, golden_period_ten_orbits_ef_low_arms.1,
    golden_period_ten_orbits_ef_low_arms.2, golden_period_ten_orbits_gh_low_arms.1,
    golden_period_ten_orbits_gh_low_arms.2, golden_period_ten_orbits_ij_low_arms.1,
    golden_period_ten_orbits_ij_low_arms.2, golden_period_ten_orbit_k_low_arm,
    by simp⟩

end D5.S0.Tower.GoldenPeriodic.EnumerationTenData
