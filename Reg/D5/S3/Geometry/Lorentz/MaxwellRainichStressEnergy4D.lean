import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
import Reg.Support.SingleDependentReadout

/-! Whole-family interventions for MaxwellRainichStressEnergy4D. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open _root_.D5.S3.Geometry.Lorentz
open Matrix
open scoped Matrix

namespace Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

local macro "family% " arena:term:max source:term:max actual:term:max witness:term:max
    bad:term:max rejected:term:max : term =>
  `({ actual := $actual
      bridge := Iff.rfl
      variation := ⟨$source, $bad, $rejected⟩
      sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
        ($arena).Law $actual $bad $rejected
      dependence := fun _ => $witness })

local macro "bindSource% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max path:term:max state:term:max function:term:max
    operand:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := { stage := .evidence, objectStage := .evidence }
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
        definition := none
        coordinates := $coordinates
        readouts := #[{
          path := $path
          stateBinder := $state
          functionOperand := $function
          stateOperand := $operand
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

private def axis : V3 := ![1, 0, 0]

private abbrev SkewM4 := {F : M4 // Fᵀ = -F}

abbrev matrixReadout : Signature := signature V3 (fun _ => V3) (fun _ => M4)

abbrev scalarReadout : Signature := signature V3 (fun _ => V3) (fun _ => ℝ)

abbrev skewReadout : Signature := signature Unit (fun _ => V3 × V3) (fun _ => SkewM4)

private def eraseMatrix (A : M4) : Realization matrixReadout :=
  realize matrixReadout (fun _ _ _ => A) (fun e => nomatch e)

private def eraseScalar (c : ℝ) : Realization scalarReadout :=
  realize scalarReadout (fun _ _ _ => c) (fun e => nomatch e)

private def eraseSkew : Realization skewReadout :=
  realize skewReadout (fun _ _ _ => ⟨0, by simp⟩) (fun e => nomatch e)

private theorem field_zero : fieldTensor 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldTensor]

private theorem tensor_zero : fieldOfTensor 0 = (0, 0) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [fieldOfTensor]

private theorem stress_zero : maxwellStressMixed 0 0 = 0 := by
  rw [maxwellStressMixed, field_zero]
  change eta4 * 0 * eta4 * 0 - ((1 / 4 : ℝ) * (eta4 * 0 * eta4 * 0).trace) • (1 : M4) = 0
  simp

private theorem stress_cov_zero : maxwellStressCov 0 0 = 0 := by
  simp [maxwellStressCov, stress_zero]

private theorem stress_axis : maxwellStressMixed 0 axis 0 0 = 1 / 2 := by
  rw [(maxwell_energy_and_poynting 0 axis).1]
  norm_num [axis, energyDensity, spatialNormSq]

private theorem stress_cov_axis : maxwellStressCov 0 axis 0 0 = 1 / 2 := by
  simp [maxwellStressCov, SL2CLorentzCover4D.eta, Matrix.diagonal_mul, stress_axis]

private theorem field_varies : fieldTensor 0 0 ≠ fieldTensor 0 axis := by
  intro h
  have he := congrArg (fun A : M4 => A 2 3) h
  norm_num [fieldTensor, axis] at he

private theorem stress_varies : maxwellStressMixed 0 0 ≠ maxwellStressMixed 0 axis := by
  intro h
  have he := congrArg (fun A : M4 => A 0 0) h
  norm_num [stress_zero, stress_axis] at he

private theorem stress_cov_varies : maxwellStressCov 0 0 ≠ maxwellStressCov 0 axis := by
  intro h
  have he := congrArg (fun A : M4 => A 0 0) h
  norm_num [stress_cov_zero, stress_cov_axis] at he

private theorem energy_varies : energyDensity 0 0 ≠ energyDensity 0 axis := by
  norm_num [energyDensity, spatialNormSq, axis]

private theorem dot_varies : spatialDot axis 0 ≠ spatialDot axis axis := by
  norm_num [spatialDot, axis]

private theorem inv2_varies : maxwellInv2 axis 0 ≠ maxwellInv2 axis axis := by
  rw [(maxwell_invariants_explicit axis 0).2, (maxwell_invariants_explicit axis axis).2]
  exact dot_varies

private theorem norm_varies : spatialNormSq 0 ≠ spatialNormSq axis := by
  norm_num [spatialNormSq, axis]

abbrev normReadout : Signature := signature Unit (fun _ => V3) (fun _ => ℝ)

private def eraseNorm (c : ℝ) : Realization normReadout :=
  realize normReadout (fun _ _ _ => c) (fun e => nomatch e)

abbrev antisymArena : Arena where
  signature := matrixReadout
  Law R := ∀ (E B : V3),
    ((R.readout () E B))ᵀ = -fieldTensor E B

def antisymFamily : Registration antisymArena (type_of% @fieldTensor_antisym) :=
  family% antisymArena (@fieldTensor_antisym) (realize matrixReadout (fun _ => fieldTensor) (fun e => nomatch e))
    (⟨0, 0, axis, field_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := congrArg (fun A : M4 => A 0 0) (h 0 0)
      simp [eraseMatrix, realize, field_zero] at he)

def antisymRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fieldTensor_antisym) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.fieldTensor_antisym.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.antisymFamily
    antisymArena antisymFamily (realize matrixReadout (fun _ => fieldTensor) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "arg"] 1 false none

abbrev dualSquareArena : Arena where
  signature := matrixReadout
  Law R := ∀ (E B : V3),
    dualFieldTensor (-B) E = -(R.readout () E B)

def dualSquareFamily : Registration dualSquareArena (type_of% @dualFieldTensor_sq) :=
  family% dualSquareArena (@dualFieldTensor_sq) (realize matrixReadout (fun _ => fieldTensor) (fun e => nomatch e))
    (⟨0, 0, axis, field_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := congrArg (fun A : M4 => A 0 0) (h 0 0)
      simp [eraseMatrix, realize, dualFieldTensor, field_zero] at he)

def dualSquareRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dualFieldTensor_sq) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.dualFieldTensor_sq.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.dualSquareFamily
    dualSquareArena dualSquareFamily (realize matrixReadout (fun _ => fieldTensor) (fun e => nomatch e))
    #[0] #["body", "body", "arg", "arg"] 1 false none

abbrev bijectiveArena : Arena where
  signature := skewReadout
  Law R := Function.Bijective (fun EB => R.readout () () EB)

def bijectiveFamily : Registration bijectiveArena (type_of% @fieldTensor_bijective) :=
  family% bijectiveArena (@fieldTensor_bijective) (realize skewReadout (fun _ => (fun _ EB => ⟨fieldTensor EB.1 EB.2, fieldTensor_antisym EB.1 EB.2⟩)) (fun e => nomatch e))
    (by
      refine ⟨(), (0, 0), (axis, 0), ?_⟩
      intro h
      have he := congrArg (fun A : SkewM4 => A.val 0 1) h
      norm_num [realize, fieldTensor, axis] at he)
    (eraseSkew)
    (by
      intro h
      have he := h.1 (a₁ := ((0, 0) : V3 × V3)) (a₂ := (axis, 0)) rfl
      have hh := congrArg (fun EB : V3 × V3 => EB.1 0) he
      norm_num [axis] at hh)

def bijectiveRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fieldTensor_bijective) (Realization skewReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.fieldTensor_bijective.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.bijectiveFamily
    bijectiveArena bijectiveFamily (realize skewReadout (fun _ => (fun _ EB => ⟨fieldTensor EB.1 EB.2, fieldTensor_antisym EB.1 EB.2⟩)) (fun e => nomatch e))
    #[] #["arg", "body"] 0 false none

abbrev invariantsArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3),
    maxwellInv1 (fieldTensor E B) = spatialNormSq B - spatialNormSq E ∧
    (R.readout () E B) = spatialDot E B

def invariantsFamily : Registration invariantsArena (type_of% @maxwell_invariants_explicit) :=
  family% invariantsArena (@maxwell_invariants_explicit) (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    (⟨axis, 0, axis, inv2_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      have he := (h 0 0).2
      norm_num [eraseScalar, realize, spatialDot] at he)

def invariantsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_invariants_explicit) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_invariants_explicit.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.invariantsFamily
    invariantsArena invariantsFamily (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    #[0] #["body", "body", "arg", "fn", "arg"] 1 false none

abbrev determinantArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3),
    (fieldTensor E B).det = ((R.readout () E B)) ^ 2

def determinantFamily : Registration determinantArena (type_of% @fieldTensor_det) :=
  family% determinantArena (@fieldTensor_det) (realize scalarReadout (fun _ => spatialDot) (fun e => nomatch e))
    (⟨axis, 0, axis, dot_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      have he := h 0 0
      norm_num [eraseScalar, realize, field_zero] at he)

def determinantRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fieldTensor_det) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.fieldTensor_det.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.determinantFamily
    determinantArena determinantFamily (realize scalarReadout (fun _ => spatialDot) (fun e => nomatch e))
    #[0] #["body", "body", "arg", "fn", "arg"] 1 false none

abbrev invariantPullbackArena : Arena where
  signature := scalarReadout
  Law R := ∀ (Λ : M4) (E B : V3)
    (_hΛ : Λᵀ * eta4 * Λ = eta4) (_hor : Λ.det = 1),
    let F' := Λᵀ * fieldTensor E B * Λ
    let EB' := fieldOfTensor F'
    maxwellInv1 F' = maxwellInv1 (fieldTensor E B) ∧
    spatialNormSq EB'.2 - spatialNormSq EB'.1 = spatialNormSq B - spatialNormSq E ∧
    maxwellInv2 EB'.1 EB'.2 = (R.readout () E B) ∧
    spatialDot EB'.1 EB'.2 = spatialDot E B

def invariantPullbackFamily : Registration invariantPullbackArena (type_of% @maxwell_invariants_lorentz_invariant) :=
  family% invariantPullbackArena (@maxwell_invariants_lorentz_invariant) (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    (⟨axis, 0, axis, inv2_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      have he := (h 1 0 0 (by simp) (by simp)).2.2.1
      norm_num [eraseScalar, realize, field_zero, tensor_zero, maxwellInv2,
        dualFieldTensor] at he)

def invariantPullbackRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_invariants_lorentz_invariant) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_invariants_lorentz_invariant.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.invariantPullbackFamily
    invariantPullbackArena invariantPullbackFamily (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    #[1] #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"] 2 false none

abbrev symmetricArena : Arena where
  signature := matrixReadout
  Law R := ∀ (E B : V3),
    ((R.readout () E B))ᵀ = maxwellStressCov E B

def symmetricFamily : Registration symmetricArena (type_of% @maxwell_stress_symmetric) :=
  family% symmetricArena (@maxwell_stress_symmetric) (realize matrixReadout (fun _ => maxwellStressCov) (fun e => nomatch e))
    (⟨0, 0, axis, stress_cov_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := congrArg (fun A : M4 => A 0 0) (h 0 0)
      simp [eraseMatrix, realize, stress_cov_zero] at he)

def symmetricRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_stress_symmetric) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_stress_symmetric.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.symmetricFamily
    symmetricArena symmetricFamily (realize matrixReadout (fun _ => maxwellStressCov) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "arg"] 1 false none

abbrev tracelessArena : Arena where
  signature := matrixReadout
  Law R := ∀ (E B : V3),
    ((R.readout () E B)).trace = 0

def tracelessFamily : Registration tracelessArena (type_of% @maxwell_stress_traceless) :=
  family% tracelessArena (@maxwell_stress_traceless) (realize matrixReadout (fun _ => maxwellStressMixed) (fun e => nomatch e))
    (⟨0, 0, axis, stress_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := h 0 0
      norm_num [eraseMatrix, realize, Matrix.trace_one] at he)

def tracelessRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_stress_traceless) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_stress_traceless.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.tracelessFamily
    tracelessArena tracelessFamily (realize matrixReadout (fun _ => maxwellStressMixed) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "arg"] 1 false none

abbrev componentsArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3),
    maxwellStressMixed E B 0 0 = (R.readout () E B) ∧
    (∀ i : Fin 3, maxwellStressMixed E B 0 i.succ = -spatialCross E B i) ∧
    (∀ i : Fin 3, maxwellStressContra E B 0 i.succ = spatialCross E B i) ∧
    ∀ i j : Fin 3, maxwellStressContra E B i.succ j.succ =
      -E i * E j - B i * B j + if i = j then energyDensity E B else 0

def componentsFamily : Registration componentsArena (type_of% @maxwell_energy_and_poynting) :=
  family% componentsArena (@maxwell_energy_and_poynting) (realize scalarReadout (fun _ => energyDensity) (fun e => nomatch e))
    (⟨0, 0, axis, energy_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      have he := (h 0 0).1
      norm_num [eraseScalar, realize, stress_zero] at he)

def componentsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_energy_and_poynting) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_energy_and_poynting.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.componentsFamily
    componentsArena componentsFamily (realize scalarReadout (fun _ => energyDensity) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "arg"] 1 false none

abbrev covariantArena : Arena where
  signature := matrixReadout
  Law R := ∀ (Λ : M4) (E B : V3)
    (_hΛ : Λᵀ * eta4 * Λ = eta4),
    let EB' := fieldOfTensor (Λᵀ * fieldTensor E B * Λ)
    maxwellStressCov EB'.1 EB'.2 = Λᵀ * (R.readout () E B) * Λ

def covariantFamily : Registration covariantArena (type_of% @maxwell_stress_lorentz_covariant) :=
  family% covariantArena (@maxwell_stress_lorentz_covariant) (realize matrixReadout (fun _ => maxwellStressCov) (fun e => nomatch e))
    (⟨0, 0, axis, stress_cov_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := h 1 0 0 (by simp)
      simp [eraseMatrix, realize, field_zero, tensor_zero, stress_cov_zero] at he)

def covariantRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_stress_lorentz_covariant) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_stress_lorentz_covariant.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.covariantFamily
    covariantArena covariantFamily (realize matrixReadout (fun _ => maxwellStressCov) (fun e => nomatch e))
    #[1] #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"] 2 false none

abbrev dualityArena : Arena where
  signature := matrixReadout
  Law R := ∀ (E B : V3) (θ : ℝ),
    let E' : V3 := Real.cos θ • E + Real.sin θ • B
    let B' : V3 := -Real.sin θ • E + Real.cos θ • B
    maxwellStressMixed E' B' = (R.readout () E B) ∧
    maxwellStressCov E' B' = maxwellStressCov E B

def dualityFamily : Registration dualityArena (type_of% @maxwell_duality_rotation_invariant) :=
  family% dualityArena (@maxwell_duality_rotation_invariant) (realize matrixReadout (fun _ => maxwellStressMixed) (fun e => nomatch e))
    (⟨0, 0, axis, stress_varies⟩)
    (eraseMatrix 1)
    (by
      intro h
      have he := (h 0 0 0).1
      simp [eraseMatrix, realize, stress_zero] at he)

def dualityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_duality_rotation_invariant) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_duality_rotation_invariant.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.dualityFamily
    dualityArena dualityFamily (realize matrixReadout (fun _ => maxwellStressMixed) (fun e => nomatch e))
    #[0] #["body", "body", "body", "body", "body", "fn", "arg", "arg"] 1 false none

abbrev poyntingBoundArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3),
    Real.sqrt (spatialNormSq (spatialCross E B)) ≤ (R.readout () E B) ∧
    (Real.sqrt (spatialNormSq (spatialCross E B)) = energyDensity E B ↔
      spatialNormSq E = spatialNormSq B ∧ spatialDot E B = 0)

def poyntingBoundFamily : Registration poyntingBoundArena (type_of% @poynting_le_energy_density) :=
  family% poyntingBoundArena (@poynting_le_energy_density) (realize scalarReadout (fun _ => energyDensity) (fun e => nomatch e))
    (⟨0, 0, axis, energy_varies⟩)
    (eraseScalar (-1))
    (by
      intro h
      have hu := (h 0 0).1
      exact (not_le_of_gt (show (-1 : ℝ) < 0 by norm_num))
        ((Real.sqrt_nonneg _).trans hu))

def poyntingBoundRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@poynting_le_energy_density) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.poynting_le_energy_density.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.poyntingBoundFamily
    poyntingBoundArena poyntingBoundFamily (realize scalarReadout (fun _ => energyDensity) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "arg"] 1 false none

abbrev rainichArena : Arena where
  signature := normReadout
  Law R := ∀ (E B : V3),
    maxwellStressMixed E B * maxwellStressMixed E B =
      ((1 / 4 : ℝ) * (((R.readout () () B) - spatialNormSq E) ^ 2 +
        4 * spatialDot E B ^ 2)) • (1 : M4)

def rainichFamily : Registration rainichArena (type_of% @maxwell_rainich_square_identity) :=
  family% rainichArena (@maxwell_rainich_square_identity) (realize normReadout (fun _ _ B => spatialNormSq B) (fun e => nomatch e))
    (⟨(), 0, axis, norm_varies⟩)
    (eraseNorm 1)
    (by
      intro h
      have he := congrArg (fun A : M4 => A 0 0) (h 0 0)
      norm_num [eraseNorm, realize, stress_zero, spatialNormSq, spatialDot,
        Matrix.one_apply] at he)

def rainichRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_rainich_square_identity) (Realization normReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_rainich_square_identity.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.rainichFamily
    rainichArena rainichFamily (realize normReadout (fun _ _ B => spatialNormSq B) (fun e => nomatch e))
    #[] #["body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg"] 1 false none

abbrev nilpotentArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3),
    maxwellStressMixed E B * maxwellStressMixed E B = 0 ↔
      spatialNormSq E = spatialNormSq B ∧ (R.readout () E B) = 0

def nilpotentFamily : Registration nilpotentArena (type_of% @maxwell_stress_nilpotent_iff_null) :=
  family% nilpotentArena (@maxwell_stress_nilpotent_iff_null) (realize scalarReadout (fun _ => spatialDot) (fun e => nomatch e))
    (⟨axis, 0, axis, dot_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      have he := ((h 0 0).1 (by simp [stress_zero])).2
      norm_num [eraseScalar, realize] at he)

def nilpotentRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_stress_nilpotent_iff_null) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_stress_nilpotent_iff_null.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.nilpotentFamily
    nilpotentArena nilpotentFamily (realize scalarReadout (fun _ => spatialDot) (fun e => nomatch e))
    #[0] #["body", "body", "arg", "arg", "fn", "arg"] 1 false none

abbrev dominantEnergyArena : Arena where
  signature := scalarReadout
  Law R := ∀ (E B : V3) (u : V4)
    (_ht : 0 ≤ u 0) (_hu : 0 ≤ minkowskiNormSq u),
    let j := maxwellStressMixed E B *ᵥ u
    0 ≤ u ⬝ᵥ (maxwellStressCov E B *ᵥ u) ∧ 0 ≤ j 0 ∧ 0 ≤ minkowskiNormSq j ∧
    minkowskiNormSq j =
      ((maxwellInv1 (fieldTensor E B) ^ 2 + 4 * (R.readout () E B) ^ 2) / 4) *
        minkowskiNormSq u

def dominantEnergyFamily : Registration dominantEnergyArena (type_of% @maxwell_dominant_energy_condition) :=
  family% dominantEnergyArena (@maxwell_dominant_energy_condition) (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    (⟨axis, 0, axis, inv2_varies⟩)
    (eraseScalar 1)
    (by
      intro h
      let u : V4 := ![1, 0, 0, 0]
      have ht : 0 ≤ u 0 := by norm_num [u]
      have hu : 0 ≤ minkowskiNormSq u := by
        norm_num [u, SL2CLorentzCover4D.minkowskiNormSq]
      have he := (h 0 0 u ht hu).2.2.2
      norm_num [eraseScalar, realize, u, stress_zero, field_zero, maxwellInv1,
        SL2CLorentzCover4D.minkowskiNormSq] at he)

def dominantEnergyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@maxwell_dominant_energy_condition) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.maxwell_dominant_energy_condition.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.dominantEnergyFamily
    dominantEnergyArena dominantEnergyFamily (realize scalarReadout (fun _ => maxwellInv2) (fun e => nomatch e))
    #[0] #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "arg"] 1 false none

end

end Reg.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
