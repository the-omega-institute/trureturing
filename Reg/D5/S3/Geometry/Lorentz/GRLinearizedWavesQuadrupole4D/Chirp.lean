import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Chirp

set_option autoImplicit false

noncomputable section

private abbrev QuadrupoleMatrix := Matrix (Fin 3) (Fin 3) ℝ

abbrev quadrupoleNormSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => QuadrupoleMatrix)

def quadrupoleNormActual : Realization quadrupoleNormSignature :=
  realize quadrupoleNormSignature
    (fun _ p t => binaryQuadrupoleD3 p.1 p.2.1 p.2.2 t) (fun e => nomatch e)

def quadrupoleNormErased : Realization quadrupoleNormSignature :=
  realize quadrupoleNormSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev quadrupoleNormArena : Arena where
  signature := quadrupoleNormSignature
  Law R := ∀ μ r ω t : ℝ,
    (∑ i : Fin 3, ∑ j : Fin 3, (R.readout () ⟨μ, r, ω⟩ t i j) ^ 2) =
      32 * μ ^ 2 * r ^ 4 * ω ^ 6

private theorem quadrupoleNorm_erased_fails : ¬ quadrupoleNormArena.Law quadrupoleNormErased := by
  intro h
  have he := h 1 1 1 0
  change (∑ _i : Fin 3, ∑ _j : Fin 3, (0 : ℝ) ^ 2) = 32 * 1 ^ 2 * 1 ^ 4 * 1 ^ 6 at he
  norm_num at he

def quadrupoleNormFamily :
    Registration quadrupoleNormArena (type_of% (@binaryQuadrupole_third_deriv_norm_sq)) where
  actual := quadrupoleNormActual
  bridge := Iff.rfl
  variation := ⟨binaryQuadrupole_third_deriv_norm_sq, quadrupoleNormErased, quadrupoleNorm_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    quadrupoleNormArena.Law quadrupoleNormActual quadrupoleNormErased quadrupoleNorm_erased_fails
  dependence := by
    intro _
    refine ⟨⟨1, 1, 1⟩, 0, Real.pi / 4, ?_⟩
    intro he
    have h := congrArg (fun A : QuadrupoleMatrix => A 0 0) he
    change 0 + (4 * 1 * 1 ^ 2 * 1 ^ 3) * Real.sin (2 * 1 * 0) =
      0 + (4 * 1 * 1 ^ 2 * 1 ^ 3) * Real.sin (2 * 1 * (Real.pi / 4)) at h
    rw [show (2 : ℝ) * 1 * (Real.pi / 4) = Real.pi / 2 by ring] at h
    norm_num at h

def quadrupoleNormRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@binaryQuadrupole_third_deriv_norm_sq) (Realization quadrupoleNormSignature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.binaryQuadrupole_third_deriv_norm_sq.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Chirp.quadrupoleNormFamily
  realizationSource := none
  generated := false
  arena := .source ⟨quadrupoleNormArena⟩
  objectArena := .source ⟨quadrupoleNormArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quadrupoleNormArena ⟨quadrupoleNormFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quadrupoleNormSignature
    (fun _ p t => binaryQuadrupoleD3 p.1 p.2.1 p.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev chirpMassSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def chirpMassActual : Realization chirpMassSignature :=
  realize chirpMassSignature (fun _ => chirpMass) (fun e => nomatch e)

def chirpMassErased : Realization chirpMassSignature :=
  realize chirpMassSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev chirpMassArena : Arena where
  signature := chirpMassSignature
  Law R := ∀ {m₁ m₂ : ℝ}, 0 < m₁ → 0 < m₂ →
    chirpMass m₁ m₂ ≤ (m₁ + m₂) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) ∧
      (R.readout () m₁ m₂ = (m₁ + m₂) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) ↔ m₁ = m₂)

private theorem chirpMass_erased_fails : ¬ chirpMassArena.Law chirpMassErased := by
  intro h
  have he := (h (m₁ := 1) (m₂ := 1) (by norm_num) (by norm_num)).2.mpr rfl
  change (0 : ℝ) = (1 + 1) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) at he
  have hp : (0 : ℝ) < (1 + 1) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) := by positivity
  exact hp.ne' he.symm

def chirpMassFamily : Registration chirpMassArena (type_of% (@chirpMass_le_equal_mass)) where
  actual := chirpMassActual
  bridge := Iff.rfl
  variation := ⟨@chirpMass_le_equal_mass, chirpMassErased, chirpMass_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    chirpMassArena.Law chirpMassActual chirpMassErased chirpMass_erased_fails
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change chirpMass 1 0 ≠ chirpMass 1 1
    have h0 : chirpMass 1 0 = 0 := by norm_num [chirpMass, Real.zero_rpow]
    have h1 : 0 < chirpMass 1 1 := by unfold chirpMass; positivity
    simpa only [h0] using h1.ne

def chirpMassRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chirpMass_le_equal_mass) (Realization chirpMassSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.chirpMass_le_equal_mass.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Chirp.chirpMassFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chirpMassArena⟩
  objectArena := .source ⟨chirpMassArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chirpMassArena ⟨chirpMassFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize chirpMassSignature (fun _ => chirpMass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D.Chirp
