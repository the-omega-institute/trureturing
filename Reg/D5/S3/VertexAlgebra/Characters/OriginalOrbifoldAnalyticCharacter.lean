import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter

/-! Register the shifted actual character through its complex weight summands. -/

set_option autoImplicit false

noncomputable section

open Complex LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldAnalyticCharacter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
  (actual_leech_low_spectrum)
open _root_.D5.S3.VertexAlgebra.ActualLeechHyperbolic (leechData leech_spec)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal (L)

namespace Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter

structure Params where
  τ : ℂ
  upper : 0 < τ.im

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p n => exp (2 * Real.pi * I * p.τ * (n - 1)) * (multiplicity n : ℂ))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun n : ℕ => ‖a.readout () ⟨τ, hτ⟩ n‖) ∧
    character τ =
      (ambientCharacter τ + (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ 24) / 2 +
        negativeTwistedCharacter τ ∧
    negativeTwistedCharacter τ =
      2048 * ((ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ 24 +
        (ModularForm.eta (τ + 1) / ModularForm.eta ((τ + 1) / 2)) ^ 24) ∧
    character (τ + 1) = character τ

private theorem bridge : (type_of% (@actual_leech_shifted_character)) ↔ arena.Law actual :=
  Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h I (by simp)).1
  change Summable (fun _ : ℕ => ‖(1 : ℂ)‖) at hs
  simp only [norm_one, summable_const_iff, one_ne_zero] at hs

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨I, by simp⟩, 0, 1, ?_⟩
  let mult := _root_.D5.S3.VertexAlgebra.OriginalOrbifoldAnalyticCharacter.multiplicity
  let A := L leechData leech_spec.2.1 leech_spec.2.2.1 0
  have hzero : mult 0 = 1 := by
    change Module.finrank ℂ (A.eigenspace ((0 : ℕ) : ℂ)) = 1
    rw [show ((0 : ℕ) : ℂ) = 0 from Nat.cast_zero]
    exact actual_leech_low_spectrum.2.2.2.1
  have hone : mult 1 = 0 := by
    change Module.finrank ℂ (A.eigenspace ((1 : ℕ) : ℂ)) = 0
    rw [show ((1 : ℕ) : ℂ) = 1 from Nat.cast_one]
    exact actual_leech_low_spectrum.2.2.2.2.1
  change exp (2 * Real.pi * I * I * ((0 : ℕ) - 1 : ℂ)) * (mult 0 : ℂ) ≠
    exp (2 * Real.pi * I * I * ((1 : ℕ) - 1 : ℂ)) * (mult 1 : ℂ)
  simp [hzero, hone, exp_ne_zero]

def family : Registration arena (type_of% (@actual_leech_shifted_character)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_leech_shifted_character, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_leech_shifted_character) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
