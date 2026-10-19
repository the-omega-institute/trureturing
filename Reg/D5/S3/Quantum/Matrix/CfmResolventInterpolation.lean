import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CfmResolventInterpolation
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Quantum.Matrix.CfmResolventInterpolation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Matrix.CfmResolventInterpolation

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop :=
  ∀ (C : Mat) (hC : C.IsHermitian) (_hspec : ∀ i, hC.eigenvalues i < 1)
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Mat →ₗ[ℝ] E),
    let r := fun s : ℝ => (s • (1 : Mat) - C)⁻¹
    R.readout () () ‖L (r 2 * r 4)‖ + ‖L (r 3 * r 4)‖ ^ 2 ≤
    54 * (‖L (r 2 * r 2)‖ ^ 2 + ‖L (r 2 * r 3)‖ ^ 2 + ‖L (r 3 * r 3)‖ ^ 2)

abbrev arena : Arena where
  signature := signature
  Law := theoremLaw.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh : (0 : Mat).IsHermitian := Matrix.isHermitian_zero
  have heig : hh.eigenvalues = 0 := hh.eigenvalues_eq_zero_iff.mpr rfl
  have hs : ∀ i, hh.eigenvalues i < 1 := by intro i; rw [heig]; norm_num
  have hbad := h 0 hh hs (0 : Mat →ₗ[ℝ] ULift.{u} ℝ)
  norm_num [rejected, realize] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def source_registration : Registration arena.{u}
    (type_of% @mixed_resolvent_control.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixed_resolvent_control.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mixed_resolvent_control.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmResolventInterpolation.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CfmResolventInterpolation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmResolventInterpolation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Matrix.CfmResolventInterpolation
