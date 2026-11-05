import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.RealThreePathRepresentation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift

/-! Typed source-bound readout variation for the original C140 statements. -/

open _root_.D5.S3.QuadraticForms.RealThreePathPolar
open _root_.D5.S3.QuadraticForms.RealThreePathRepresentation
open _root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.RealThreePathPolar

noncomputable section
universe u v w

abbrev signature : Signature where
  Params := Σ V : Type u, V → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def noAnchor : ∀ (_ : Empty) (p : Σ V : Type u, V → ℝ), p.1 :=
  fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) noAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) noAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [AddCommGroup V] [Module ℝ V]
    (U : V → V) (q : V → ℝ) (_hq : ∀ x, 0 ≤ q x) (_h : Balance U (fun x => Z.readout () ⟨V, q⟩ x)),
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = (q (x + y) - q (x - y)) / 4) ∧
      (∀ x y, B x y = B y x) ∧
      (∀ x, q x = q 0 + B x x) ∧ (∀ x, 0 ≤ B x x) ∧
      (∀ x, B (U x) (U x) = B x x) ∧
      (∀ x y, B x y + B x (U y) + B (U x) y = 0) ∧
      (∀ x y, B (U x) (U y) = B x y) ∧
      (∀ x, B x x = 0 ↔ x ∈ B.ker) ∧
      (∀ x, x + U x + U (U x) ∈ B.ker)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let q : ULift.{u} ℝ → ℝ := fun x => (x.down + 1) ^ 2
  have hq : ∀ x, 0 ≤ q x := fun _ => sq_nonneg _
  have hz : Balance (id : ULift.{u} ℝ → ULift.{u} ℝ) (fun _ => (0 : ℝ)) := by
    dsimp only [Balance]
    intro x y t
    ring
  obtain ⟨B, hb, hs, hd, hp, rest⟩ := h id q hq hz
  have hh := hd (ULift.up (-1 : ℝ))
  change ((-1 : ℝ) + 1) ^ 2 = (0 + 1) ^ 2 + B _ _ at hh
  norm_num at hh
  linarith [hp (ULift.up (-1 : ℝ))]

def evidence : Registration arena.{u}
    (type_of% @_root_.D5.S3.QuadraticForms.RealThreePathPolar.raw_real_polar.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.QuadraticForms.RealThreePathPolar.raw_real_polar.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℂ, fun x => ‖x.down‖ ^ 2⟩, ⟨0⟩, ⟨1⟩, ?_⟩
    change ‖(0 : ℂ)‖ ^ 2 ≠ ‖(1 : ℂ)‖ ^ 2
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.QuadraticForms.RealThreePathPolar.raw_real_polar.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.RealThreePathPolar.unit
  realizationName := `Reg.D5.S3.QuadraticForms.RealThreePathPolar.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => p.2 x) noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.RealThreePathPolar
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body","body","body","body","body","body","domain","arg" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.RealThreePathPolar
