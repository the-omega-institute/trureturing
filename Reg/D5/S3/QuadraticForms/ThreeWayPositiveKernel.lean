import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.ThreeWayPositiveKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.ThreeWayPositiveKernel

noncomputable section
universe u v w

abbrev signature : Signature where
  Params := Σ A : Type u, A → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] (U : A →+ A) (q : A → ℝ)
    (_hq : ∀ x, 0 ≤ q x),
    ((∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) ↔
      Nonempty (HilbertRepresentation.{u, u} U (fun x => R.readout () ⟨A, q⟩ x))) ∧
    (∀ M : HilbertRepresentation.{u, v} U q, ∀ x y,
      q (x + y) + q (x + U y) + q (x + U (U y)) = 3 * q x + 3 * q y) ∧
    (∀ (M : HilbertRepresentation.{u, v} U q) (N : HilbertRepresentation.{u, w} U q),
      ∃! e : M.carrier ≃ₗᵢ[ℂ] N.carrier, ∀ x, e (M.label x) = N.label x)

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hh := (h (A := ULift.{u} ℤ) 0 (fun _ => 0) (by intro x; exact le_rfl)).1.mp
    (by intro x y; norm_num)
  obtain ⟨R⟩ := hh
  have hz := R.normSq 0
  change (0 : ℝ) + 1 = ‖R.label 0‖ ^ 2 at hz
  rw [map_zero, norm_zero] at hz
  norm_num at hz

def evidence : Registration arena.{u, v, w}
    (type_of% @_root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel.three_way_hilbert_characterization.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_way_hilbert_characterization.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℝ, ULift.down⟩, ⟨0⟩, ⟨1⟩, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel.three_way_hilbert_characterization.{u, v, w})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.ThreeWayPositiveKernel.unit
  realizationName := `Reg.D5.S3.QuadraticForms.ThreeWayPositiveKernel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ThreeWayPositiveKernel
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.ThreeWayPositiveKernel
