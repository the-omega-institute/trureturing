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

namespace Reg.D5.S3.QuadraticForms.RealThreePathRepresentationQuotient

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

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [AddCommGroup V] [Module ℝ V]
    (U : V → V) (q : V → ℝ) (_hq : ∀ x, 0 ≤ q x) (_h : Balance U (fun x => Z.readout () ⟨V, q⟩ x)),
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = (q (x + y) - q (x - y)) / 4) ∧
      (∀ x y, B x y = B y x) ∧
      (∀ x, q x = q 0 + B x x) ∧
      (∀ x, B x x = 0 ↔ x ∈ B.ker) ∧
      ∃ (g : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker) →ₗ[ℝ] ℝ)
        (T : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker)),
        (∀ x y, g (B.ker.mkQ x) (B.ker.mkQ y) = B x y) ∧
        (∀ z, 0 ≤ g z z) ∧ (∀ z, g z z = 0 ↔ z = 0) ∧
        (∀ x, T (B.ker.mkQ x) = B.ker.mkQ (U x)) ∧
        (∀ z w, g (T z) (T w) = g z w) ∧
        (∀ z, z + T z + T (T z) = 0) ∧
        (∀ R : HilbertModel.{u, v} U q,
          ∃ F : (V ⧸ B.ker) →ₗ[ℝ] R.carrier, ∀ x, F (B.ker.mkQ x) = R.label x)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let q : ULift.{u} ℝ → ℝ := fun x => (x.down + 1) ^ 2
  have hq : ∀ x, 0 ≤ q x := fun _ => sq_nonneg _
  have hz : Balance (id : ULift.{u} ℝ → ULift.{u} ℝ) (fun _ => (0 : ℝ)) := by
    dsimp only [Balance]
    intro x y t
    ring
  obtain ⟨B, hb, hs, hd, hn, g, T, hg, hp, rest⟩ := h id q hq hz
  have hh := hd (ULift.up (-1 : ℝ))
  change ((-1 : ℝ) + 1) ^ 2 = (0 + 1) ^ 2 + B _ _ at hh
  norm_num at hh
  have hhpos := hp (B.ker.mkQ (ULift.up (-1 : ℝ)))
  rw [hg] at hhpos
  linarith

def evidence : Registration arena.{u, v}
    (type_of% @_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_visible_quotient.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_visible_quotient.{u, v}, rejected, rejected_law⟩
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

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_visible_quotient.{u, v}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.RealThreePathRepresentationQuotient.unit
  realizationName := `Reg.D5.S3.QuadraticForms.RealThreePathRepresentationQuotient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.RealThreePathRepresentation
    definition := none
    coordinates := #[0, 4]
    readouts := #[{ path := #["body","body","body","body","body","body","domain","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.RealThreePathRepresentationQuotient

namespace Reg.D5.S3.QuadraticForms.RealThreePathRepresentation

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

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p x => -p.2 x) (fun e => nomatch e)

private def sampleQ : ULift.{u} ℂ → ℝ := fun x => ‖x.down‖ ^ 2
private def sampleU : ULift.{u} ℂ → ULift.{u} ℂ := fun x => ⟨omega * x.down⟩
private theorem sample_nonneg : ∀ x : ULift.{u} ℂ, 0 ≤ sampleQ x := fun _ => sq_nonneg _
private theorem sample_balance : Balance sampleU.{u} sampleQ := by
  let F := (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).toLinearMap
  apply (original_hilbert_characterization.{u, 0, 0} sampleU sampleQ sample_nonneg).2.1 ℂ F
  · intro x
    change ‖x.down‖ ^ 2 = ‖(0 : ℂ)‖ ^ 2 + ‖x.down‖ ^ 2
    simp
  · intro x
    rfl

abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [AddCommGroup V] [Module ℝ V]
    (U : V → V) (q : V → ℝ) (_hq : ∀ x, 0 ≤ q x),
    (Balance U q ↔ Nonempty (HilbertModel.{u, u} U (fun x => Z.readout () ⟨V, q⟩ x))) ∧
    (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (F : V →ₗ[ℝ] H),
      (∀ x, q x = q 0 + ‖F x‖ ^ 2) →
      (∀ x, F (U x) = omega • F x) → Balance U q) ∧
    (∀ (R : HilbertModel.{u, v} U q) (S : HilbertModel.{u, w} U q),
      ∃! e : R.carrier ≃ₗᵢ[ℂ] S.carrier, ∀ x, e (R.label x) = S.label x) ∧
    (Balance U q → ∀ x, q 0 ≤ q x)

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hh := (h sampleU sampleQ sample_nonneg).1.mp sample_balance
  obtain ⟨M⟩ := hh
  have hn := M.normSq (ULift.up (1 : ℂ))
  change -‖(1 : ℂ)‖ ^ 2 = -‖(0 : ℂ)‖ ^ 2 + ‖M.label _‖ ^ 2 at hn
  norm_num at hn
  nlinarith [sq_nonneg ‖M.label (ULift.up (1 : ℂ))‖]

def evidence : Registration arena.{u, v, w}
    (type_of% @_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_hilbert_characterization.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_hilbert_characterization.{u, v, w}, rejected, rejected_law⟩
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

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.QuadraticForms.RealThreePathRepresentation.original_hilbert_characterization.{u, v, w}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.RealThreePathRepresentation.unit
  realizationName := `Reg.D5.S3.QuadraticForms.RealThreePathRepresentation.evidence
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
    owner := `D5.S3.QuadraticForms.RealThreePathRepresentation
    definition := none
    coordinates := #[0, 4]
    readouts := #[{ path := #["body","body","body","body","body","body","fn","arg","arg","arg","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.RealThreePathRepresentation
