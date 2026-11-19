import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw
import Reg.Support.DependentFamily

/-! # Ambient factorial in the alternating completion law -/

open Relation
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw

noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n.factorial) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type u} [Finite V] (E : V → V → Prop) (k : V → Bool)
    (n : ℕ) (_hn : 0 < n)
    (_hout : Relator.RightUnique E) (_hin : Relator.LeftUnique E)
    (_ha : ∀ x, ¬ TransGen E x x) (_hk : ∀ x y, E x y → k x ≠ k y)
    (_hr : Nat.card (Side k false) = n) (_hb : Nat.card (Side k true) = n),
    let S : Set (AlternatingFullCycle k) := {σ | ∀ x y, E x y → σ.1 x = y}
    let D := F.readout () () n * (n - 1).factorial
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : AlternatingCompletion E k ≃ Compatible (fun A => k (h A)) (fun A => !(k (t A))))
      (μ : PMF (AlternatingFullCycle k)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, σ.1 (t A) = h ((Φ σ).1 A)) ∧
      (∀ σ, μ σ = (D : ℝ≥0∞)⁻¹) ∧
      μ.toOuterMeasure S = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞) / D ∧
      (0 < μ.toOuterMeasure S ↔ Nonempty (AlternatingCompletion E k)) ∧
      ∀ hs : ∃ σ ∈ S, σ ∈ μ.support,
        ∃ ν : PMF (AlternatingCompletion E k),
          (∀ τ, ν τ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹) ∧
          μ.filter S hs = ν.map (includeCompletion E k) ∧
          (∀ ρ, ν.map Φ.toFun ρ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹)

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro hbad
  let V := ULift.{u} Bool
  let k (x : V) := x.down
  let E (_ _ : V) : Prop := False
  have hside (b : Bool) : Nat.card (Side k b) = 1 := by
    let e : Side k b ≃ Unit := {
      toFun := fun _ => ()
      invFun := fun _ => ⟨ULift.up b, rfl⟩
      left_inv := fun x => Subtype.ext (ULift.ext x.2.symm)
      right_inv := fun _ => Subsingleton.elim _ _ }
    exact (Nat.card_congr e).trans (by simp [Nat.card_eq_fintype_card])
  have hacyclic (x : V) : ¬ TransGen E x x := by
    intro hx
    cases hx with
    | single h => exact h.elim
    | tail _ h => exact h.elim
  obtain ⟨_, _, _, μ, _, _, _, huniform, _⟩ :=
    hbad E k 1 (by decide) (by intro a b c h _; exact h.elim)
      (by intro a b c h _; exact h.elim) hacyclic
      (fun _ _ h => h.elim) (hside false) (hside true)
  obtain ⟨σ, _⟩ := μ.support_nonempty
  apply μ.apply_ne_top σ
  simpa [rejected, realize] using huniform σ

def evidence : Registration arena.{u} (type_of% (@alternating_completion_law.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@alternating_completion_law.{u}, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@alternating_completion_law.{u}) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw.alternating_completion_law
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n.factorial) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw
