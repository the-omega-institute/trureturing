import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts
import Reg.Support.DependentFamily

/-! # Vertex-count readout in the edge cardinality identity -/

open Relation
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts

noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := Type u
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ V => Nat.card V) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ V => Nat.card V + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law F := ∀ {V : Type u} [Finite V] (E : V → V → Prop)
    (_hout : Relator.RightUnique E) (_hin : Relator.LeftUnique E)
    (_hacyclic : ∀ x, ¬ TransGen E x x)
    (_hV : 2 ≤ Nat.card V) (_hc : 2 ≤ Nat.card (Component E)),
    Nat.card {xy : V × V // E xy.1 xy.2} = F.readout () () V - Nat.card (Component E) ∧
    ∀ (μ : PMF (FullCycle V)),
      (∀ σ, μ σ = (Nat.card (FullCycle V) : ℝ≥0∞)⁻¹) →
      μ.toOuterMeasure {σ | ∀ x y, E x y → σ.1 x = y} =
        ((Nat.card (Component E) - 1).factorial : ℝ≥0∞) /
          ((Nat.card V - 1).factorial : ℝ≥0∞) ∧
      0 < μ.toOuterMeasure {σ | ∀ x y, E x y → σ.1 x = y}

private def emptyRel {V : Type u} (_ _ : V) : Prop := False

private def emptyRel_component (V : Type u) : Component (@emptyRel V) ≃ V where
  toFun := Quotient.lift id (fun _ _ h => by
    change EqvGen emptyRel _ _ at h
    induction h with
    | rel _ _ hr => exact hr.elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := Quotient.mk _
  left_inv := fun x => Quotient.inductionOn x fun _ => rfl
  right_inv := fun _ => rfl

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 2)
  have hcard : Nat.card V = 2 := by simp [V, Nat.card_eq_fintype_card]
  have hc : Nat.card (Component (@emptyRel V)) = 2 :=
    (Nat.card_congr (emptyRel_component V)).trans hcard
  have hpath (x y : V) : ¬ TransGen emptyRel x y := by
    intro hp
    cases hp with
    | single he => exact he.elim
    | tail _ he => exact he.elim
  have hout : Relator.RightUnique (@emptyRel V) := by
    intro _ _ _ he _
    exact he.elim
  have hin : Relator.LeftUnique (@emptyRel V) := by
    intro _ _ _ he _
    exact he.elim
  have hbad := (h (@emptyRel V) hout hin (fun x => hpath x x) (by omega) (by omega)).1
  change Nat.card {xy : V × V // False} = Nat.card V + 1 - Nat.card (Component (@emptyRel V))
    at hbad
  have hempty : Nat.card {xy : V × V // False} = 0 := by simp
  rw [hempty, hcard, hc] at hbad
  omega

def evidence : Registration arena.{u} (type_of% (@edge_and_completion_mass.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@edge_and_completion_mass.{u}, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), ULift.{u} (Fin 2), ULift.{u} (Fin 3), ?_⟩
    change Nat.card (ULift.{u} (Fin 2)) ≠ Nat.card (ULift.{u} (Fin 3))
    simp [Nat.card_eq_fintype_card]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@edge_and_completion_mass.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts.edge_and_completion_mass
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ V => Nat.card V) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts
