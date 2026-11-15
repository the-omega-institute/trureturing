import D5.S1.Words.RankedCostDescent
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.RankedCostDescent

universe u v

structure Parameters where
  States : Type u
  Letters : Type v
  step : States → Letters → States
  goal : States → Prop
  rank : States → Nat
  potential : States → Nat
  charge : States → Letters → Nat

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.States
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def goalConclusion (p : Parameters.{u,v}) (s : p.States) : Prop :=
  ∃ w : List p.Letters, p.goal (w.foldl p.step s) ∧
    _root_.D5.S1.Words.RankedCostDescent.wordCost p.step p.charge s w +
      p.potential (w.foldl p.step s) ≤ p.potential s

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p s => goalConclusion p s) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ (X : Type u) (A : Type v) (step : X → A → X)
    (Goal : X → Prop) (rank potential : X → Nat)
    (charge : X → A → Nat) (start : X),
    (∀ s, ¬ Goal s → ∃ a : List A,
      rank (a.foldl step s) < rank s ∧
      _root_.D5.S1.Words.RankedCostDescent.wordCost step charge s a +
        potential (a.foldl step s) ≤ potential s) →
      R.readout () ⟨X, A, step, Goal, rank, potential, charge⟩ start

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (ULift.{u} Unit) (ULift.{v} Unit) (fun s _ => s)
    (fun _ => True) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) ⟨()⟩
    (fun _ hs => (hs trivial).elim)

private abbrev separatingParameters : Parameters.{u,v} where
  States := ULift.{u} Bool
  Letters := ULift.{v} Unit
  step s _ := s
  goal s := s.down = false
  rank _ := 0
  potential _ := 0
  charge _ _ := 0

private theorem false_readout :
    goalConclusion separatingParameters.{u,v} ⟨false⟩ := by
  exact ⟨[], rfl, Nat.zero_le _⟩

private theorem true_readout :
    ¬ goalConclusion separatingParameters.{u,v} ⟨true⟩ := by
  rintro ⟨w, hgoal, _⟩
  have unchanged : w.foldl separatingParameters.step ⟨true⟩ = ⟨true⟩ := by
    induction w with
    | nil => rfl
    | cons a w ih => exact ih
  change (w.foldl separatingParameters.step ⟨true⟩).down = false at hgoal
  rw [unchanged] at hgoal
  cases hgoal

def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S1.Words.RankedCostDescent.exists_goal_word_cost_add_potential_le.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RankedCostDescent.exists_goal_word_cost_add_potential_le,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨separatingParameters, ⟨false⟩, ⟨true⟩, ?_⟩
    change goalConclusion separatingParameters ⟨false⟩ ≠
      goalConclusion separatingParameters ⟨true⟩
    intro heq
    exact true_readout (Eq.mp heq false_readout)

noncomputable def audit : Contract.Registration
    (@_root_.D5.S1.Words.RankedCostDescent.exists_goal_word_cost_add_potential_le.{u,v})
    (type_of% actual.{u,v}) Unit Unit := {
  unitName := `D5.S1.Words.RankedCostDescent.exists_goal_word_cost_add_potential_le.__information_unit,
  realizationName := `Reg.D5.S1.Words.RankedCostDescent.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.RankedCostDescent, definition := none,
    coordinates := #[0, 1, 2, 3, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 7, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.RankedCostDescent
