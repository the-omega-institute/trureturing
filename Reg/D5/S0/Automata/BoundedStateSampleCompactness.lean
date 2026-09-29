import D5.S0.Automata.BoundedStateSampleCompactness
import Reg.Support.DependentFamily

namespace Reg.D5.S0.Automata.BoundedStateSampleCompactness

open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.BoundedStateSampleCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The same budget must be used for global and finite-sample realizability. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {Alphabet : Type u} {Output : Type v} [Finite Alphabet] [Finite Output]
    (D : Set (List Alphabet)) (target : D → Output) (s : ℕ),
    (∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
      Fintype.card State ≤ s ∧ CorrectOnFamily machine Subtype.val target) ↔
    ∀ E : Finset D,
      ∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
        Fintype.card State ≤ R.readout () () s ∧
          FitsSubsample machine Subtype.val target (fun i : E => i.val)

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let D : Set (List (ULift.{u} Unit)) := ∅
  let target : D → ULift.{v} Unit := fun _ => ⟨()⟩
  have hiff := h D target 1
  have global : ∃ (State : Type w) (_ : Fintype State)
      (machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) State),
      Fintype.card State ≤ 1 ∧ CorrectOnFamily machine Subtype.val target := by
    let machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) :=
      { start := ⟨()⟩, step := fun q _ => q, accept := ∅, output := fun _ => ⟨()⟩ }
    refine ⟨ULift.{w} Unit, inferInstance, machine, by simp, ?_⟩
    intro i
    exact False.elim i.property
  obtain ⟨State, inst, machine, bound, _⟩ := hiff.mp global ∅
  have positive : 0 < Fintype.card State := Fintype.card_pos_iff.mpr ⟨machine.start⟩
  change Fintype.card State ≤ 0 at bound
  omega

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_state_sample_compactness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

register_information_theorem bounded_state_sample_compactness in arena
  readout via (realize signature (fun _ _ s => s) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S0.Automata.BoundedStateSampleCompactness
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "fn", "arg", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "bounded-state compactness registration is not declaredValidated"

#print axioms registration

end Reg.D5.S0.Automata.BoundedStateSampleCompactness
