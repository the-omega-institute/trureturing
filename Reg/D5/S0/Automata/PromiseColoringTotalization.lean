import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Automata.PromiseColoringTotalization
import Reg.Support.DependentFamily

namespace Reg.D5.S0.Automata.PromiseColoringTotalization

open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.PromiseColoringTotalization
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

/-- The complete source family, with an intervention only on the color budget. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {Alphabet : Type u} {Output : Type v}
    (D : Set (List Alphabet)) (f : D → Output) (nonempty : D.Nonempty)
    (s : ℕ) (_positive : 0 < s),
    (∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
      Fintype.card State ≤ s ∧ CorrectOnFamily machine Subtype.val f) ↔
    Nonempty (Coloring D f (Fin (R.readout () () s)))

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Zero available colors fail on a nonempty singleton promise at budget one. -/
theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let D : Set (List (ULift.{u} Unit)) := {[]}
  let f : D → ULift.{v} Unit := fun _ => ⟨()⟩
  have nonempty : D.Nonempty := ⟨[], by simp [D]⟩
  have global : ∃ (State : Type w) (_ : Fintype State)
      (machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) State),
      Fintype.card State ≤ 1 ∧ CorrectOnFamily machine Subtype.val f := by
    let machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) :=
      { start := ⟨()⟩, step := fun q _ => q, accept := ∅, output := fun _ => ⟨()⟩ }
    refine ⟨ULift.{w} Unit, inferInstance, machine, by simp, ?_⟩
    intro word
    rfl
  obtain ⟨c⟩ := (h D f nonempty 1 (by decide)).mp global
  exact Fin.elim0 (c.color ⟨[], ⟨[], by simp [D]⟩⟩)

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨promise_coloring_iff_total_dfao, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact False.elim (different (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S0.Automata.PromiseColoringTotalization.promise_coloring_iff_total_dfao.{u,v,w})
      (type_of% (realize.{0,0,0,0,0} signature (fun _ _ s => s) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S0.Automata.PromiseColoringTotalization.promise_coloring_iff_total_dfao.__information_unit,
  realizationName := `Reg.D5.S0.Automata.PromiseColoringTotalization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w}⟩,
  objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w} ⟨registration.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ s => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Automata.PromiseColoringTotalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

end Reg.D5.S0.Automata.PromiseColoringTotalization
