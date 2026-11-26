import D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The bounded-phase transport law observes the symbol at a specified actual path index. -/

open Quiver
open _root_.D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

universe u v w

set_option linter.checkUnivs false

abbrev PathParameters :=
  Σ V : Type u, Σ q : Quiver.{v} V, Σ α : Type w, Σ _label : @EdgeLabel V q α,
    Σ S : @StronglyConnectedComponent V q, Σ a : @Component V q S, Σ b : @Component V q S,
      @Path _ (@componentQuiver V q S) a b

abbrev signature : Signature where
  Params := PathParameters.{u, v, w}
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def readPath (_ : Unit) (p : PathParameters.{u, v, w}) (i : Nat) : Option p.2.2.1 :=
  match p with
  | ⟨V, q, _, label, S, _, _, H⟩ =>
    (@output _ (@componentQuiver V q S) _ (@componentLabel V q _ label S) _ _ H)[i]?

def actual : Realization signature.{u, v, w} :=
  realize signature readPath (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R :=
    ∀ {V : Type u} [q : Quiver.{v} V] [Finite V] {α : Type w}
      (label : EdgeLabel V α) (S : StronglyConnectedComponent V),
    BoundedPhases label S →
      ∃ p : Nat, 0 < p ∧ p ≤ Nat.card (Component S) ∧
        ∃ P : ZMod p → α, ∃ θ : Component S → ZMod p,
          (∀ {a b : Component S} (e : a ⟶ b),
            componentLabel label S e = P (θ a) ∧ θ b = θ a + 1) ∧
          ∀ {a b : Component S} (H : Path a b),
            θ b = θ a + (H.length : ZMod p) ∧
            ∀ (i : Nat), i < H.length →
              R.readout () ⟨V, q, α, label, S, a, b, H⟩ i =
                some (P (θ a + (i : ZMod p)))

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

private abbrev loopQuiver : Quiver.{v} (ULift.{u} Unit) :=
  ⟨fun _ _ => ULift.{v} Unit⟩

private def loopLabel : @EdgeLabel (ULift.{u} Unit) loopQuiver (ULift.{w} Unit) :=
  fun _ => ⟨()⟩

private def loopComponent : @StronglyConnectedComponent (ULift.{u} Unit) loopQuiver :=
  @StronglyConnectedComponent.mk _ loopQuiver ⟨()⟩

private def loopVertex : @Component _ loopQuiver loopComponent.{u, v} := ⟨⟨()⟩, rfl⟩

private def loopPath : Quiver.Path loopVertex.{u, v} loopVertex :=
  Quiver.Path.nil.cons ⟨()⟩

private theorem loop_phases : @BoundedPhases _ loopQuiver _ loopLabel.{u, v, w} loopComponent := by
  refine ⟨1, by decide, ?_, fun _ => ⟨()⟩, fun _ => 0, ?_⟩
  · exact le_of_eq ((Nat.card_eq_one_iff_unique).2 ⟨inferInstance, ⟨loopVertex⟩⟩).symm
  · intro a b e
    exact ⟨rfl, Subsingleton.elim _ _⟩

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, pathlaw⟩ :=
    @h _ loopQuiver inferInstance _ loopLabel loopComponent loop_phases
  have absurd := (pathlaw loopPath).2 0 (by simp [loopPath])
  cases absurd

def family : Registration arena.{u, v, w} (type_of% (@path_output_of_bounded_phases.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨path_output_of_bounded_phases, rejected, rejected_law⟩
  sensitivity := by
    refine ⟨?_, fun e => nomatch e⟩
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    exact fun j hj => (hj (Subsingleton.elim j i)).elim
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, loopQuiver, ULift.{w} Unit, loopLabel, loopComponent,
      loopVertex, loopVertex, loopPath⟩, 0, 1, ?_⟩
    simp [actual, realize, readPath, loopPath, output, Quiver.Path.weight_cons,
      FreeMonoid.toList_of]

open LeanInformationAudit in
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@path_output_of_bounded_phases.{u, v, w})
    (type_of% (realize signature.{u, v, w} readPath (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.CoherentReturnPathTemplates.path_output_of_bounded_phases.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.CoherentReturnPathTemplates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readPath (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
    definition := none
    coordinates := #[0, 3, 4, 5, 10, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "body", "arg", "body", "arg",
        "body", "body", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

end Reg.D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
