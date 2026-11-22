import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
import Reg.Support.DependentFamily

/-! Position observations in the adjacency laws of a graph join. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph

open _root_.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev Parameters := Σ A : Type, Σ B : Type, Σ _G : SimpleGraph A,
  Σ _H : SimpleGraph B, Σ _a : A, B

abbrev signature (X : Parameters → Type) : Signature where
  Params := Parameters
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := X
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem sensitivity {X : Parameters → Type}
    (law : Realization (signature X) → Prop) (actual rejected : Realization (signature X))
    (invalid : ¬ law rejected) : Sensitivity ⟨signature X, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, invalid⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private abbrev leftParameters : Parameters :=
  ⟨Fin 2, Unit, ⊤, ⊥, 0, ()⟩

private abbrev rightParameters : Parameters :=
  ⟨Unit, Fin 2, ⊥, ⊤, (), 0⟩

namespace Left

abbrev stage := signature fun p => p.1

def actual : Realization stage :=
  realize stage (fun _ _ x => x) (fun e => nomatch e)

private def rejected : Realization stage :=
  realize stage (fun _ p _ => p.2.2.2.2.1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := stage
  Law R := ∀ {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
      (x y : A), (joinAt G H a b).Adj (.inl x) (.inl y) ↔ G.Adj (R.readout () ⟨A, B, G, H, a, b⟩ x) y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have wrongly := h (A := Fin 2) (B := Unit) ⊤ ⊥ 0 () 1 0
  have observed := (joinAt_inl (A := Fin 2) (B := Unit) ⊤ ⊥ 0 () 1 0).mpr
    (by change (1 : Fin 2) ≠ 0; decide)
  have contradiction := wrongly.mp observed
  change (0 : Fin 2) ≠ 0 at contradiction
  exact contradiction rfl

def family : Registration arena (type_of% @joinAt_inl) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joinAt_inl, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨leftParameters, 0, 1, by change (0 : Fin 2) ≠ 1; decide⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@joinAt_inl) (Realization stage) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.joinAt_inl.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph.Left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stage (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Left

namespace Right

abbrev stage := signature fun p => p.2.1

def actual : Realization stage :=
  realize stage (fun _ _ x => x) (fun e => nomatch e)

private def rejected : Realization stage :=
  realize stage (fun _ p _ => p.2.2.2.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := stage
  Law R := ∀ {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
      (x y : B), (joinAt G H a b).Adj (.inr x) (.inr y) ↔ H.Adj (R.readout () ⟨A, B, G, H, a, b⟩ x) y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have wrongly := h (A := Unit) (B := Fin 2) ⊥ ⊤ () 0 1 0
  have observed := (joinAt_inr (A := Unit) (B := Fin 2) ⊥ ⊤ () 0 1 0).mpr
    (by change (1 : Fin 2) ≠ 0; decide)
  have contradiction := wrongly.mp observed
  change (0 : Fin 2) ≠ 0 at contradiction
  exact contradiction rfl

def family : Registration arena (type_of% @joinAt_inr) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joinAt_inr, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨rightParameters, 0, 1, by change (0 : Fin 2) ≠ 1; decide⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@joinAt_inr) (Realization stage) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.joinAt_inr.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph.Right.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stage (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Right

namespace Cross

abbrev stage := signature fun p => p.1

def actual : Realization stage :=
  realize stage (fun _ _ x => x) (fun e => nomatch e)

private def rejected : Realization stage :=
  realize stage (fun _ p _ => p.2.2.2.2.1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := stage
  Law R := ∀ {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
      (x : A) (y : B), (joinAt G H a b).Adj (.inl x) (.inr y) ↔ R.readout () ⟨A, B, G, H, a, b⟩ x = a ∧ y = b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have wrongly := h (A := Fin 2) (B := Unit) ⊤ ⊥ 0 () 1 ()
  have wronglyAdjacent := wrongly.mpr ⟨rfl, rfl⟩
  have badEquality := ((joinAt_cross (A := Fin 2) (B := Unit) ⊤ ⊥ 0 () 1 ()).mp wronglyAdjacent).1
  exact (by decide : (1 : Fin 2) ≠ 0) badEquality

def family : Registration arena (type_of% @joinAt_cross) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joinAt_cross, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨leftParameters, 0, 1, by change (0 : Fin 2) ≠ 1; decide⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@joinAt_cross) (Realization stage) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.joinAt_cross.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph.Cross.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stage (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Cross

end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Graph
