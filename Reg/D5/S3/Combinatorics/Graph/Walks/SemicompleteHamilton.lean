import D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open _root_.D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
namespace Reg.D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
universe u
abbrev signature : Signature where
  Params := Type u
  State V := List V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ w => w.Nodup) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V] (S : Finset V) (D : V → V → Prop)
    (hD : ∀ {s t}, D s t → s ∈ S ∧ t ∈ S) (hsize : 2 ≤ S.card)
    (hsemi : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → D s t ∨ D t s)
    (hstrong : ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen D s t)
    (a : V) (ha : a ∈ S),
    ∃ l : List V, R.readout () V (a :: l) ∧ (a :: l).toFinset = S ∧
      2 ≤ (a :: l).length ∧ List.IsChain D ((a :: l) ++ [a])

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  have hn : 2 ≤ (univ : Finset (ULift.{u} Bool)).card := by simp
  obtain ⟨l,hl,_⟩ := h (univ : Finset (ULift.{u} Bool)) (fun _ _ => True)
    (by simp) hn (by simp) (by intro s hs t ht; exact .single trivial)
    ⟨false⟩ (by simp)
  exact hl
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, [], [⟨()⟩,⟨()⟩], ?_⟩
  simp [actual,realize]
def source_registration : Registration arena.{u}
    (type_of% (@finite_semicomplete_hamilton.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_semicomplete_hamilton,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def hamilton_audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_semicomplete_hamilton.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton.finite_semicomplete_hamilton.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ w => w.Nodup) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
