import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities

open Finset LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
universe u

noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, Fintype V
  State p := p.1 → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p d => letI := p.2; (∑ v, d v) = 0) (fun e => nomatch e)

def unrestricted : Realization signature.{u} :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V]
      (G : SimpleGraph V) (_ : G.Connected) (d : V → ZMod 2),
    (∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, (Nat.card (H.neighborSet v) : ZMod 2) = d v) ↔
      R.readout () ⟨V, inferInstance⟩ d

private theorem unrestricted_fails : ¬ arena.{u}.Law unrestricted := by
  classical
  intro law
  let V := PUnit.{u+1}
  let G : SimpleGraph V := ⊤
  let d : V → ZMod 2 := fun _ => 1
  have h := (law G SimpleGraph.connected_top d).mpr True.intro
  have impossible := (exact_parity_subgraph G SimpleGraph.connected_top d).mp h
  simp [V, d] at impossible

def family : Registration arena.{u} (type_of% (@exact_parity_subgraph.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_parity_subgraph, unrestricted, unrestricted_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨unrestricted, ?_, rfl, unrestricted_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let V := PUnit.{u+1}
    refine ⟨⟨V, inferInstance⟩, fun _ => 0, fun _ => 1, ?_⟩
    change (((∑ _ : V, (0 : ZMod 2)) = 0) : Prop) ≠ ((∑ _ : V, (1 : ZMod 2)) = 0)
    simp [V]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_parity_subgraph.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities.paritySum
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => letI := p.2; (∑ v, d v) = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end

end Reg.D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities
