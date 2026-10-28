import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import Reg.Support.DependentFamily

/-! The full generic cycle-deletion statement is observed through the weight
of its returned walk, with its endpoints and all scalar structures retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Maths Maths.MaxPlusPotential
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
noncomputable section
universe uK uV uE

private instance liftedIntegerOrdered : IsOrderedAddMonoid (ULift.{uK} Int) where
  add_le_add_left a b h c := by
    change a.down + c.down ≤ b.down + c.down
    change a.down ≤ b.down at h
    omega

structure PruningParams where
  Scalar : Type uK
  [scalarAdd : AddCommMonoid Scalar]
  [scalarOrder : LinearOrder Scalar]
  [scalarOrdered : IsOrderedAddMonoid Scalar]
  Vertex : Type uV
  Edge : Type uE
  graph : EdgeGraph Vertex Edge
  weight : Edge → Scalar
  start : Vertex
  finish : Vertex

attribute [instance] PruningParams.scalarAdd PruningParams.scalarOrder PruningParams.scalarOrdered

abbrev pruningSignature : Signature where
  Params := PruningParams.{uK,uV,uE}
  State q := q.graph.Walk q.start q.finish
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := q.Scalar
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev pruningActual : Realization pruningSignature.{uK,uV,uE} :=
  realize pruningSignature (fun _ q walk => walkWeight q.weight walk) (fun e => nomatch e)

abbrev pruningRejected : Realization pruningSignature.{uK,uV,uE} :=
  realize pruningSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev pruningArena : Arena where
  signature := pruningSignature.{uK,uV,uE}
  Law R := ∀ q : PruningParams.{uK,uV,uE},
    (∀ vertex (cycle : q.graph.Walk vertex vertex), walkWeight q.weight cycle ≤ 0) →
    ∀ (bound : Nat) (walk : q.graph.Walk q.start q.finish), walk.length ≤ bound →
      ∃ pruned : q.graph.Walk q.start q.finish,
        pruned.visited.Nodup ∧ walkWeight q.weight walk ≤ R.readout () q pruned

private theorem pruning_rejected : ¬ pruningArena.{uK,uV,uE}.Law pruningRejected := by
  intro law
  let q : PruningParams.{uK,uV,uE} := {
    Scalar := ULift.{uK} Int
    Vertex := ULift.{uV} (Fin 2)
    Edge := ULift.{uE} (Fin 1)
    graph := { source := fun _ => ⟨0⟩, target := fun _ => ⟨1⟩ }
    weight := fun _ => ⟨1⟩
    start := ⟨0⟩
    finish := ⟨1⟩ }
  have potential : IsPotential q.graph q.weight (fun v => ⟨(v.down.val : Int)⟩) := by
    intro e
    change (0 : Int) + 1 ≤ 1
    omega
  have cycles : ∀ vertex (cycle : q.graph.Walk vertex vertex), walkWeight q.weight cycle ≤ 0 := by
    intro vertex cycle
    have h := potential.walkWeight_add_le cycle
    change (walkWeight q.weight cycle).down + (vertex.down.val : Int) ≤ vertex.down.val at h
    change (walkWeight q.weight cycle).down ≤ 0
    omega
  let walk : q.graph.Walk q.start q.finish := .concat .nil ⟨0⟩ rfl
  obtain ⟨pruned, _, hle⟩ := law q cycles 1 walk (by decide)
  change (1 : Int) ≤ 0 at hle
  omega

def pruningEvidence : Registration pruningArena.{uK,uV,uE}
    (type_of% (@exists_nodup_visited_walkWeight_le.{uV,uE,uK})) where
  actual := pruningActual
  bridge := by
    constructor
    · intro h q cycles bound walk hlen
      exact h cycles bound walk hlen
    · intro h Scalar scalarAdd scalarOrder scalarOrdered Vertex Edge graph weight cycles bound
        start finish walk hlen
      exact h {
        Scalar := Scalar
        Vertex := Vertex
        Edge := Edge
        graph := graph
        weight := weight
        start := start
        finish := finish } cycles bound walk hlen
  variation := ⟨fun q cycles bound walk hlen =>
    exists_nodup_visited_walkWeight_le cycles bound walk hlen, pruningRejected, pruning_rejected⟩
  sensitivity := ⟨fun i => ⟨pruningRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, pruning_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    let q : PruningParams.{uK,uV,uE} := {
      Scalar := ULift.{uK} Int
      Vertex := ULift.{uV} Unit
      Edge := ULift.{uE} Unit
      graph := { source := fun _ => ⟨()⟩, target := fun _ => ⟨()⟩ }
      weight := fun _ => ⟨1⟩
      start := ⟨()⟩
      finish := ⟨()⟩ }
    refine ⟨q, .nil, .concat .nil ⟨()⟩ rfl, ?_⟩
    intro eq
    have eqDown := congrArg (fun x : ULift.{uK} Int => x.down) eq
    change (0 : Int) = 1 at eqDown
    omega

def pruningRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_nodup_visited_walkWeight_le.{0,0,0})
    (Realization pruningSignature.{0,0,0}) (Nat → Type) Unit where
  unitName := `Maths.MaxPlusPotential.exists_nodup_visited_walkWeight_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual.pruningEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pruningArena.{0,0,0}⟩
  objectArena := .source ⟨pruningArena.{0,0,0}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pruningArena.{0,0,0} ⟨pruningEvidence.{0,0,0}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pruningSignature.{0,0,0}
    (fun _ q walk => walkWeight q.weight walk) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pruningEvidence
end
end Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
