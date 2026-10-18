import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

/-! The full arbitrary-vertex union source and all terminal occurrences vary. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit

universe u
noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

structure Parameters where
  Vertices : Type u
  leftGraph : SimpleGraph Vertices
  rightGraph : SimpleGraph Vertices
  leftVertices : Set Vertices
  rightVertices : Set Vertices
  gate : Vertices

private theorem singleton_union :
    OneVertexUnion (⊥ : SimpleGraph PUnit.{u+1}) ⊥ Set.univ Set.univ PUnit.unit where
  left_support := by simp
  right_support := by simp
  intersection := fun {_} _ _ => Subsingleton.elim _ _

private theorem single_sensitivity {S : Signature} (L : Realization S → Prop)
    (actual bad : Realization S) [Subsingleton S.Role] [IsEmpty S.Anchor]
    (hbad : ¬ L bad) : Sensitivity ⟨S,L⟩ actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact isEmptyElim e
  · intro e
    exact isEmptyElim e

namespace Reachability

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Vertices × p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p st => (p.leftGraph ⊔ p.rightGraph).Reachable st.1 st.2)
  (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {H K : SimpleGraph V} {A B : Set V} {g : V}
    (_h : OneVertexUnion H K A B g) {a b c : V}
    (_ha : a ∈ A) (_hb : b ∈ A) (_hc : c ∈ B),
    (R.readout () ⟨V,H,K,A,B,g⟩ (a,b) ↔ H.Reachable a b) ∧
    (R.readout () ⟨V,H,K,A,B,g⟩ (a,c) ↔ H.Reachable a g ∧ K.Reachable g c) ∧
    (R.readout () ⟨V,H,K,A,B,g⟩ (b,c) ↔ H.Reachable b g ∧ K.Reachable g c)

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := @h PUnit.{u+1} ⊥ ⊥ Set.univ Set.univ PUnit.unit
    singleton_union PUnit.unit PUnit.unit PUnit.unit (by trivial) (by trivial) (by trivial)
  exact hh.1.mpr Reachable.rfl

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  refine ⟨⟨ULift Bool,⊥,⊥,Set.univ,Set.univ,a⟩,(a,a),(a,b),?_⟩
  simp [actual,realize,a,b]

def registration : Registration arena.{u} (type_of% @simultaneous_reachability.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simultaneous_reachability,bad,rejected⟩
  sensitivity := single_sensitivity _ actual bad rejected
  dependence := dependence

def register_simultaneous_reachability : Contract.Registration (@simultaneous_reachability.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Reachability.register_simultaneous_reachability
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Reachability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p st => (p.leftGraph ⊔ p.rightGraph).Reachable st.1 st.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reachability

namespace Partition

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Vertices × p.Vertices × p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p st => graphMode (p.leftGraph ⊔ p.rightGraph) st.1 st.2.1 st.2.2)
  (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => .ac) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {H K : SimpleGraph V} {A B : Set V} {g : V}
    (_h : OneVertexUnion H K A B g) {a b c : V}
    (_ha : a ∈ A) (_hb : b ∈ A) (_hc : c ∈ B),
    R.readout () ⟨V,H,K,A,B,g⟩ (a,b,c) =
      if K.Reachable g c then graphMode H a b g else
        match graphMode H a b g with
        | .all | .ab => .ab
        | _ => .separate

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := @h PUnit.{u+1} ⊥ ⊥ Set.univ Set.univ PUnit.unit
    singleton_union PUnit.unit PUnit.unit PUnit.unit (by trivial) (by trivial) (by trivial)
  simpa [bad,realize,graphMode] using hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  refine ⟨⟨ULift Bool,⊥,⊥,Set.univ,Set.univ,a⟩,(a,a,a),(a,b,a),?_⟩
  simp [actual,realize,graphMode,a,b]

def registration : Registration arena.{u} (type_of% @graphMode_pendant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graphMode_pendant,bad,rejected⟩
  sensitivity := single_sensitivity _ actual bad rejected
  dependence := dependence

def register_graphMode_pendant : Contract.Registration (@graphMode_pendant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Partition.register_graphMode_pendant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Partition.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p st => graphMode (p.leftGraph ⊔ p.rightGraph) st.1 st.2.1 st.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Partition

namespace ActualEdges

structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  finiteEdges : Fintype graph.edgeSet
  decidableEdges : DecidableEq graph.edgeSet
  a : Vertices
  b : Vertices
  c : Vertices
  rate : graph.edgeSet → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact law (actualEdgeEnds p.graph) p.a p.b p.c p.rate)
  (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (G : SimpleGraph V)
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype G.edgeSet] [dE : DecidableEq G.edgeSet]
    (a b c : V) (θ : G.edgeSet → ℝ),
    R.readout () ⟨V,G,hV,dV,hE,dE,a,b,c,θ⟩ = bondLaw G a b c θ

private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := congrFun (h G PUnit.unit PUnit.unit PUnit.unit (fun _ => 0)) .all
  change 0 = bondLaw G PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all at hh
  rw [(_root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
    PUnit.unit (fun _ : G.edgeSet => 0)).1] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  refine ⟨⟨PUnit,G,inferInstance,inferInstance,inferInstance,inferInstance,
    PUnit.unit,PUnit.unit,PUnit.unit,fun _ => 0⟩,.all,.separate,?_⟩
  change law (actualEdgeEnds G) PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all ≠
    law (actualEdgeEnds G) PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .separate
  rw [actual_edge_law]
  obtain ⟨hall,hsep⟩ :=
    _root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
      PUnit.unit (fun _ : G.edgeSet => 0)
  rw [hall,hsep]
  norm_num

def registration : Registration arena.{u} (type_of% @actual_edge_law.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_edge_law,bad,rejected⟩
  sensitivity := single_sensitivity _ actual bad rejected
  dependence := dependence

def register_actual_edge_law : Contract.Registration (@actual_edge_law.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualEdges.register_actual_edge_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualEdges.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteEdges
      letI := p.decidableEdges
      exact law (actualEdgeEnds p.graph) p.a p.b p.c p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end ActualEdges

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Reachability.register_simultaneous_reachability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reachability.register_simultaneous_reachability

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.Partition.register_graphMode_pendant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Partition.register_graphMode_pendant

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualEdges.register_actual_edge_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ActualEdges.register_actual_edge_law

namespace ActualGraph
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.graph.edgeSet → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := SimpleGraph p.Vertices
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize _
  (fun _ p ω => openGraph (actualEdgeEnds p.graph) ω) (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => ⊥) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (G : SimpleGraph V) (ω : G.edgeSet → Bool),
    R.readout () ⟨V,G⟩ ω = bondGraph G ω
private theorem all_open {V : Type*} (G : SimpleGraph V) :
    bondGraph G (fun _ => true) = G := by
  ext x y
  simp [bondGraph]
private theorem all_closed {V : Type*} (G : SimpleGraph V) :
    bondGraph G (fun _ => false) = ⊥ := by
  ext x y
  simp [bondGraph]
private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  have hh := h (⊤ : SimpleGraph (ULift.{u} Bool)) (fun _ => true)
  rw [all_open] at hh
  have he := congrArg (fun G : SimpleGraph (ULift.{u} Bool) => G.Adj a b) hh
  simpa [bad,realize,a,b] using he
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  refine ⟨⟨ULift Bool,⊤⟩,(fun _ => true),(fun _ => false),?_⟩
  change openGraph (actualEdgeEnds (⊤ : SimpleGraph (ULift.{u} Bool))) (fun _ => true) ≠
    openGraph (actualEdgeEnds (⊤ : SimpleGraph (ULift.{u} Bool))) (fun _ => false)
  rw [actual_edge_graph,actual_edge_graph,all_open,all_closed]
  intro h
  have he := congrArg (fun G : SimpleGraph (ULift.{u} Bool) => G.Adj a b) h
  simpa [a,b] using he
def registration : Registration arena.{u} (type_of% @actual_edge_graph.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_edge_graph,bad,rejected⟩
  sensitivity := single_sensitivity _ actual bad rejected
  dependence := dependence
def register_actual_edge_graph : Contract.Registration (@actual_edge_graph.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualGraph.register_actual_edge_graph
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualGraph.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p ω => openGraph (actualEdgeEnds p.graph) ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.ActualGraph.register_actual_edge_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_actual_edge_graph
end ActualGraph

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
