import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

/-! Typed registrations retain the complete actual five-mode edge sources. -/

set_option backward.isDefEq.respectTransparency.types false
namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph
universe u
noncomputable section

namespace Split
structure Parameters where
  Vertices : Type u
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  left : SimpleGraph Vertices
  right : SimpleGraph Vertices
  finiteLeft : Fintype left.edgeSet
  decidableLeft : DecidableEq left.edgeSet
  finiteRight : Fintype right.edgeSet
  decidableRight : DecidableEq right.edgeSet
  finiteUnion : Fintype (left ⊔ right).edgeSet
  decidableUnion : DecidableEq (left ⊔ right).edgeSet
  a : Vertices
  b : Vertices
  c : Vertices
  rate : (left ⊔ right).edgeSet → ℝ
abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize _ (fun _ p => by
  letI := p.finiteUnion
  exact bondLaw (p.left ⊔ p.right) p.a p.b p.c p.rate) (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [hV : Fintype V] [dV : DecidableEq V]
    (H K : SimpleGraph V) [hH : Fintype H.edgeSet] [dH : DecidableEq H.edgeSet]
    [hK : Fintype K.edgeSet] [dK : DecidableEq K.edgeSet]
    [hU : Fintype (H ⊔ K).edgeSet] [dU : DecidableEq (H ⊔ K).edgeSet]
    (_h : Disjoint H.edgeSet K.edgeSet) (a b c : V) (θ : (H ⊔ K).edgeSet → ℝ),
    R.readout () ⟨V,hV,dV,H,K,hH,dH,hK,dK,hU,dU,a,b,c,θ⟩ =
      law (Sum.elim (actualEdgeEnds H) (actualEdgeEnds K)) a b c
        (Sum.elim
          (fun e : H.edgeSet => θ ⟨e.val,edgeSet_mono le_sup_left e.property⟩)
          (fun e : K.edgeSet => θ ⟨e.val,edgeSet_mono le_sup_right e.property⟩))
private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI : Fintype (G ⊔ G).edgeSet := Fintype.ofFinite _
  have hd : Disjoint G.edgeSet G.edgeSet := by simp [G]
  have hh := congrFun (h G G hd PUnit.unit PUnit.unit PUnit.unit (fun _ => 0)) .all
  have ho := congrFun (edge_split_law G G hd PUnit.unit PUnit.unit PUnit.unit
    (fun _ => 0)) .all
  change 0 = _ at hh
  rw [← ho] at hh
  rw [(_root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
    PUnit.unit (fun _ : (G ⊔ G).edgeSet => 0)).1] at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI : Fintype (G ⊔ G).edgeSet := Fintype.ofFinite _
  refine ⟨⟨PUnit,inferInstance,inferInstance,G,G,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,inferInstance,
    PUnit.unit,PUnit.unit,PUnit.unit,fun _ => 0⟩,.all,.separate,?_⟩
  change bondLaw (G ⊔ G) PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all ≠
    bondLaw (G ⊔ G) PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .separate
  obtain ⟨hall,hsep⟩ :=
    _root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
      PUnit.unit (fun _ : (G ⊔ G).edgeSet => 0)
  rw [hall,hsep]
  norm_num
def registration : Registration arena.{u} (type_of% @edge_split_law.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_split_law,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_edge_split_law : Contract.Registration (@edge_split_law.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Split.register_edge_split_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Split.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.finiteUnion
    exact bondLaw (p.left ⊔ p.right) p.a p.b p.c p.rate) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Split.register_edge_split_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_edge_split_law
end Split

namespace Induced
structure Parameters where
  Vertices : Type u
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  graph : SimpleGraph Vertices
  side : Set Vertices
  finiteSide : Fintype side
  decidableSide : DecidableEq side
  finiteInducedEdges : Fintype (graph.induce side).edgeSet
  decidableInducedEdges : DecidableEq (graph.induce side).edgeSet
  finiteSideEdges : Fintype (sideGraph graph side).edgeSet
  decidableSideEdges : DecidableEq (sideGraph graph side).edgeSet
  a : side
  b : side
  c : side
  rate : (sideGraph graph side).edgeSet → ℝ
abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize _ (fun _ p => by
  letI := p.finiteSideEdges
  exact bondLaw (sideGraph p.graph p.side) p.a.val p.b.val p.c.val p.rate)
  (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [hV : Fintype V] [dV : DecidableEq V]
    (G : SimpleGraph V) (A : Set V) [hA : Fintype A] [dA : DecidableEq A]
    [hI : Fintype (G.induce A).edgeSet] [dI : DecidableEq (G.induce A).edgeSet]
    [hS : Fintype (sideGraph G A).edgeSet] [dS : DecidableEq (sideGraph G A).edgeSet]
    (a b c : A) (θ : (sideGraph G A).edgeSet → ℝ),
    R.readout () ⟨V,hV,dV,G,A,hA,dA,hI,dI,hS,dS,a,b,c,θ⟩ =
      bondLaw (G.induce A) a b c (fun i => θ (inducedEdgeEquiv G A i))
private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  let A : Set PUnit.{u+1} := Set.univ
  let a : A := ⟨PUnit.unit,by trivial⟩
  have hh := congrFun (h G A a a a (fun _ => 0)) .all
  change 0 = bondLaw (G.induce A) a a a (fun _ => 0) .all at hh
  rw [(_root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
    a (fun _ : (G.induce A).edgeSet => 0)).1] at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph PUnit.{u+1} := ⊥
  let A : Set PUnit.{u+1} := Set.univ
  let a : A := ⟨PUnit.unit,by trivial⟩
  refine ⟨⟨PUnit,inferInstance,inferInstance,G,A,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,inferInstance,a,a,a,fun _ => 0⟩,
    .all,.separate,?_⟩
  change bondLaw (sideGraph G A) a.val a.val a.val (fun _ => 0) .all ≠
    bondLaw (sideGraph G A) a.val a.val a.val (fun _ => 0) .separate
  obtain ⟨hall,hsep⟩ :=
    _root_.Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.same_terminal_law
      a.val (fun _ : (sideGraph G A).edgeSet => 0)
  rw [hall,hsep]
  norm_num
def registration : Registration arena.{u} (type_of% @induced_source_law.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨induced_source_law,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_induced_source_law : Contract.Registration (@induced_source_law.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Induced.register_induced_source_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Induced.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.finiteSideEdges
    exact bondLaw (sideGraph p.graph p.side) p.a.val p.b.val p.c.val p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.Induced.register_induced_source_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_induced_source_law
end Induced

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit
