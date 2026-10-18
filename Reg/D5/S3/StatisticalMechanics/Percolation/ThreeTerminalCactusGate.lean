import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The gate relation varies over the full graph, cycle and source-vertex family. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit
universe u
noncomputable section

structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  base : Vertices
  cycle : graph.Walk base base
  source : Vertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p g => @decide (g ∈ p.cycle.support ∧
    (p.graph.deleteEdges p.cycle.edgeSet).Reachable p.source g)
    (Classical.propDecidable _)) (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (_hG : G.Connected) (_hcactus : IsCactus G) {o : V}
    (C : G.Walk o o) (_hC : C.IsCycle) (x : V),
    ∃! g, R.readout () ⟨V,G,o,C,x⟩ g = true

private def triangle : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Walk
    (ULift.up 0) (ULift.up 0) :=
  .cons (v := ULift.up 1) (by simp) (.cons (v := ULift.up 2) (by simp) (.cons (by simp) .nil))

private theorem triangle_cycle : triangle.{u}.IsCycle := by
  norm_num [Walk.isCycle_def, Walk.isTrail_def, triangle, Sym2.eq_iff]

private theorem triangle_cactus : IsCactus (⊤ : SimpleGraph (ULift.{u} (Fin 3))) := by
  let a : ULift.{u} (Fin 3) := ULift.up 0
  let b : ULift.{u} (Fin 3) := ULift.up 1
  let c : ULift.{u} (Fin 3) := ULift.up 2
  let E : Finset (Sym2 (ULift.{u} (Fin 3))) := {s(a,b),s(a,c),s(b,c)}
  have hfull : ∀ e : Sym2 (ULift.{u} (Fin 3)),
      e ∈ (⊤ : SimpleGraph (ULift.{u} (Fin 3))).edgeSet → e ∈ E := by
    decide
  have hcard : E.card = 3 := by decide
  have hall {o : ULift.{u} (Fin 3)} (p : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Walk o o)
      (hp : p.IsCycle) : p.edges.toFinset = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      exact hfull e (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    · have hlen := hp.three_le_length
      have hpcard : p.edges.toFinset.card = p.length := by
        rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]
      omega
  intro o o' p q hp hq hne
  exact (hne ((hall p hp).trans (hall q hq).symm)).elim

private theorem triangle_connected : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Connected := by
  constructor
  intro a b
  by_cases hab : a = b
  · subst b; exact .rfl
  · exact (show (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj a b from hab).reachable

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  obtain ⟨g, hg, _⟩ := h triangle_connected triangle_cactus triangle triangle_cycle (ULift.up 0)
  simp [bad, realize] at hg

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph (ULift.{u} (Fin 3)) := ⊤
  let a : ULift.{u} (Fin 3) := ULift.up 0
  let b : ULift.{u} (Fin 3) := ULift.up 1
  have hbot : G.deleteEdges triangle.edgeSet = ⊥ := by
    ext u v
    obtain ⟨u⟩ := u
    obtain ⟨v⟩ := v
    fin_cases u <;> fin_cases v <;>
      simp [G, deleteEdges_adj, triangle, Walk.edgeSet, Sym2.eq_iff]
  refine ⟨⟨ULift (Fin 3),G,a,triangle,a⟩,a,b,?_⟩
  simp only [actual,realize]
  rw [hbot]
  simp [triangle, a, b, reachable_bot]

def registration : Registration arena.{u} (type_of% @cycle_gate.{u}) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq] using
    @cycle_gate.{u},bad,rejected⟩
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

def register_cycle_gate : Contract.Registration (@cycle_gate.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_gate
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.registration
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
    (fun _ p g => @decide (g ∈ p.cycle.support ∧
      (p.graph.deleteEdges p.cycle.edgeSet).Reachable p.source g)
      (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev decompositionArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (_hG : G.Connected) (_hcactus : IsCactus G) {o : V}
    (C : G.Walk o o) (_hC : C.IsCycle) (x : V),
    let A := {v | (G.deleteEdges C.edgeSet).Reachable x v}
    ∃ g, R.readout () ⟨V,G,o,C,x⟩ g = true ∧
      let B := Aᶜ ∪ {g}
      G = sideGraph G A ⊔ sideGraph G B ∧
      _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.OneVertexUnion
        (sideGraph G A) (sideGraph G B) A B g ∧
      Disjoint (sideGraph G A).edgeSet (sideGraph G B).edgeSet ∧
      Disjoint (sideGraph G A).edgeSet C.edgeSet ∧
      (G.induce A).Connected ∧ (G.induce B).Connected

private theorem decomposition_rejected : ¬ decompositionArena.{u}.Law bad := by
  intro h
  obtain ⟨g, hg, _⟩ := h triangle_connected triangle_cactus triangle triangle_cycle (ULift.up 0)
  simp [bad, realize] at hg

def decompositionRegistration : Registration decompositionArena.{u}
    (type_of% @cycle_component_decomposition.{u}) where
  actual := actual
  bridge := by simp only [decompositionArena, actual, realize, decide_eq_true_eq,
    and_assoc, Set.mem_setOf_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq,and_assoc,Set.mem_setOf_eq] using
    @cycle_component_decomposition.{u},bad,decomposition_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,decomposition_rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_cycle_component_decomposition : Contract.Registration (@cycle_component_decomposition.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_component_decomposition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.decompositionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨decompositionArena⟩
  objectArena := .source ⟨decompositionArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source decompositionArena ⟨decompositionRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p g => @decide (g ∈ p.cycle.support ∧
      (p.graph.deleteEdges p.cycle.edgeSet).Reachable p.source g)
      (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_component_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_component_decomposition

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_gate

abbrev edgeSignature : Signature where
  Params := Parameters.{u}
  State p := Sym2 p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def edgeActual : Realization edgeSignature.{u} := realize _
  (fun _ p e => @decide (e ∈ p.graph.edgeSet) (Classical.propDecidable _))
  (fun e => nomatch e)

def edgeBad : Realization edgeSignature.{u} :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

abbrev spanningArena : Arena where
  signature := edgeSignature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (_hcactus : IsCactus G) {o : V} (C : G.Walk o o) (_hC : C.IsCycle)
    (_hspan : ∀ x, x ∈ C.support),
    {e | R.readout () ⟨V,G,o,C,o⟩ e = true} = C.edgeSet

private theorem spanning_rejected : ¬ spanningArena.{u}.Law edgeBad := by
  intro h
  have hspan : ∀ x : ULift.{u} (Fin 3), x ∈ triangle.support := by
    rintro ⟨x⟩
    fin_cases x <;> simp [triangle]
  have hh := h triangle_cactus triangle triangle_cycle hspan
  have he : s(ULift.up (0 : Fin 3),ULift.up (1 : Fin 3)) ∈ triangle.{u}.edgeSet := by
    simp [triangle,Walk.edgeSet]
  rw [← hh] at he
  simpa [edgeBad,realize] using he

private theorem edge_dependence : ObservationalDependence edgeSignature.{u} edgeActual := by
  intro i
  refine ⟨⟨ULift (Fin 3),⊤,ULift.up 0,triangle,ULift.up 0⟩,
    s(ULift.up (0 : Fin 3),ULift.up (1 : Fin 3)),
    s(ULift.up (0 : Fin 3),ULift.up (0 : Fin 3)),?_⟩
  simp [edgeActual,realize]

def spanningRegistration : Registration spanningArena.{u}
    (type_of% @cycle_spanning_edges.{u}) where
  actual := edgeActual
  bridge := by simp only [spanningArena,edgeActual,realize,decide_eq_true_eq,Set.setOf_mem_eq]
  variation := ⟨by simpa only [edgeActual,realize,decide_eq_true_eq,Set.setOf_mem_eq] using
    @cycle_spanning_edges.{u},edgeBad,spanning_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨edgeBad,?_,?_,spanning_rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := edge_dependence

def register_cycle_spanning_edges : Contract.Registration (@cycle_spanning_edges.{u})
    (Realization edgeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_spanning_edges
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.spanningRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨spanningArena⟩
  objectArena := .source ⟨spanningArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source spanningArena ⟨spanningRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize edgeSignature
    (fun _ p e => @decide (e ∈ p.graph.edgeSet) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_spanning_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_spanning_edges

private def leafGraph : SimpleGraph (ULift.{u} (Fin 4)) :=
  SimpleGraph.fromRel fun x y => (x.down ≠ 0 ∧ y.down ≠ 0) ∨ (x.down = 0 ∧ y.down = 3)

private def leafTriangle : leafGraph.{u}.Walk (ULift.up 1) (ULift.up 1) :=
  .cons (v := ULift.up 2) (by norm_num [leafGraph,SimpleGraph.fromRel])
    (.cons (v := ULift.up 3) (by norm_num [leafGraph,SimpleGraph.fromRel])
      (.cons (by norm_num [leafGraph,SimpleGraph.fromRel]) .nil))

private theorem leaf_cycle : leafTriangle.{u}.IsCycle := by
  norm_num [Walk.isCycle_def,Walk.isTrail_def,leafTriangle,Sym2.eq_iff]

private theorem leaf_connected : leafGraph.{u}.Connected := by
  have hg : ∀ v : ULift.{u} (Fin 4), leafGraph.Reachable v (ULift.up 3) := by
    rintro ⟨v⟩
    fin_cases v
    · exact (show leafGraph.Adj (ULift.up 0) (ULift.up 3) by
        norm_num [leafGraph,SimpleGraph.fromRel]).reachable
    · exact (show leafGraph.Adj (ULift.up 1) (ULift.up 3) by
        norm_num [leafGraph,SimpleGraph.fromRel]).reachable
    · exact (show leafGraph.Adj (ULift.up 2) (ULift.up 3) by
        norm_num [leafGraph,SimpleGraph.fromRel]).reachable
    · exact .rfl
  constructor
  intro v w
  exact (hg v).trans (hg w).symm

private theorem leaf_cactus : IsCactus leafGraph.{u} := by
  letI : DecidableRel leafGraph.{u}.Adj := fun x y =>
    inferInstanceAs (Decidable (x ≠ y ∧
      (((x.down ≠ 0 ∧ y.down ≠ 0) ∨ (x.down = 0 ∧ y.down = 3)) ∨
       ((y.down ≠ 0 ∧ x.down ≠ 0) ∨ (y.down = 0 ∧ x.down = 3)))))
  let a : ULift.{u} (Fin 4) := ULift.up 1
  let b : ULift.{u} (Fin 4) := ULift.up 2
  let c : ULift.{u} (Fin 4) := ULift.up 3
  let d : ULift.{u} (Fin 4) := ULift.up 0
  let E : Finset (Sym2 (ULift.{u} (Fin 4))) := {s(a,b),s(a,c),s(b,c)}
  have hb : leafGraph.IsBridge s(d,c) := by rw [isBridge_iff]; decide
  have hfull : ∀ e : Sym2 (ULift.{u} (Fin 4)), e ∈ leafGraph.edgeSet →
      e = s(d,c) ∨ e ∈ E := by decide
  have hcard : E.card = 3 := by decide
  have hall {o : ULift.{u} (Fin 4)} (p : leafGraph.Walk o o) (hp : p.IsCycle) :
      p.edges.toFinset = E := by
    have hout : s(d,c) ∉ p.edges := hb.notMem_edges_of_isCycle hp
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      exact (hfull e (p.edges_subset_edgeSet (List.mem_toFinset.mp he))).resolve_left
        (fun heq => hout (heq ▸ List.mem_toFinset.mp he))
    · have hlen := hp.three_le_length
      have hc : p.edges.toFinset.card = p.length := by
        rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup,Walk.length_edges]
      omega
  intro o o' p q hp hq hne
  exact (hne ((hall p hp).trans (hall q hq).symm)).elim

abbrev strictArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V] [Finite V] {G : SimpleGraph V}
    (_hG : G.Connected) (_hcactus : IsCactus G) {o : V}
    (C : G.Walk o o) (_hC : C.IsCycle) (x : V) (_hx : x ∉ C.support),
    let A := {v | (G.deleteEdges C.edgeSet).Reachable x v}
    ∃ g, R.readout () ⟨V,G,o,C,x⟩ g = true ∧
      let B := Aᶜ ∪ {g}
      G = sideGraph G A ⊔ sideGraph G B ∧
      _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.OneVertexUnion
        (sideGraph G A) (sideGraph G B) A B g ∧
      Disjoint (sideGraph G A).edgeSet (sideGraph G B).edgeSet ∧
      (G.induce A).Connected ∧ (G.induce B).Connected ∧
      IsCactus (G.induce A) ∧ IsCactus (G.induce B) ∧
      (sideGraph G A).edgeSet.Nonempty ∧ (sideGraph G B).edgeSet.Nonempty ∧
      (sideGraph G A).edgeSet ⊂ G.edgeSet ∧ (sideGraph G B).edgeSet ⊂ G.edgeSet ∧
      Nat.card (G.induce A).edgeSet < Nat.card G.edgeSet ∧
      Nat.card (G.induce B).edgeSet < Nat.card G.edgeSet

private theorem strict_rejected : ¬ strictArena.{u}.Law bad := by
  intro h
  have hout : ULift.up (0 : Fin 4) ∉ leafTriangle.{u}.support := by simp [leafTriangle]
  obtain ⟨g,hg,_⟩ := h leaf_connected leaf_cactus leafTriangle leaf_cycle (ULift.up 0) hout
  simp [bad,realize] at hg

def strictRegistration : Registration strictArena.{u}
    (type_of% @cycle_component_strict_edges.{u}) where
  actual := actual
  bridge := by simp only [strictArena,actual,realize,decide_eq_true_eq,and_assoc,Set.mem_setOf_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq,and_assoc,Set.mem_setOf_eq] using
    @cycle_component_strict_edges.{u},bad,strict_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,strict_rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_cycle_component_strict_edges : Contract.Registration (@cycle_component_strict_edges.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_component_strict_edges
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.strictRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨strictArena⟩
  objectArena := .source ⟨strictArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source strictArena ⟨strictRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p g => @decide (g ∈ p.cycle.support ∧
      (p.graph.deleteEdges p.cycle.edgeSet).Reachable p.source g)
      (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.register_cycle_component_strict_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_component_strict_edges

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
