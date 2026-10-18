import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-family registrations retain the complete finite-edge tree telescope. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section

/-- The entire graph, actual finite edge type and all three terminals vary together. -/
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  finiteEdges : Fintype graph.edgeSet
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
  (fun _ p => @bondLaw p.Vertices p.graph p.finiteEdges p.a p.b p.c p.rate)
  (fun e => nomatch e)

def two : Realization signature.{u} := realize _ (fun _ _ _ => 2) (fun e => nomatch e)
def negative : Realization signature.{u} := realize _
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)

private theorem singleton_tree : (⊥ : SimpleGraph PUnit.{u+1}).IsTree :=
  ⟨SimpleGraph.connected_bot_iff.mpr ⟨inferInstance,inferInstance⟩,
   SimpleGraph.isAcyclic_bot⟩

theorem same_terminal_law {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] (a : V) (θ : G.edgeSet → ℝ) :
    bondLaw G a a a θ .all = 1 ∧ bondLaw G a a a θ .separate = 0 := by
  classical
  have hm (ω : G.edgeSet → Bool) : graphMode (bondGraph G ω) a a a = .all := by
    unfold graphMode
    rw [if_pos SimpleGraph.Reachable.rfl,if_pos SimpleGraph.Reachable.rfl]
  constructor
  · unfold bondLaw
    calc _ = ∑ ω : G.edgeSet → Bool, weight θ ω := by
           apply Finset.sum_congr rfl
           intro ω _
           rw [hm]
           exact if_pos rfl
         _ = 1 := weight_sum θ
  · unfold bondLaw
    apply Finset.sum_eq_zero
    intro ω _
    rw [hm]
    exact if_neg (by decide)

theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  let θ : G.edgeSet → ℝ := fun _ => 0
  refine ⟨⟨PUnit,G,inferInstance,PUnit.unit,PUnit.unit,PUnit.unit,θ⟩,.all,.separate,?_⟩
  change bondLaw G PUnit.unit PUnit.unit PUnit.unit θ .all ≠
    bondLaw G PUnit.unit PUnit.unit PUnit.unit θ .separate
  obtain ⟨hall,hsep⟩ := same_terminal_law PUnit.unit θ
  rw [hall,hsep]
  norm_num

theorem single_sensitivity (L : Realization signature.{u} → Prop)
    (bad : Realization signature.{u}) (hbad : ¬ L bad) :
    Sensitivity ⟨signature,L⟩ actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

abbrev lawArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [hE : Fintype G.edgeSet]
    (_hG : G.IsTree) (a b c : V) (θ : G.edgeSet → ℝ)
    (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    ∃ A B C : ℝ, A ∈ Set.Icc 0 1 ∧ B ∈ Set.Icc 0 1 ∧ C ∈ Set.Icc 0 1 ∧
      R.readout () ⟨V,G,hE,a,b,c,θ⟩ = law starEnds 0 1 2 ![A,B,C]

private theorem two_rejected : ¬ lawArena.{u}.Law two := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  obtain ⟨A,B,C,hA,hB,hC,hp⟩ := h singleton_tree PUnit.unit PUnit.unit PUnit.unit
    (fun _ => 0) (fun _ => by norm_num)
  have hh := congrFun hp .all
  rw [star_law] at hh
  change 2 = A*B*C at hh
  have hAB : A*B ≤ 1 := mul_le_one₀ hA.2 hB.1 hB.2
  have hABC : A*B*C ≤ 1 := by
    calc A*B*C ≤ 1*C := mul_le_mul_of_nonneg_right hAB hC.1
         _ ≤ 1 := by simpa using hC.2
  linarith

def lawRegistration : Registration lawArena.{u} (type_of% @tree_law.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tree_law,two,two_rejected⟩
  sensitivity := single_sensitivity _ two two_rejected
  dependence := dependence

abbrev boundArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [hE : Fintype G.edgeSet]
    (_hG : G.IsTree) (a b c : V) (θ : G.edgeSet → ℝ)
    (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    0 ≤ delta (R.readout () ⟨V,G,hE,a,b,c,θ⟩) ∧
      delta (bondLaw G a b c θ) ≤ bondLaw G a b c θ .ac

private theorem negative_rejected : ¬ boundArena.{u}.Law negative := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := (h singleton_tree PUnit.unit PUnit.unit PUnit.unit
    (fun _ => 0) (fun _ => by norm_num)).1
  norm_num [negative,realize,delta] at hh

def boundRegistration : Registration boundArena.{u} (type_of% @tree_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tree_bound,negative,negative_rejected⟩
  sensitivity := single_sensitivity _ negative negative_rejected
  dependence := dependence

def register_tree_law : Contract.Registration (@tree_law.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.register_tree_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.lawRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lawArena⟩
  objectArena := .source ⟨lawArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source lawArena ⟨lawRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => @bondLaw p.Vertices p.graph p.finiteEdges p.a p.b p.c p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def register_tree_bound : Contract.Registration (@tree_bound.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.register_tree_bound
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.boundRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source boundArena ⟨boundRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => @bondLaw p.Vertices p.graph p.finiteEdges p.a p.b p.c p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit
universe u
noncomputable section
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  start : Vertices
  finish : Vertices
  walk : graph.Walk start finish
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Sym2 p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize _
  (fun _ p e => @decide (e ∈ p.walk.edges) (Classical.propDecidable _)) (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} (_hG : G.IsAcyclic) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (r : G.Walk a c)
    (_hp : p.IsPath) (_hq : q.IsPath) (_hr : r.IsPath) (e : Sym2 V),
    R.readout () ⟨V,G,a,c,r⟩ e = true ↔
      (e ∈ p.edges ∧ e ∉ q.edges) ∨ (e ∈ q.edges ∧ e ∉ p.edges)
private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := @h PUnit.{u+1} (⊥ : SimpleGraph PUnit.{u+1}) isAcyclic_bot
    PUnit.unit PUnit.unit PUnit.unit .nil .nil .nil
    Walk.IsPath.nil Walk.IsPath.nil Walk.IsPath.nil s(PUnit.unit,PUnit.unit)
  norm_num [bad,realize] at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let G : SimpleGraph (ULift.{u} Bool) := ⊤
  let a : ULift.{u} Bool := ULift.up false
  let c : ULift.{u} Bool := ULift.up true
  have hadj : G.Adj a c := by simp [G,a,c]
  let r : G.Walk a c := .cons hadj .nil
  refine ⟨⟨ULift Bool,G,a,c,r⟩,s(a,c),s(a,a),?_⟩
  simp [actual,realize,r,a,c,Sym2.eq_iff]
def registration : Registration arena.{u} (type_of% @path_edge_symmDiff.{u}) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq] using
    @path_edge_symmDiff.{u},bad,rejected⟩
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
def register_path_edge_symmDiff : Contract.Registration (@path_edge_symmDiff.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path.register_path_edge_symmDiff
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path.registration
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
    (fun _ p e => @decide (e ∈ p.walk.edges) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [hE : Fintype G.edgeSet]
    (a b c : V) (θ : G.edgeSet → ℝ), ∑ s, R.readout () ⟨V,G,hE,a,b,c,θ⟩ s = 1
private theorem rejected : ¬ arena.{u}.Law two := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := h (G:=G) PUnit.unit PUnit.unit PUnit.unit (fun _ => 0)
  have hc : Fintype.card Mode = 5 := by decide
  norm_num [two,realize,hc] at hh

def registration : Registration arena.{u} (type_of% @bondLaw_sum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bondLaw_sum,two,rejected⟩
  sensitivity := single_sensitivity _ two rejected
  dependence := dependence

def register_bondLaw_sum : Contract.Registration (@bondLaw_sum.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization.register_bondLaw_sum
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization.registration
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
    (fun _ p => @bondLaw p.Vertices p.graph p.finiteEdges p.a p.b p.c p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Cylinder
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
universe u
noncomputable section

structure Parameters where
  Edges : Type u
  finiteEdges : Fintype Edges
  decidableEdges : DecidableEq Edges
  rate : Edges → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.Edges
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p S => by
    classical
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact ∑ ω : p.Edges → Bool,
      if (∀ e ∈ S, ω e = true) then weight p.rate ω else 0)
  (fun e => nomatch e)

def bad : Realization signature.{u} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [hE : Fintype E] [dE : DecidableEq E]
    (θ : E → ℝ) (S : Finset E),
    R.readout () ⟨E,hE,dE,θ⟩ S = ∏ e ∈ S, θ e

private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  have hh := h (E := PEmpty.{u+1}) (fun _ => 0) ∅
  simpa [bad,realize] using hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  refine ⟨⟨PUnit.{u+1},inferInstance,inferInstance,fun _ => 0⟩,∅,{PUnit.unit},?_⟩
  simp [actual,realize,cylinder_mass]

def registration : Registration arena.{u} (type_of% @cylinder_mass.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cylinder_mass,bad,rejected⟩
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

def register_cylinder_mass : Contract.Registration (@cylinder_mass.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Cylinder.register_cylinder_mass
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Cylinder.registration
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
    (fun _ p S => by
      classical
      letI := p.finiteEdges
      letI := p.decidableEdges
      exact ∑ ω : p.Edges → Bool,
        if (∀ e ∈ S, ω e = true) then weight p.rate ω else 0)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Cylinder.register_cylinder_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cylinder_mass

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Cylinder

open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.register_tree_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_tree_law
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.register_tree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_tree_bound
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Path.register_path_edge_symmDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_path_edge_symmDiff
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.Normalization.register_bondLaw_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_bondLaw_sum
