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

private theorem same_terminal_law {V : Type u} {G : SimpleGraph V}
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

private theorem dependence : ObservationalDependence signature.{u} actual := by
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

private theorem single_sensitivity (L : Realization signature.{u} → Prop)
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
