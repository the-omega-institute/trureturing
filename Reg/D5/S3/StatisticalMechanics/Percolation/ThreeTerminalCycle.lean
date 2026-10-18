import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The original graph-edge cube supplies the complete five-mode probability readout. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit
universe u
noncomputable section

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
def bad : Realization signature.{u} := realize _ (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [fE : Fintype G.edgeSet] {v : V}
    (p : G.Walk v v) (_hp : p.IsCycle) (_hedges : G.edgeSet = p.edgeSet)
    (a b c : V) (_ha : a ∈ p.support) (_hb : b ∈ p.support) (_hc : c ∈ p.support)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (θ : G.edgeSet → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    ∃ u v r : ℝ, u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧ r ∈ Set.Icc 0 1 ∧
      R.readout () ⟨V,G,fE,a,b,c,θ⟩ =
        law triangleArmsEnds 0 1 2 ![u,v,r,1,1,1] ∧
      0 ≤ delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) ∧
      delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) +
        R.readout () ⟨V,G,fE,a,b,c,θ⟩ .all * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac ≤
          2 * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac

private def triWalk : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Walk
    (ULift.up 0) (ULift.up 0) :=
  let h01 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 0) (ULift.up 1) := by simp
  let h12 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 1) (ULift.up 2) := by simp
  let h20 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 2) (ULift.up 0) := by simp
  .cons h01 (.cons h12 (.cons h20 .nil))
private theorem triWalk_cycle : (triWalk.{u}).IsCycle := by
  simp [triWalk,Walk.cons_isCycle_iff,Walk.isPath_def,Walk.edges_cons,Sym2.eq_iff]
private theorem triWalk_edges :
    (⊤ : SimpleGraph (ULift.{u} (Fin 3))).edgeSet = triWalk.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    fin_cases x <;> fin_cases y <;> simp [triWalk,Walk.edgeSet,Sym2.eq_iff]

private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  letI : Fintype (⊤ : SimpleGraph (ULift.{u} (Fin 3))).edgeSet := Fintype.ofFinite _
  have hh := h triWalk triWalk_cycle triWalk_edges (ULift.up 0) (ULift.up 1) (ULift.up 2)
    (by simp [triWalk]) (by simp [triWalk]) (by simp [triWalk])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ => 0) (by intro e; exact ⟨le_rfl,by norm_num⟩)
  obtain ⟨u,v,r,_,_,_,_,_,hineq⟩ := hh
  norm_num [bad,realize,delta] at hineq

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let V := PUnit.{u+1}
  letI : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  let G : SimpleGraph V := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  let θ : G.edgeSet → ℝ := fun _ => 0
  refine ⟨⟨V,G,inferInstance,PUnit.unit,PUnit.unit,PUnit.unit,θ⟩,.all,.separate,?_⟩
  have hmode (ω : G.edgeSet → Bool) :
      graphMode (bondGraph G ω) PUnit.unit PUnit.unit PUnit.unit = .all := by
    simp [graphMode]
  change bondLaw G _ _ _ θ .all ≠ bondLaw G _ _ _ θ .separate
  simp only [bondLaw,hmode,ite_true,reduceCtorEq,ite_false,Finset.sum_const_zero]
  rw [weight_sum]
  norm_num

def registration : Registration arena.{u} (type_of% @cycle_law_and_invariant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_law_and_invariant,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact isEmptyElim e
    · intro e
      exact isEmptyElim e
  dependence := dependence

def register_cycle_law_and_invariant : Contract.Registration (@cycle_law_and_invariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_cycle_law_and_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.registration
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

abbrev coincidentArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (G : SimpleGraph V) [fE : Fintype G.edgeSet]
    (a b c : V) (_heq : a = b ∨ a = c ∨ b = c)
    (θ : G.edgeSet → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1)
    (C : ℝ) (_hC : 1 ≤ C),
    0 ≤ delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) ∧
      delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) +
        R.readout () ⟨V,G,fE,a,b,c,θ⟩ .all * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac ≤
          C * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac

private theorem coincident_rejected : ¬ coincidentArena.{u}.Law bad := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := h G PUnit.unit PUnit.unit PUnit.unit (Or.inl rfl)
    (fun _ => 0) (by intro e; exact ⟨le_rfl,by norm_num⟩) 1 le_rfl
  norm_num [bad,realize,delta] at hh

private theorem single_sensitivity (L : Realization signature.{u} → Prop)
    (hbad : ¬ L bad) : Sensitivity ⟨signature,L⟩ actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact isEmptyElim e
  · intro e
    exact isEmptyElim e

def coincidentRegistration : Registration coincidentArena.{u}
    (type_of% @coincident_terminal_invariant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coincident_terminal_invariant,bad,coincident_rejected⟩
  sensitivity := single_sensitivity _ coincident_rejected
  dependence := dependence

abbrev cycleArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [fE : Fintype G.edgeSet] {v : V}
    (p : G.Walk v v) (_hp : p.IsCycle) (_hedges : G.edgeSet = p.edgeSet)
    (a b c : V) (_ha : a ∈ p.support) (_hb : b ∈ p.support) (_hc : c ∈ p.support)
    (θ : G.edgeSet → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    0 ≤ delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) ∧
      delta (R.readout () ⟨V,G,fE,a,b,c,θ⟩) +
        R.readout () ⟨V,G,fE,a,b,c,θ⟩ .all * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac ≤
          2 * R.readout () ⟨V,G,fE,a,b,c,θ⟩ .ac

private theorem cycle_rejected : ¬ cycleArena.{u}.Law bad := by
  classical
  intro h
  letI : Fintype (⊤ : SimpleGraph (ULift.{u} (Fin 3))).edgeSet := Fintype.ofFinite _
  have hh := h triWalk triWalk_cycle triWalk_edges (ULift.up 0) (ULift.up 1) (ULift.up 2)
    (by simp [triWalk]) (by simp [triWalk]) (by simp [triWalk])
    (fun _ => 0) (by intro e; exact ⟨le_rfl,by norm_num⟩)
  norm_num [bad,realize,delta] at hh

def cycleRegistration : Registration cycleArena.{u} (type_of% @cycle_invariant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_invariant,bad,cycle_rejected⟩
  sensitivity := single_sensitivity _ cycle_rejected
  dependence := dependence

def register_coincident_terminal_invariant : Contract.Registration (@coincident_terminal_invariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_coincident_terminal_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.coincidentRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coincidentArena⟩
  objectArena := .source ⟨coincidentArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source coincidentArena ⟨coincidentRegistration⟩
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

def register_cycle_invariant : Contract.Registration (@cycle_invariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_cycle_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.cycleRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cycleArena⟩
  objectArena := .source ⟨cycleArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source cycleArena ⟨cycleRegistration⟩
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

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_cycle_law_and_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_law_and_invariant

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_coincident_terminal_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_coincident_terminal_invariant

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.register_cycle_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_invariant

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle
