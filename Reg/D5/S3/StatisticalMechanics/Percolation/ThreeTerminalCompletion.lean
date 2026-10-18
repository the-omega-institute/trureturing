import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness

/-! Full-source registrations for the actual bond-law completion conclusions. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section

/-- The same probability operation appears in every clause of the original conclusion. -/
def Pyramid (p : Mode → ℝ) (C : ℝ) : Prop :=
  (p .ac < 1 →
    |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤ C*p .ac/(1-p .ac) ∧
    ∀ f : Mode → ℝ,
      |(∑ s, f s*p s)-(∑ s, f s*completion p s)| ≤
        |interaction f| * (C*p .ac/(1-p .ac))) ∧
  (p .ac = 0 → p = completion p) ∧
  (p .ac = 1 → p = fun s => if s = .ac then 1 else 0)

namespace Tree
open Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

def bad : Realization signature.{u} := realize _ (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [hE : Fintype G.edgeSet]
    (_hG : G.IsTree) (a b c : V) (θ : G.edgeSet → ℝ)
    (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    let p := R.readout () ⟨V,G,hE,a,b,c,θ⟩
    (p .ac < 1 →
      |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤ p .ac/(1-p .ac) ∧
      ∀ f : Mode → ℝ,
        |(∑ s, f s*p s)-(∑ s, f s*completion p s)| ≤
          |interaction f| * (p .ac/(1-p .ac))) ∧
    (p .ac = 0 → p = completion p) ∧
    (p .ac = 1 → p = fun s => if s = .ac then 1 else 0)

private theorem rejected : ¬ arena.{u}.Law bad := by
  classical
  intro h
  let G : SimpleGraph PUnit.{u+1} := ⊥
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hG : G.IsTree :=
    ⟨SimpleGraph.connected_bot_iff.mpr ⟨inferInstance,inferInstance⟩,SimpleGraph.isAcyclic_bot⟩
  have hh := (h hG PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) (fun _ => by norm_num)).1
  norm_num [bad,realize] at hh

def registration : Registration arena.{u} (type_of% @tree_pyramid.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tree_pyramid,bad,rejected⟩
  sensitivity := single_sensitivity _ bad rejected
  dependence := dependence

def register_tree_pyramid : Contract.Registration (@tree_pyramid.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Tree.register_tree_pyramid
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Tree.registration
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
end Tree

namespace Pendant
open Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness

def bad : Realization signature := realize _ (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ u v s A : ℝ, u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 →
    s ∈ Set.Icc 0 1 → A ∈ Set.Icc 0 1 → Pyramid (R.readout () (u,v,s,A)) 2
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := (h 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [bad,realize] at hh

def registration : Registration arena (type_of% @pendant_pyramid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pendant_pyramid,bad,rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad rejected
  dependence := dependence

def register_pendant_pyramid : Contract.Registration (@pendant_pyramid)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Pendant.register_pendant_pyramid
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Pendant.registration
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
    (fun _ p => law pendantEnds 0 1 2 ![p.1,p.2.1,p.2.2.1,p.2.2.2]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pendant

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion

open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Tree
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Tree.register_tree_pyramid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_tree_pyramid
open
  Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Pendant
in
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.Pendant.register_pendant_pyramid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_pendant_pyramid
