/- GID: D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PaddingConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.module_two_connected; premises=D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.core_parent_facts,D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.marked_parent_facts
   digest: Exact local paths feed arbitrary-size padding connectivity. -/

import D5.S3.Combinatorics.Graph.StarForming.PaddingRings
import D5.S3.Combinatorics.Graph.StarForming.CyclicProjection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual path argument for CUBIC_EQUALITY_PADDING_RINGS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Local parent/rank certificates check only edges on twenty
or thirty-four fixed vertices. Their fulfilled premises are consumed
by a symbolic arbitrary transitive-permutation proof, never by an
extrapolation from finitely many core lengths. -/
namespace D5.S3.Combinatorics.Graph.StarForming.PaddingConnectivity
open PaddingModule

private def coreGraph : SimpleGraph (Fin 20) where
  Adj v w := EqualityCore.internal v w ∧ ¬ ((v=14 ∧ w=15) ∨ (v=15 ∧ w=14))
  symm := ⟨by intro v w h; refine ⟨h.1.symm,?_⟩; tauto⟩
  loopless := ⟨by decide +kernel⟩
private instance : DecidableRel coreGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ ¬ _))

private def markedAdj : Fin 14 ⊕ Fin 20 → Fin 14 ⊕ Fin 20 → Prop
  | .inl v,.inl w => HeawoodPorts.graph.Adj v w
  | .inr v,.inr w => coreGraph.Adj v w ∧ ¬ ((v=12 ∧ w=13) ∨ (v=13 ∧ w=12))
  | .inl v,.inr w => (v=0 ∧ w=13) ∨ (v=8 ∧ w=12)
  | .inr v,.inl w => (w=0 ∧ v=13) ∨ (w=8 ∧ v=12)
private def decode : Fin 34 → Fin 14 ⊕ Fin 20 := (finSumFinEquiv (m:=14) (n:=20)).symm
private def markedGraph : SimpleGraph (Fin 34) where
  Adj v w := markedAdj (decode v) (decode w)
  symm := ⟨by
    intro v w h
    have hs : ∀ a b, markedAdj a b → markedAdj b a := by
      intro a b
      cases a <;> cases b <;> dsimp [markedAdj]
      · exact HeawoodPorts.graph.adj_symm
      · exact id
      · exact id
      · intro h; refine ⟨coreGraph.adj_symm h.1,?_⟩; tauto
    exact hs _ _ h⟩
  loopless := ⟨by
    intro v h
    have hi : ∀ a, ¬ markedAdj a a := by
      intro a; cases a <;> dsimp [markedAdj]
      · exact HeawoodPorts.graph.irrefl
      · exact fun h => coreGraph.irrefl h.1
    exact hi _ h⟩
private instance : DecidableRel markedGraph.Adj := by
  intro v w
  unfold markedGraph
  dsimp
  cases decode v <;> cases decode w <;> dsimp [markedAdj] <;> infer_instance

private def core_root (z : Fin 20) : Fin 20 := if z=0 then 1 else 0
private def core_parent : Fin 20 → Fin 20 → Fin 20 :=
  ![![1,1,1,2,3,4,18,1,2,3,4,19,13,7,8,9,10,11,8,7],
    ![0,0,8,2,10,4,0,13,18,19,18,19,6,12,13,16,10,16,6,7],
    ![0,0,0,9,10,11,0,1,18,19,18,19,6,7,13,9,10,11,6,7],
    ![0,0,1,0,10,11,0,1,2,19,18,19,6,7,8,9,10,11,6,7],
    ![0,0,1,2,0,11,0,1,2,3,18,19,6,7,8,9,10,11,6,7],
    ![0,0,1,2,3,0,0,1,2,3,18,19,6,7,8,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,4,19,13,7,8,9,10,11,8,7],
    ![0,0,1,2,3,4,0,0,2,3,18,5,6,12,8,9,10,16,6,9],
    ![0,0,1,2,3,4,0,1,0,3,18,19,6,7,13,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,0,18,19,6,7,8,16,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,0,19,6,7,8,9,15,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,0,6,7,8,9,10,16,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,0,7,8,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,6,0,8,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,6,7,0,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,6,7,8,0,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,6,7,8,9,0,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,18,19,6,7,8,9,10,0,6,7],
    ![0,0,1,2,3,4,0,1,2,3,4,19,6,7,8,9,10,11,0,7],
    ![0,0,1,2,3,4,0,1,2,3,18,5,6,7,8,9,10,16,6,0]]
private def core_rank : Fin 20 → Fin 20 → ℕ :=
  ![![0,0,1,2,3,4,4,1,2,3,4,3,3,2,3,4,5,4,3,2],
    ![0,0,4,5,4,5,1,4,3,6,3,6,2,3,4,5,4,5,2,5],
    ![0,1,0,5,4,5,1,2,3,4,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,0,4,5,1,2,3,4,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,3,0,5,1,2,3,4,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,3,4,0,1,2,3,4,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,3,4,5,0,2,3,4,5,4,4,3,4,5,6,5,4,3],
    ![0,1,2,3,4,5,1,0,3,4,3,6,2,3,4,5,4,5,2,5],
    ![0,1,2,3,4,5,1,2,0,4,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,0,3,4,2,3,4,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,0,4,2,3,4,5,6,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,0,2,3,4,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,0,3,4,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,2,0,4,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,2,3,0,5,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,2,3,4,0,4,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,2,3,4,5,0,5,2,3],
    ![0,1,2,3,4,5,1,2,3,4,3,4,2,3,4,5,4,0,2,3],
    ![0,1,2,3,4,5,1,2,3,4,5,4,2,3,4,5,6,5,0,3],
    ![0,1,2,3,4,5,1,2,3,4,3,6,2,3,4,5,4,5,2,0]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem core_parent_facts : ∀ z a : Fin 20, a≠z → core_parent z a≠z ∧
    (a=core_root z ∨ coreGraph.Adj a (core_parent z a) ∧
      core_rank z (core_parent z a)<core_rank z a) := by
  decide +kernel

private theorem core_root_survives (z : Fin 20) : core_root z≠z := by
  unfold core_root
  split <;> simp_all [eq_comm]

private theorem core_delete_preconnected (z : Fin 20) :
    (coreGraph.induce {a | a≠z}).Preconnected := by
  let p : {a : Fin 20 // a≠z} → {a : Fin 20 // a≠z} :=
    fun a => ⟨core_parent z a,(core_parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨core_root z,core_root_survives z⟩ p
    (fun a => core_rank z a)
  intro a ha
  rcases (core_parent_facts z a a.property).2 with h | h
  · exact (ha (Subtype.ext h)).elim
  · exact h

private theorem core_preconnected : coreGraph.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 20, ∃ z : Fin 20, a≠z ∧ b≠z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (coreGraph.induce {a | a≠z}) →g coreGraph := ⟨fun a => a.val,fun h => h⟩
  exact ((core_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

private def marked_root (z : Fin 34) : Fin 34 := if z=0 then 1 else 0
private def marked_parent : Fin 34 → Fin 34 → Fin 34 :=
  ![![1,1,9,11,11,8,9,6,1,1,2,1,5,5,20,14,15,16,24,18,26,15,32,17,32,33,8,21,22,30,24,30,20,21],
    ![0,0,10,10,7,12,7,0,5,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,0,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,0,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,9,10,10,0,13,7,0,1,6,0,3,2,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,0,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,0,0,1,2,0,4,4,3,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,9,10,10,12,12,9,0,1,2,0,3,2,3,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,0,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,20,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,0,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,12,11,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,9,10,10,7,12,7,0,5,6,0,0,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,13,7,0,1,6,0,4,0,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,0,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,0,21,15,16,17,25,32,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,20,0,22,23,17,25,32,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,0,23,17,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,0,19,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,0,25,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,0,14,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,0,27,28,33,32,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,16,22,16,17,18,32,0,28,17,32,19,8,0,27,23,24,30,22,23],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,0,33,32,33,8,0,27,23,29,25,20,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,0,32,33,8,0,27,30,31,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,0,33,8,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,18,14,27,28,33,32,0,8,0,27,23,29,30,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,0,0,27,23,29,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,20,14,15,16,24,18,26,15,32,17,32,33,8,0,22,30,24,30,20,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,16,33,32,33,8,0,0,23,29,25,20,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,0,31,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,0,25,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,32,33,8,0,27,23,29,0,22,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,25,14,27,28,33,18,33,8,0,27,23,29,25,0,21],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,6,15,21,15,16,17,18,14,27,28,17,32,19,8,0,27,23,24,30,22,0]]
private def marked_rank : Fin 34 → Fin 34 → ℕ :=
  ![![0,0,2,2,2,2,2,3,1,1,3,1,3,3,4,5,6,7,6,7,3,6,5,8,5,8,2,7,6,7,6,7,4,7],
    ![0,0,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,0,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,0,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,0,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,0,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,0,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,4,4,4,0,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,0,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,0,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,4,4,2,4,2,1,5,3,0,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,0,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,0,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,0,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,0,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,6,0,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,0,5,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,0,6,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,0,5,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,0,5,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,0,2,3,4,5,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,6,5,4,5,6,7,5,0,3,6,5,8,6,1,2,7,6,7,4,7],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,0,4,7,4,6,1,2,5,6,5,6,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,0,5,4,6,1,2,7,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,0,4,6,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,7,5,2,3,4,5,0,6,1,2,5,6,7,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,0,1,2,5,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,8,9,10,11,10,11,7,10,9,12,9,12,6,0,10,11,10,11,8,11],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,5,4,7,4,6,1,0,5,6,5,6,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,0,6,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,0,5,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,5,4,6,1,2,5,6,0,4,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,5,5,2,3,4,7,4,6,1,2,5,6,5,0,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,3,4,3,4,5,6,7,5,2,3,6,5,8,6,1,2,7,6,7,4,0]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem marked_parent_facts : ∀ z a : Fin 34, a≠z → marked_parent z a≠z ∧
    (a=marked_root z ∨ markedGraph.Adj a (marked_parent z a) ∧
      marked_rank z (marked_parent z a)<marked_rank z a) := by
  decide +kernel

private theorem marked_root_survives (z : Fin 34) : marked_root z≠z := by
  unfold marked_root
  split <;> simp_all [eq_comm]

private theorem marked_delete_preconnected (z : Fin 34) :
    (markedGraph.induce {a | a≠z}).Preconnected := by
  let p : {a : Fin 34 // a≠z} → {a : Fin 34 // a≠z} :=
    fun a => ⟨marked_parent z a,(marked_parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨marked_root z,marked_root_survives z⟩ p
    (fun a => marked_rank z a)
  intro a ha
  rcases (marked_parent_facts z a a.property).2 with h | h
  · exact (ha (Subtype.ext h)).elim
  · exact h

private theorem marked_preconnected : markedGraph.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 34, ∃ z : Fin 34, a≠z ∧ b≠z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (markedGraph.induce {a | a≠z}) →g markedGraph := ⟨fun a => a.val,fun h => h⟩
  exact ((marked_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

theorem mapped_deleted_reachable {A V : Type*} (B : SimpleGraph A) (G : SimpleGraph V)
    (hB : B.Preconnected) (hd : ∀ z, (B.induce {a | a≠z}).Preconnected)
    (f : A ↪ V) (hf : ∀ a b, B.Adj a b → G.Adj (f a) (f b))
    (z : V) (a b : A) (ha : f a≠z) (hb : f b≠z) :
    (G.induce {x | x≠z}).Reachable ⟨f a,ha⟩ ⟨f b,hb⟩ := by
  classical
  by_cases hz : ∃ c, f c=z
  · obtain ⟨c,hc⟩ := hz
    have hac : a≠c := fun h => ha (h ▸ hc)
    have hbc : b≠c := fun h => hb (h ▸ hc)
    let g : (B.induce {a | a≠c}) →g (G.induce {x | x≠z}) :=
      ⟨fun a => ⟨f a.val,fun h => a.property (f.injective (h.trans hc.symm))⟩,
        fun h => hf _ _ h⟩
    exact ((hd c) ⟨a,hac⟩ ⟨b,hbc⟩).map g
  · let g : B →g (G.induce {x | x≠z}) :=
      ⟨fun a => ⟨f a,fun h => hz ⟨a,h⟩⟩,fun h => hf _ _ h⟩
    exact (hB a b).map g

variable {I : Type} [Fintype I] [DecidableEq I]

private def index (mark : I) : Vertex I → I
  | .inl _ => mark
  | .inr x => x.1

private def coreEmbed (i : I) : Fin 20 ↪ Vertex I :=
  ⟨fun v => .inr (i,v),by intro v w h; exact (Prod.mk.inj (Sum.inr.inj h)).2⟩

private def markedMap (mark : I) : Fin 14 ⊕ Fin 20 → Vertex I
  | .inl v => .inl v
  | .inr v => .inr (mark,v)

private def markedEmbed (mark : I) : Fin 34 ↪ Vertex I where
  toFun := fun v => markedMap mark (decode v)
  inj' := by
    intro a b h
    apply (finSumFinEquiv (m:=14) (n:=20)).symm.injective
    have hi : Function.Injective (markedMap mark) := by
      intro x y he
      cases x <;> cases y <;> simp_all [markedMap]
    exact hi h

private theorem core_edge (e : Equiv.Perm I) (mark i : I) (hi : i≠mark)
    (a b : Fin 20) (h : coreGraph.Adj a b) :
    (graph e mark).Adj (coreEmbed i a) (coreEmbed i b) := by
  change (FourPortCore.graph e mark).Adj (i,a) (i,b)
  refine ⟨Or.inl ⟨rfl,h.1⟩,?_⟩
  simp [FourPortCore.cut,hi]

private theorem marked_edge (e : Equiv.Perm I) (mark : I)
    (a b : Fin 34) (h : markedGraph.Adj a b) :
    (graph e mark).Adj (markedEmbed mark a) (markedEmbed mark b) := by
  change markedAdj (decode a) (decode b) at h
  change (graph e mark).Adj (markedMap mark (decode a)) (markedMap mark (decode b))
  generalize ha : decode a = aa at h ⊢
  generalize hb : decode b = bb at h ⊢
  cases aa with
  | inl v => cases bb with
    | inl w => exact h
    | inr w => exact ⟨rfl,h⟩
  | inr v => cases bb with
    | inl w => exact ⟨rfl,h⟩
    | inr w =>
      refine ⟨Or.inl ⟨rfl,h.1.1⟩,?_⟩
      change ¬ (mark=mark ∧ mark=mark ∧ _)
      intro hc
      rcases hc.2.2 with h0 | h0 | h0 | h0
      · exact h.2 (Or.inl h0)
      · exact h.2 (Or.inr h0)
      · exact h.1.2 (Or.inl h0)
      · exact h.1.2 (Or.inr h0)

private theorem marked_preimage (mark : I) (x : Vertex I) (h : index mark x=mark) :
    ∃ a, markedEmbed mark a=x := by
  cases x with
  | inl v =>
    refine ⟨finSumFinEquiv (m:=14) (n:=20) (.inl v),?_⟩
    simp [markedEmbed,decode,markedMap]
  | inr x =>
    rcases x with ⟨i,v⟩
    change i=mark at h
    subst i
    refine ⟨finSumFinEquiv (m:=14) (n:=20) (.inr v),?_⟩
    simp [markedEmbed,decode,markedMap]

private theorem core_preimage (mark : I) (x : Vertex I) (h : index mark x≠mark) :
    ∃ a, coreEmbed (index mark x) a=x := by
  cases x with
  | inl v => exact (h rfl).elim
  | inr x => exact ⟨x.2,rfl⟩

private theorem fiber_preconnected (e : Equiv.Perm I) (mark : I)
    (x y : Vertex I) (h : index mark x=index mark y) : (graph e mark).Reachable x y := by
  by_cases hx : index mark x=mark
  · obtain ⟨a,rfl⟩ := marked_preimage mark x hx
    obtain ⟨b,rfl⟩ := marked_preimage mark y (h.symm.trans hx)
    let f : markedGraph →g graph e mark := ⟨(fun v => markedEmbed mark v),fun h => marked_edge e mark _ _ h⟩
    exact (marked_preconnected a b).map f
  · obtain ⟨a,ha⟩ := core_preimage mark x hx
    obtain ⟨b,hb⟩ := core_preimage mark y (fun hy => hx (h.trans hy))
    rw [← h] at hb
    let f : coreGraph →g graph e mark := ⟨(fun v => coreEmbed (index mark x) v),fun h => core_edge e mark _ hx _ _ h⟩
    rw [← ha,← hb]
    exact (core_preconnected a b).map f

private theorem deleted_fiber_preconnected (e : Equiv.Perm I) (mark : I) (z : Vertex I)
    (x y : {v : Vertex I // v≠z}) (h : index mark x.val=index mark y.val) :
    ((graph e mark).induce {v | v≠z}).Reachable x y := by
  by_cases hx : index mark x.val=mark
  · obtain ⟨a,ha⟩ := marked_preimage mark x.val hx
    obtain ⟨b,hb⟩ := marked_preimage mark y.val (h.symm.trans hx)
    have h1 : markedEmbed mark a≠z := ha ▸ x.property
    have h2 : markedEmbed mark b≠z := hb ▸ y.property
    have hr := mapped_deleted_reachable markedGraph (graph e mark) marked_preconnected
      marked_delete_preconnected (markedEmbed mark) (marked_edge e mark) z a b h1 h2
    have hax : (⟨_,h1⟩ : {v : Vertex I // v≠z})=x := Subtype.ext ha
    have hby : (⟨_,h2⟩ : {v : Vertex I // v≠z})=y := Subtype.ext hb
    rwa [hax,hby] at hr
  · obtain ⟨a,ha⟩ := core_preimage mark x.val hx
    obtain ⟨b,hb⟩ := core_preimage mark y.val (fun hy => hx (h.trans hy))
    rw [← h] at hb
    have h1 : coreEmbed (index mark x.val) a≠z := ha ▸ x.property
    have h2 : coreEmbed (index mark x.val) b≠z := hb ▸ y.property
    have hr := mapped_deleted_reachable coreGraph (graph e mark) core_preconnected
      core_delete_preconnected (coreEmbed (index mark x.val)) (core_edge e mark _ hx) z a b h1 h2
    have hax : (⟨_,h1⟩ : {v : Vertex I // v≠z})=x := Subtype.ext ha
    have hby : (⟨_,h2⟩ : {v : Vertex I // v≠z})=y := Subtype.ext hb
    rwa [hax,hby] at hr

/-- The actual open padding module, before the last ring seam, is connected
and stays connected after every vertex deletion for every positive cyclic
core size. The permutation hypothesis is transitivity, not a size bound. -/
theorem module_two_connected (e : Equiv.Perm I) (mark : I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) :
    (graph e mark).Connected ∧
    (∀ z : Vertex I, ((graph e mark).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (Vertex I) := by
  let p : I → Vertex I := fun i => .inr (i,5)
  let q : I → Vertex I := fun i => .inr (i,0)
  have hp : ∀ i, index mark (p i)=i := fun _ => rfl
  have hq : ∀ i, index mark (q i)=i := fun _ => rfl
  have hn : ∀ i, p i≠q i := by intro i h; cases h
  have hb : ∀ i, (graph e mark).Adj (p i) (q (e i)) := by
    intro i
    refine ⟨Or.inr (Or.inl ⟨rfl,rfl,rfl⟩),?_⟩
    simp [p,q,FourPortCore.cut]
  refine ⟨⟨CyclicProjection.preconnected _ (index mark) e horbit p q hp hq
    (fiber_preconnected e mark) hb⟩,?_,?_⟩
  · intro z
    refine
      { preconnected := CyclicProjection.delete_preconnected _ (index mark) e horbit p q hp hq hn z
          (deleted_fiber_preconnected e mark z) hb
        nonempty := ?_ }
    by_cases hz : z=Sum.inl 0
    · exact ⟨⟨Sum.inl 1,by
        rw [hz]
        intro h
        have hh := Sum.inl.inj h
        norm_num at hh⟩⟩
    · exact ⟨⟨Sum.inl 0,Ne.symm hz⟩⟩
  · simp only [Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega

end D5.S3.Combinatorics.Graph.StarForming.PaddingConnectivity


namespace D5.S3.Combinatorics.Graph.StarForming.PaddingConnectivity
open PaddingRings
variable {J : Type} [Fintype J] [DecidableEq J]
variable {K : J → Type} [∀ j, Fintype (K j)] [∀ j, DecidableEq (K j)]

/-- Independently varying positive cyclic modules remain connected after
every single vertex deletion. The module and core permutations need only
be transitive, and singleton cyclic seams remain in scope. -/
theorem rings_two_connected [Nonempty J] (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J)
    (hq : ∀ j, ∀ a b, ∃ n : ℕ, (q j : K j → K j)^[n] a=b)
    (he : ∀ i j, ∃ n : ℕ, (e : J → J)^[n] i=j) :
    (PaddingRings.graph q mark e).Connected ∧
    (∀ z : PaddingRings.Vertex K, ((PaddingRings.graph q mark e).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (PaddingRings.Vertex K) := by
  letI : Nonempty (PaddingRings.Vertex K) := ⟨⟨Classical.arbitrary J,Sum.inl 0⟩⟩
  have hm (j : J) := PaddingConnectivity.module_two_connected (q j) (mark j) (hq j)
  have hl (x y : PaddingRings.Vertex K) (h : x.1=y.1) : (PaddingRings.graph q mark e).Reachable x y := by
    rcases x with ⟨i,a⟩
    rcases y with ⟨j,b⟩
    change i=j at h
    subst j
    let f : (PaddingModule.graph (q i) (mark i)) →g PaddingRings.graph q mark e :=
      ⟨(fun v => (⟨i,v⟩ : PaddingRings.Vertex K)),fun h => Or.inl (PaddingRings.Within.intro i _ _ h)⟩
    exact ((hm i).1.preconnected a b).map f
  have hd (z : PaddingRings.Vertex K) (x y : {v : PaddingRings.Vertex K // v≠z})
      (h : x.val.1=y.val.1) :
      ((PaddingRings.graph q mark e).induce {v | v≠z}).Reachable x y := by
    rcases x with ⟨⟨i,a⟩,ha⟩
    rcases y with ⟨⟨j,b⟩,hb⟩
    change i=j at h
    subst j
    let f : PaddingModule.Vertex (K i) ↪ PaddingRings.Vertex K :=
      ⟨(fun v => (⟨i,v⟩ : PaddingRings.Vertex K)),fun _ _ h => by simpa using h⟩
    exact PaddingConnectivity.mapped_deleted_reachable _ _ (hm i).1.preconnected
      (fun z => ((hm i).2.1 z).preconnected) f
      (fun a b h => Or.inl (PaddingRings.Within.intro i a b h)) z a b ha hb
  have hp : ∀ i, (left mark i).1=i := fun _ => rfl
  have hr : ∀ i, (right mark i).1=i := fun _ => rfl
  have hn : ∀ i, left mark i≠right mark i := by
    intro i h
    have hh := (Sigma.mk.inj_iff.mp h).2
    cases hh
  have hb : ∀ i, (PaddingRings.graph q mark e).Adj (left mark i) (right mark (e i)) :=
    fun i => Or.inr (Or.inl ⟨i,rfl,rfl⟩)
  refine ⟨⟨CyclicProjection.preconnected _ Sigma.fst e he (left mark) (right mark)
    hp hr hl hb⟩,?_,?_⟩
  · intro z
    refine
      { preconnected := CyclicProjection.delete_preconnected _ Sigma.fst e he (left mark) (right mark)
          hp hr hn z (hd z) hb
        nonempty := ?_ }
    by_cases hz : left mark z.1=z
    · exact ⟨⟨right mark z.1,fun h => hn _ (hz.trans h.symm)⟩⟩
    · exact ⟨⟨left mark z.1,hz⟩⟩
  · obtain ⟨j⟩ := (inferInstance : Nonempty J)
    have hi : Function.Injective (fun v : PaddingModule.Vertex (K j) => (⟨j,v⟩ : PaddingRings.Vertex K)) :=
      fun _ _ h => by simpa using h
    exact (hm j).2.2.trans (Fintype.card_le_of_injective _ hi)

end D5.S3.Combinatorics.Graph.StarForming.PaddingConnectivity
