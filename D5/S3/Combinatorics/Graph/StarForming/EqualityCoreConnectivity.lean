/- GID: D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual local paths and all-size cyclic two-connectivity. -/

import D5.S3.Combinatorics.Graph.StarForming.EqualityCore
import D5.S3.Combinatorics.Graph.StarForming.CyclicConnectivity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The local paths and cyclic fiber argument for the received graph,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
Every edge in the local parent certificate is checked in the actual graph.
The arbitrary transitive-permutation argument covers all positive lengths. -/
namespace D5.S3.Combinatorics.Graph.StarForming.EqualityCoreConnectivity
private def localGraph : SimpleGraph (Fin 20) where
  Adj := EqualityCore.internal
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by decide +kernel⟩

private instance : DecidableRel localGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
open EqualityCore

private def root (z : Fin 20) : Fin 20 := if z=0 then 1 else 0
private def parent : Fin 20 → Fin 20 → Fin 20 :=
  ![![1,1,1,2,3,4,18,1,2,3,4,19,13,7,8,9,10,11,8,7],
    ![0,0,8,2,10,4,0,13,18,15,18,19,6,12,13,14,10,16,6,7],
    ![0,0,0,9,10,11,0,1,18,19,18,19,6,7,13,14,10,11,6,7],
    ![0,0,1,0,10,11,0,1,2,19,18,19,6,7,8,14,10,11,6,7],
    ![0,0,1,2,0,11,0,1,2,3,18,19,6,7,8,9,10,11,6,7],
    ![0,0,1,2,3,0,0,1,2,3,18,19,6,7,8,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,3,4,19,13,7,8,9,10,11,8,7],
    ![0,0,1,2,3,4,0,0,2,3,18,5,6,12,8,9,10,16,6,9],
    ![0,0,1,2,3,4,0,1,0,3,18,19,6,7,13,9,10,11,6,7],
    ![0,0,1,2,3,4,0,1,2,0,18,19,6,7,8,14,10,11,6,7],
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
private def rank : Fin 20 → Fin 20 → ℕ :=
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

private theorem parent_facts : ∀ z a : Fin 20, a≠z → parent z a≠z ∧
    (a=root z ∨ localGraph.Adj a (parent z a) ∧ rank z (parent z a)<rank z a) := by
  decide +kernel

private theorem root_survives (z : Fin 20) : root z≠z := by
  unfold root
  split <;> simp_all [eq_comm]

private theorem local_delete_preconnected (z : Fin 20) :
    (localGraph.induce {a | a≠z}).Preconnected := by
  let p : {a : Fin 20 // a≠z} → {a : Fin 20 // a≠z} :=
    fun a => ⟨parent z a,(parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨root z,root_survives z⟩ p
    (fun a => rank z a)
  intro a ha
  rcases (parent_facts z a a.property).2 with h | h
  · exact (ha (Subtype.ext h)).elim
  · exact h

private theorem local_preconnected : localGraph.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 20, ∃ z : Fin 20, a≠z ∧ b≠z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (localGraph.induce {a | a≠z}) →g localGraph := ⟨fun a => a.val,fun h => h⟩
  exact ((local_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Actual cyclic bridges and local paths survive every vertex deletion. -/
theorem two_connected [Nonempty I] (e : Equiv.Perm I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) :
    (graph e).Connected ∧
    (∀ z : I × Fin 20, ((graph e).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (I × Fin 20) := by
  have hint : ∀ i a b, localGraph.Adj a b → (graph e).Adj (i,a) (i,b) :=
    fun _ _ _ h => Or.inl ⟨rfl,h⟩
  have hb : ∀ i, (graph e).Adj (i,5) (e i,0) := fun _ => Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)
  refine ⟨⟨CyclicConnectivity.preconnected _ _ e horbit 5 0 local_preconnected hint hb⟩,?_,?_⟩
  · intro z
    exact
      { preconnected := CyclicConnectivity.delete_preconnected _ _ e horbit 5 0
          (by decide) local_preconnected local_delete_preconnected hint hb z
        nonempty := ⟨⟨(z.1,root z.2),fun h => root_survives z.2 (congrArg Prod.snd h)⟩⟩ }
  · have hi := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

/-- Every positive cyclic size, with the singleton case explicitly retained. -/
theorem cyclic_two_connected (r : ℕ) (hr : 0<r) :
    (graph (finRotate r)).Connected ∧
    (∀ z : Fin r × Fin 20, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (Fin r × Fin 20) := by
  letI : NeZero r := ⟨hr.ne'⟩
  apply two_connected
  intro i j
  refine ⟨(j-i).val,?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  simp

end D5.S3.Combinatorics.Graph.StarForming.EqualityCoreConnectivity
