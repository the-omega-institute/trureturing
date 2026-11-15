/- GID: D5/S3/Combinatorics/Graph/StarForming/H0Geometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/H0Geometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual local paths and all-size cyclic two-connectivity. -/

import D5.S3.Combinatorics.Graph.StarForming.Semantics
import D5.S3.Combinatorics.Graph.StarForming.CyclicConnectivity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The local paths and cyclic fiber argument for the received graph,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
Every edge in the local parent certificate is checked in the actual graph.
The arbitrary transitive-permutation argument covers all positive lengths. -/
namespace D5.S3.Combinatorics.Graph.StarForming.H0Geometry
def graph {I : Type} (e : Equiv.Perm I) : SimpleGraph (I × Fin 10) :=
  Amplification.family (fun i j => e i=j)

instance {I : Type} [DecidableEq I] (e : Equiv.Perm I) : DecidableRel (graph e).Adj :=
  fun a b => inferInstanceAs (Decidable ((a.1=b.1 ∧ Amplification.base.Adj a.2 b.2) ∨ (a.2=5 ∧ b.2=0 ∧ e a.1=b.1) ∨ (a.2=0 ∧ b.2=5 ∧ e b.1=a.1)))

private def root (z : Fin 10) : Fin 10 := if z=0 then 1 else 0
private def parent : Fin 10 → Fin 10 → Fin 10 :=
  ![![1,1,8,6,5,1,1,4,1,4],
    ![0,0,9,6,5,0,0,4,4,0],
    ![0,5,0,6,5,0,0,4,1,0],
    ![0,5,9,0,5,0,0,4,1,0],
    ![0,5,9,6,0,0,0,3,1,0],
    ![0,6,9,6,9,0,0,3,1,0],
    ![0,5,9,9,5,0,0,4,1,0],
    ![0,5,9,6,5,0,0,0,1,0],
    ![0,5,9,6,5,0,0,4,0,0],
    ![0,5,8,6,5,0,0,4,1,0]]
private def rank : Fin 10 → Fin 10 → ℕ :=
  ![![0,0,2,2,2,1,1,3,1,3],
    ![0,0,2,2,2,1,1,3,3,1],
    ![0,2,0,2,2,1,1,3,3,1],
    ![0,2,2,0,2,1,1,3,3,1],
    ![0,2,2,2,0,1,1,3,3,1],
    ![0,2,2,2,2,0,1,3,3,1],
    ![0,2,2,2,2,1,0,3,3,1],
    ![0,2,2,2,2,1,1,0,3,1],
    ![0,2,2,2,2,1,1,3,0,1],
    ![0,2,4,2,2,1,1,3,3,0]]

private theorem parent_facts : ∀ z a : Fin 10, a≠z → parent z a≠z ∧
    (a=root z ∨ Amplification.base.Adj a (parent z a) ∧ rank z (parent z a)<rank z a) := by
  decide +kernel

private theorem root_survives (z : Fin 10) : root z≠z := by
  unfold root
  split <;> simp_all [eq_comm]

private theorem local_delete_preconnected (z : Fin 10) :
    (Amplification.base.induce {a | a≠z}).Preconnected := by
  let p : {a : Fin 10 // a≠z} → {a : Fin 10 // a≠z} :=
    fun a => ⟨parent z a,(parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨root z,root_survives z⟩ p
    (fun a => rank z a)
  intro a ha
  rcases (parent_facts z a a.property).2 with h | h
  · exact (ha (Subtype.ext h)).elim
  · exact h

private theorem local_preconnected : Amplification.base.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 10, ∃ z : Fin 10, a≠z ∧ b≠z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (Amplification.base.induce {a | a≠z}) →g Amplification.base := ⟨fun a => a.val,fun h => h⟩
  exact ((local_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Actual cyclic bridges and local paths survive every vertex deletion. -/
theorem two_connected [Nonempty I] (e : Equiv.Perm I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) :
    (graph e).Connected ∧
    (∀ z : I × Fin 10, ((graph e).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (I × Fin 10) := by
  have hint : ∀ i a b, Amplification.base.Adj a b → (graph e).Adj (i,a) (i,b) :=
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
    (∀ z : Fin r × Fin 10, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (Fin r × Fin 10) := by
  letI : NeZero r := ⟨hr.ne'⟩
  apply two_connected
  intro i j
  refine ⟨(j-i).val,?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  simp

end D5.S3.Combinatorics.Graph.StarForming.H0Geometry
