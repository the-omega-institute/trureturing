/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual broken-block connectivity and reciprocal interface assemblies. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodInterfaces
import D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity
import Mathlib.Data.Fin.VecNotation

/-! The reciprocal construction from EXACT_CUBIC_COMPOSITION at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The finite parent table is only a certificate for one fixed
fourteen-vertex block; arbitrary interface graphs are handled symbolically. -/
namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodConnectivity
open Cubic HeawoodInterfaces

private def root (z : Fin 14) : Fin 14 := if z = 0 then 1 else 0
private def parent : Fin 14 → Fin 14 → Fin 14 :=
  ![![1,1,9,11,11,8,9,6,1,1,2,1,5,5],
    ![0,0,10,10,7,12,7,0,5,6,0,4,4,6],
    ![0,11,0,10,7,12,7,0,1,6,0,4,4,6],
    ![0,11,10,0,7,12,7,0,1,6,0,4,4,6],
    ![0,9,10,10,0,13,7,0,1,6,0,3,2,6],
    ![0,11,10,10,7,0,7,0,1,6,0,4,4,6],
    ![0,11,10,10,7,12,0,0,1,2,0,4,4,3],
    ![0,9,10,10,12,12,9,0,1,2,0,3,2,3],
    ![0,11,10,10,7,12,7,0,0,6,0,4,4,6],
    ![0,11,10,10,7,12,7,0,1,0,0,4,4,6],
    ![0,11,12,11,7,12,7,0,1,6,0,4,4,6],
    ![0,9,10,10,7,12,7,0,5,6,0,0,4,6],
    ![0,11,10,10,7,13,7,0,1,6,0,4,0,6],
    ![0,11,10,10,7,12,7,0,1,6,0,4,4,0]]

private def rank : Fin 14 → Fin 14 → ℕ :=
  ![![0,0,2,2,2,2,2,3,1,1,3,1,3,3],
    ![0,0,2,2,2,4,2,1,5,3,1,3,3,3],
    ![0,4,0,2,2,4,2,1,5,3,1,3,3,3],
    ![0,4,2,0,2,4,2,1,5,3,1,3,3,3],
    ![0,4,2,2,0,4,2,1,5,3,1,3,3,3],
    ![0,4,2,2,2,0,2,1,5,3,1,3,3,3],
    ![0,4,2,2,2,4,0,1,5,3,1,3,3,3],
    ![0,4,2,2,4,4,4,0,5,3,1,3,3,3],
    ![0,4,2,2,2,4,2,1,0,3,1,3,3,3],
    ![0,4,2,2,2,4,2,1,5,0,1,3,3,3],
    ![0,4,4,4,2,4,2,1,5,3,0,3,3,3],
    ![0,4,2,2,2,4,2,1,5,3,1,0,3,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,0,3],
    ![0,4,2,2,2,4,2,1,5,3,1,3,3,0]]

private theorem root_survives (z : Fin 14) : root z ≠ z := by
  unfold root
  split <;> simp_all [eq_comm]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem parent_facts : ∀ z a : Fin 14, a ≠ z →
    parent z a ≠ z ∧ (a = root z ∨
      BrokenAdj a (parent z a) ∧ rank z (parent z a) < rank z a) := by
  unfold parent rank root BrokenAdj brokenNeighbors fanoNeighbors
  decide +kernel

/-- Deleting any one vertex leaves the actual broken Heawood block connected. -/
theorem broken_delete_preconnected (z : Fin 14) :
    (HeawoodPorts.graph.induce {a | a ≠ z}).Preconnected := by
  let p : {a : Fin 14 // a ≠ z} → {a : Fin 14 // a ≠ z} :=
    fun a => ⟨parent z a,(parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨root z,root_survives z⟩ p (fun a => rank z a)
  intro a ha
  have hn : a.val ≠ root z := fun he => ha (Subtype.ext he)
  have h := (parent_facts z a a.property).2
  rcases h with h | h
  · exact (hn h).elim
  · exact h

/-- The undeleted block is connected as well. -/
theorem broken_preconnected : HeawoodPorts.graph.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 14, ∃ z : Fin 14, a ≠ z ∧ b ≠ z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (HeawoodPorts.graph.induce {a | a ≠ z}) →g HeawoodPorts.graph :=
    ⟨fun a => a.val,fun h => h⟩
  exact ((broken_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

def reciprocal {I : Type} (Q : SimpleGraph I) : SimpleGraph (I × Fin 2) where
  Adj x y := Q.Adj x.1 y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨Q.adj_symm h.1,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Opposite port types preserve the displayed Heawood bipartition. -/
theorem reciprocal_bipartite {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) :
    (graph (reciprocal Q)).Colorable 2 := by
  apply HeawoodInterfaces.bipartite
  intro i p j q h
  exact h.2

private theorem deleted_fiber_reachable {I : Type} (Q : SimpleGraph I)
    (z : I × Fin 14)
    (a b : {x : I × Fin 14 // x ≠ z}) (he : a.val.1 = b.val.1) :
    ((graph (reciprocal Q)).induce {x | x ≠ z}).Reachable a b := by
  rcases a with ⟨⟨i,x⟩,ha⟩
  rcases b with ⟨⟨j,y⟩,hb⟩
  change i = j at he
  subst j
  by_cases hi : i = z.1
  · have hx : x ≠ z.2 := fun hx => ha (Prod.ext hi hx)
    have hy : y ≠ z.2 := fun hy => hb (Prod.ext hi hy)
    let f : (HeawoodPorts.graph.induce {a | a ≠ z.2}) →g
        ((graph (reciprocal Q)).induce {a | a ≠ z}) :=
      ⟨fun a => ⟨(i,a.val),fun he => a.property (congrArg Prod.snd he)⟩,
        fun h => Or.inl ⟨rfl,h⟩⟩
    exact ((broken_delete_preconnected z.2) ⟨x,hx⟩ ⟨y,hy⟩).map f
  · let f : HeawoodPorts.graph →g ((graph (reciprocal Q)).induce {a | a ≠ z}) :=
      ⟨fun a => ⟨(i,a),fun he => hi (congrArg Prod.fst he)⟩,
        fun h => Or.inl ⟨rfl,h⟩⟩
    exact (broken_preconnected x y).map f

/-- Every one-vertex deletion of the reciprocal assembly is connected whenever
its interaction graph is preconnected. No finiteness or regularity is needed. -/
theorem reciprocal_delete_preconnected {I : Type} (Q : SimpleGraph I)
    (hQ : Q.Preconnected) (z : I × Fin 14) :
    ((graph (reciprocal Q)).induce {x | x ≠ z}).Preconnected := by
  apply FiberConnectivity.preconnected_of_fibers _ Q (fun x => x.val.1) hQ
  · exact deleted_fiber_reachable Q z
  · intro i j hij
    have hne := Q.ne_of_adj hij
    have h0 : (0 : Fin 14) ≠ 8 := by decide
    have hsur := FiberConnectivity.surviving_pair (i,0) (j,8) (i,8) (j,0) z
      (fun h => h0 (congrArg Prod.snd h))
      (fun h => hne (congrArg Prod.fst h))
      (fun h => hne (congrArg Prod.fst h).symm)
      (fun h => h0 (congrArg Prod.snd h).symm)
    rcases hsur with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · refine ⟨⟨(i,0),ha⟩,⟨(j,8),hb⟩,rfl,rfl,?_⟩
      exact Or.inr ⟨0,1,rfl,rfl,hij,(by decide : (0 : Fin 2) ≠ 1)⟩
    · refine ⟨⟨(i,8),ha⟩,⟨(j,0),hb⟩,rfl,rfl,?_⟩
      exact Or.inr ⟨1,0,rfl,rfl,hij,(by decide : (1 : Fin 2) ≠ 0)⟩

/-- The reciprocal assembly itself is preconnected. -/
theorem reciprocal_preconnected {I : Type} (Q : SimpleGraph I)
    (hQ : Q.Preconnected) : (graph (reciprocal Q)).Preconnected := by
  intro a b
  have hz : ∀ x y : Fin 14, ∃ t : Fin 14, x ≠ t ∧ y ≠ t := by decide +kernel
  obtain ⟨t,ha,hb⟩ := hz a.2 b.2
  let z := (a.1,t)
  have hna : a ≠ z := fun he => ha (congrArg Prod.snd he)
  have hnb : b ≠ z := fun he => hb (congrArg Prod.snd he)
  let f : ((graph (reciprocal Q)).induce {x | x ≠ z}) →g graph (reciprocal Q) :=
    ⟨fun x => x.val,fun h => h⟩
  exact ((reciprocal_delete_preconnected Q hQ z) ⟨a,hna⟩ ⟨b,hnb⟩).map f

/-- Actual connectedness before and after every vertex deletion, and order at
least three: the complete two-connectivity assertion for reciprocal assemblies. -/
theorem reciprocal_two_connected {I : Type} [Fintype I] [Nonempty I]
    (Q : SimpleGraph I) (hQ : Q.Preconnected) :
    (graph (reciprocal Q)).Connected ∧
      (∀ z : I × Fin 14, ((graph (reciprocal Q)).induce {x | x ≠ z}).Connected) ∧
      3 ≤ Fintype.card (I × Fin 14) := by
  refine ⟨⟨reciprocal_preconnected Q hQ⟩,?_,?_⟩
  · intro z
    have hz : ∃ a : I × Fin 14, a ≠ z := by
      obtain ⟨i⟩ := ‹Nonempty I›
      by_cases h : (i,0) = z
      · exact ⟨(i,1),by intro he; have := congrArg Prod.snd (h.trans he.symm); norm_num at this⟩
      · exact ⟨(i,0),h⟩
    obtain ⟨a,ha⟩ := hz
    letI : Nonempty {x : I × Fin 14 // x ≠ z} := ⟨⟨a,ha⟩⟩
    exact { preconnected := reciprocal_delete_preconnected Q hQ z, nonempty := ⟨⟨a,ha⟩⟩ }
  · have hi := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

/-- Reciprocal interactions are precisely the original loopless graph. -/
theorem reciprocal_interaction {I : Type} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (i j : I) :
    interaction (reciprocal Q) i j ↔ Q.Adj i j := by
  constructor
  · rintro ⟨p,q,h,_⟩; exact h
  · intro h; exact ⟨0,1,h,(by decide : (0 : Fin 2) ≠ 1)⟩

/-- The actual loop-aware independence maximum reduces to ordinary alpha. -/
theorem reciprocal_alpha0 {I : Type} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) : alpha0 (reciprocal Q) = Q.indepNum := by
  classical
  have he (A : Finset I) : IndependentBlocks (reciprocal Q) A ↔
      Q.IsIndepSet (A : Set I) := by
    constructor
    · intro h a ha b hb _ hab
      exact h a ha b hb ((reciprocal_interaction Q a b).mpr hab)
    · intro h a ha b hb hab
      have hh := (reciprocal_interaction Q a b).mp hab
      exact h ha hb (Q.ne_of_adj hh) hh
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    exact ((he A).mp (Finset.mem_filter.mp hA).2).card_le_indepNum
  · obtain ⟨A,hA⟩ := Q.maximumIndepSet_exists
    rw [← Q.maximumIndepSet_card_eq_indepNum A hA]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,(he A).mpr hA.isIndepSet⟩)

/-- Exact attained graph parameters for every finite reciprocal interface. -/
theorem reciprocal_sf_beta {I : Type} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) :
    StarFormingDissociationRefutation.SF (graph (reciprocal Q)) 2 = 8*Fintype.card I ∧
    StarFormingDissociationRefutation.beta (graph (reciprocal Q)) 2 =
      7*Fintype.card I + Q.indepNum := by
  constructor
  · exact sf_graph _
  · rw [beta_graph,reciprocal_alpha0]

end D5.S3.Combinatorics.Graph.StarForming.HeawoodConnectivity
