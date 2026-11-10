/- GID: D5/S3/Combinatorics/Graph/StarForming/H0Parameters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/H0Parameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual H0 cyclic degrees and edge counts with the exact nontrivial-cycle domain. -/

import D5.S3.Combinatorics.Graph.StarForming.H0Geometry
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! EXACT_STAR_FORMING_COMPOSITION, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69. The unchanged original H0
is used directly. A singleton restores an existing edge and is therefore
excluded from the seventeen-edges-per-cell formula, as in the source. -/
namespace D5.S3.Combinatorics.Graph.StarForming.H0Parameters
open StarFormingDissociationRefutation H0Geometry
open scoped BigOperators

private def baseNeighbors : Fin 10 → List (Fin 10) :=
  ![[5,6,9],[5,6,8],[8,9],[6,7,8,9],[5,7,8,9],
    [0,1,4],[0,1,3],[3,4],[1,2,3,4],[0,2,3,4]]
private theorem base_neighbors : ∀ v w : Fin 10,
    Amplification.base.Adj v w ↔ w∈baseNeighbors v := by decide +kernel
private theorem base_nodup : ∀ v : Fin 10, (baseNeighbors v).Nodup := by decide +kernel

variable {I : Type} [Fintype I] [DecidableEq I]

def neighbors (e : Equiv.Perm I) (v : I × Fin 10) : List (I × Fin 10) :=
  (baseNeighbors v.2).map (fun w => (v.1,w)) ++
    (if v.2=0 then [(e.symm v.1,5)] else if v.2=5 then [(e v.1,0)] else [])

private theorem adjacency_neighbors (e : Equiv.Perm I) (v w : I × Fin 10) :
    (graph e).Adj v w ↔ w∈neighbors e v := by
  rcases v with ⟨i,v⟩
  rcases w with ⟨j,w⟩
  by_cases h0 : v=0 <;> by_cases h5 : v=5 <;>
    simp [graph,Amplification.family,neighbors,← base_neighbors,h0,h5,
      Prod.mk.injEq,and_comm,and_left_comm,and_assoc,Equiv.eq_symm_apply,eq_comm]

private theorem neighbor_properties (e : Equiv.Perm I) (hf : ∀ i,e i≠i) (v : I × Fin 10) :
    (neighbors e v).Nodup ∧ (neighbors e v).length=
      if v.2=2 ∨ v.2=7 then 2 else if v.2=1 ∨ v.2=6 then 3 else 4 := by
  have hp (i : I) : e.symm i≠i := by
    intro h
    have he := congrArg e h
    rw [Equiv.apply_symm_apply] at he
    exact hf i he.symm
  rcases v with ⟨i,v⟩
  have hi : Function.Injective (fun w : Fin 10 => (i,w)) :=
    fun _ _ h => congrArg Prod.snd h
  have hn := (base_nodup v).map hi
  fin_cases v <;> simp_all [neighbors,baseNeighbors,Prod.mk.injEq,eq_comm]

/-- Every actual vertex has its exact degree, with both extrema attained
in every nonempty assembly. -/
theorem degrees (e : Equiv.Perm I) (hf : ∀ i,e i≠i) (v : I × Fin 10) :
    DegreeCapacity.degree (graph e) v=
      if v.2=2 ∨ v.2=7 then 2 else if v.2=1 ∨ v.2=6 then 3 else 4 := by
  classical
  have he : Finset.univ.filter ((graph e).Adj v)=(neighbors e v).toFinset := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    exact adjacency_neighbors e v w
  unfold DegreeCapacity.degree
  rw [he,List.toFinset_card_of_nodup (neighbor_properties e hf v).1,
    (neighbor_properties e hf v).2]

/-- The actual disjoint internal edges and cyclic port edges total seventeen
per block, even at two blocks. -/
theorem edge_count (e : Equiv.Perm I) (hf : ∀ i,e i≠i) :
    (graph e).edgeFinset.card=17*Fintype.card I := by
  classical
  have he := (graph e).sum_degrees_eq_twice_card_edges
  have hd (x : I × Fin 10) : (graph e).degree x=DegreeCapacity.degree (graph e) x := by
    unfold SimpleGraph.degree DegreeCapacity.degree
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [hd] at he
  rw [Fintype.sum_prod_type] at he
  have hlocal (i : I) : ∑ v : Fin 10, DegreeCapacity.degree (graph e) (i,v)=34 := by
    simp only [degrees e hf]
    change (∑ v : Fin 10, if v=2 ∨ v=7 then 2 else if v=1 ∨ v=6 then 3 else 4)=34
    decide +kernel
  simp_rw [hlocal] at he
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at he
  omega

/-- Actual H0 cyclic counts and exact finite maxima, at every r at least two. -/
theorem cyclic_parameters (r : ℕ) (hr : 2≤r) :
    let G := graph (finRotate r)
    Fintype.card (Fin r × Fin 10)=10*r ∧ G.edgeFinset.card=17*r ∧
    beta G 2=5*r ∧ SF G 2=6*r ∧ SF G 2-beta G 2=r ∧
    (∀ v, 2≤DegreeCapacity.degree G v ∧ DegreeCapacity.degree G v≤4) ∧
    (∃ v, DegreeCapacity.degree G v=2) ∧ (∃ v, DegreeCapacity.degree G v=4) := by
  letI : NeZero r := ⟨by omega⟩
  have hf : ∀ i : Fin r, finRotate r i≠i := by
    intro i h
    have hv := congrArg Fin.val h
    have hh := i.isLt
    obtain ⟨n,hn⟩ : ∃ n,r=n+1 := ⟨r-1,by omega⟩
    subst r
    rw [coe_finRotate] at hv
    split_ifs at hv <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> omega
  have hb : beta (graph (finRotate r)) 2=5*Fintype.card (Fin r) := by
    convert beta_family (fun i j : Fin r => finRotate r i=j) using 1 <;>
      congr 1 <;> exact Subsingleton.elim _ _
  have hs : SF (graph (finRotate r)) 2=6*Fintype.card (Fin r) := by
    convert sf_family (fun i j : Fin r => finRotate r i=j) using 1 <;>
      congr 1 <;> exact Subsingleton.elim _ _
  have hm := edge_count (finRotate r) hf
  simp only [Fintype.card_fin] at hb hs hm
  refine ⟨by simp [Nat.mul_comm],hm,hb,hs,by omega,?_,?_,?_⟩
  · intro v
    rw [degrees _ hf]
    split_ifs <;> omega
  · exact ⟨(0,2),by simp [degrees _ hf]⟩
  · exact ⟨(0,0),by simp [degrees _ hf]⟩

end D5.S3.Combinatorics.Graph.StarForming.H0Parameters
