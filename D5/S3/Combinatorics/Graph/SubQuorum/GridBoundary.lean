/- GID: D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/GridBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual grid degrees and selected boundary deficiency in forming bounds. -/

import D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
import D5.S3.Combinatorics.Graph.StarForming.DissociationDeficiency
import Mathlib.Combinatorics.SimpleGraph.Prod

/-! The rectangular-grid boundary argument from REGULAR_STAR_FORMING_BOUND,
received at subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Selected degree deficiency is distinct from perimeter length.
No sub-quorum coloring upper bound is inferred from this forming bound. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
open GridDissociation StarFormingDissociationRefutation
open StarForming DegreeCapacity
open scoped BigOperators

private def pathNeighbors {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  (if h : (0 : ℕ) < i.val then {⟨i.val-1,by omega⟩} else ∅) ∪
    (if h : i.val+1<n then {⟨i.val+1,h⟩} else ∅)

private theorem mem_pathNeighbors {n : ℕ} (i j : Fin n) :
    j ∈ pathNeighbors i ↔ (SimpleGraph.pathGraph n).Adj i j := by
  unfold pathNeighbors
  split_ifs <;> (try simp_all [SimpleGraph.pathGraph_adj,Fin.ext_iff]) <;> omega

private theorem path_degree {n : ℕ} (i : Fin n) :
    (SimpleGraph.pathGraph n).degree i=
      (if i.val=0 then 0 else 1)+(if i.val+1=n then 0 else 1) := by
  have he : (SimpleGraph.pathGraph n).neighborFinset i=pathNeighbors i := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset,mem_pathNeighbors]
  unfold SimpleGraph.degree
  rw [he]
  unfold pathNeighbors
  split_ifs <;> (try simp_all [Fin.ext_iff]) <;> (try split_ifs) <;> omega

private theorem grid_box (m n : ℕ) :
    graph m n=(SimpleGraph.pathGraph m) □ (SimpleGraph.pathGraph n) := by
  ext x y
  simp only [graph,SimpleGraph.boxProd_adj]
  tauto

private theorem degree_bridge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DegreeCapacity.degree G v=G.degree v := by
  unfold SimpleGraph.degree DegreeCapacity.degree
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The four possible missing grid directions are counted separately at corners. -/
theorem degree_formula {m n : ℕ} (v : Fin m × Fin n) :
    DegreeCapacity.degree (graph m n) v=
      (if v.1.val=0 then 0 else 1)+(if v.1.val+1=m then 0 else 1)+
      (if v.2.val=0 then 0 else 1)+(if v.2.val+1=n then 0 else 1) := by
  have he : (graph m n).degree v=
      ((SimpleGraph.pathGraph m) □ (SimpleGraph.pathGraph n)).degree v := by
    unfold SimpleGraph.degree
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    simp only [graph,SimpleGraph.boxProd_adj]
    tauto
  rw [degree_bridge,he,SimpleGraph.degree_boxProd,path_degree,path_degree]
  omega

/-- Every actual grid vertex has at most four neighbors, including degenerate grids. -/
theorem degree_le_four {m n : ℕ} (v : Fin m × Fin n) :
    DegreeCapacity.degree (graph m n) v≤4 := by
  rw [degree_formula]
  split_ifs <;> omega

private theorem endpoint_count (n : ℕ) (hn : 0 < n) :
    (∑ i : Fin n, ((if i.val=0 then (1 : ℕ) else 0)+
      (if i.val+1=n then 1 else 0)))=2 := by
  rw [Finset.sum_add_distrib]
  have h0 : (∑ i : Fin n, if i.val=0 then (1 : ℕ) else 0)=1 := by
    have he (i : Fin n) : i.val=0 ↔ i=⟨0,hn⟩ := by simp [Fin.ext_iff]
    simp_rw [he]
    simp
  have h1 : (∑ i : Fin n, if i.val+1=n then (1 : ℕ) else 0)=1 := by
    have he (i : Fin n) : i.val+1=n ↔ i=⟨n-1,by omega⟩ := by
      simp only [Fin.ext_iff,Fin.val_mk]
      omega
    simp_rw [he]
    simp
  omega

/-- The entire actual boundary deficiency is 2m+2n for positive dimensions. -/
theorem total_deficiency {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    DissociationDeficiency.deficiency (graph m n) 4 Finset.univ=2*m+2*n := by
  have hv (v : Fin m × Fin n) : 4-DegreeCapacity.degree (graph m n) v=
      ((if v.1.val=0 then 1 else 0)+(if v.1.val+1=m then 1 else 0))+
      ((if v.2.val=0 then 1 else 0)+(if v.2.val+1=n then 1 else 0)) := by
    rw [degree_formula]
    split_ifs <;> omega
  unfold DissociationDeficiency.deficiency
  simp_rw [hv]
  rw [Fintype.sum_prod_type]
  have hr (i : Fin m) :
      (∑ j : Fin n, (((if i.val=0 then 1 else 0)+(if i.val+1=m then 1 else 0))+
        ((if j.val=0 then 1 else 0)+(if j.val+1=n then 1 else 0))))=
      n*((if i.val=0 then 1 else 0)+(if i.val+1=m then 1 else 0))+2 := by
    rw [Finset.sum_add_distrib,endpoint_count n hn]
    simp
  simp_rw [hr]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,endpoint_count m hm]
  simp [Nat.mul_comm, Nat.add_comm]

/-- The source's selected deficiency is bounded by the actual perimeter deficit. -/
theorem selected_deficiency_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (S : Finset (Fin m × Fin n)) :
    DissociationDeficiency.deficiency (graph m n) 4 S≤2*m+2*n := by
  rw [← total_deficiency hm hn]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- Every minimal forming selection satisfies the exact selected-boundary bound. -/
theorem forming_bound {m n : ℕ} (S : Finset (Fin m × Fin n))
    (hS : IsMinimalStarForming (graph m n) 2 S) :
    7*S.card+(isolates (graph m n) S).card≤4*(m*n)+
      DissociationDeficiency.deficiency (graph m n) 4 S := by
  have hc := degree_capacity (graph m n) S hS 4 degree_le_four
  have hd : DissociationDeficiency.deficiency (graph m n) 4 S+
      (∑ v ∈ S,DegreeCapacity.degree (graph m n) v)=4*S.card := by
    rw [DissociationDeficiency.deficiency,← Finset.sum_add_distrib]
    calc
      _ = ∑ _v ∈ S,4 := Finset.sum_congr rfl
        (fun v _ => Nat.sub_add_cancel (degree_le_four v))
      _ = _ := by simp [Nat.mul_comm]
  have ht : (Finset.univ \ S).card+S.card=m*n := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  omega

/-- The stated rectangular-grid star-forming estimate follows for every minimal set. -/
theorem forming_perimeter_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (S : Finset (Fin m × Fin n)) (hS : IsMinimalStarForming (graph m n) 2 S) :
    7*S.card+(isolates (graph m n) S).card≤4*(m*n)+2*m+2*n :=
  (forming_bound S hS).trans (by have h := selected_deficiency_bound hm hn S; omega)

end D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
