/- GID: D5/S3/Combinatorics/Graph/StarForming/CycleParameters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CycleParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual all-order cycle dissociation witnesses and exact star-forming maximum. -/

import D5.S3.Combinatorics.Graph.StarForming.Comparison
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! The cycle equality in SUBCUBIC_STAR_FORMING_GAPS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
The upper bound reuses the stronger current degree-capacity theorem;
the actual 110-word witness is counted and checked for every length. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CycleParameters
open StarFormingDissociationRefutation

def selection (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val%3≠2 ∧ v.val+1<n)

private theorem cycle_adj_nat {n : ℕ} (hn : 2≤n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔
      j.val=i.val+1 ∨ i.val=j.val+1 ∨ (i.val=0 ∧ j.val+1=n) ∨ (j.val=0 ∧ i.val+1=n) := by
  letI : NeZero n := ⟨by omega⟩
  rw [SimpleGraph.cycleGraph_adj']
  by_cases hij : i ≤ j
  · by_cases heq : i=j
    · subst j
      simp only [sub_self,Fin.val_zero]
      have hi := i.isLt
      omega
    · have hlt : i < j := lt_of_le_of_ne hij heq
      rw [Fin.sub_val_of_le hij,Fin.coe_sub_iff_lt.mpr hlt]
      have hi := i.isLt
      have hj := j.isLt
      change i.val < j.val at hlt
      omega
  · have hlt : j < i := lt_of_not_ge hij
    rw [Fin.sub_val_of_le hlt.le,Fin.coe_sub_iff_lt.mpr hlt]
    have hi := i.isLt
    have hj := j.isLt
    change j.val < i.val at hlt
    omega

/-- The actual cyclic 110-word, with its final vertex omitted, dissociates. -/
theorem selection_independent (n : ℕ) (hn : 3≤n) :
    IsKIndependent (SimpleGraph.cycleGraph n) 2 (selection n) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  have hc' := (Finset.mem_filter.mp hc).2
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  rw [cycle_adj_nat (by omega)] at hca hcb
  apply Fin.ext
  omega

/-- Count the selected vertices by their exact two-per-three indexing,
including every residue class of the total length. -/
theorem selection_card (n : ℕ) : (selection n).card=2*n/3 := by
  have hf : ∀ j : Fin (2*n/3), 3*(j.val/2)+j.val%2<n := by
    intro j
    have := j.isLt
    omega
  have hc : (Finset.univ : Finset (Fin (2*n/3))).card=(selection n).card := by
    apply Finset.card_bij (fun j _ => (⟨3*(j.val/2)+j.val%2,hf j⟩ : Fin n))
    · intro j hj
      simp only [selection,Finset.mem_filter,Finset.mem_univ,true_and]
      change (3*(j.val/2)+j.val%2)%3≠2 ∧ 3*(j.val/2)+j.val%2+1<n
      have := j.isLt
      omega
    · intro i hi j hj he
      apply Fin.ext
      have hv := congrArg Fin.val he
      change 3*(i.val/2)+i.val%2=3*(j.val/2)+j.val%2 at hv
      omega
    · intro i hi
      have hm := (Finset.mem_filter.mp hi).2
      refine ⟨⟨2*(i.val/3)+i.val%3,by omega⟩,by simp,?_⟩
      apply Fin.ext
      dsimp
      omega
  simpa using hc.symm

/-- Every genuine cycle, n at least three, has both actual finite maxima
floor(2n/3). No bipartite or parity premise is imposed. -/
theorem parameters (n : ℕ) (hn : 3≤n) :
    beta (SimpleGraph.cycleGraph n) 2=2*n/3 ∧ SF (SimpleGraph.cycleGraph n) 2=2*n/3 := by
  classical
  have hreg : ∀ v, DegreeCapacity.degree (SimpleGraph.cycleGraph n) v=2 := by
    intro v
    obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
    have hh := SimpleGraph.cycleGraph_degree_three_le (v := v)
    unfold DegreeCapacity.degree
    rw [← hh]
    unfold SimpleGraph.degree
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]
  have hu := DegreeCapacity.sf_regular_bound (SimpleGraph.cycleGraph n) 2 (by omega) hreg
  simp only [Fintype.card_fin] at hu
  norm_num at hu
  have hl : 2*n/3≤beta (SimpleGraph.cycleGraph n) 2 := by
    rw [← selection_card]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,selection_independent n hn⟩)
  have hb := beta_le_sf (SimpleGraph.cycleGraph n)
  exact ⟨by omega,by omega⟩

end D5.S3.Combinatorics.Graph.StarForming.CycleParameters
