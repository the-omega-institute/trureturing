import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

/-! Enumerating a finite simple graph by its prescribed degrees, removing
one vertex and subtracting its incident edges at each step. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeRows

open Finset

universe u
variable {V : Type u} [DecidableEq V]

/-- Choose the first row of the remaining adjacency matrix, then reduce the
degrees of its selected neighbors. -/
def degreeEdges : List V → (V → ℕ) → Finset (Finset (V × V))
  | [], _ => {∅}
  | v :: vs, d =>
      ((vs.toFinset.powersetCard (d v)).filter (fun N => ∀ u ∈ N, 0 < d u)).biUnion
        fun N => (degreeEdges vs (fun u => d u - if u ∈ N then 1 else 0)).image
          fun E => E ∪ N.image (fun u => (v,u))

private theorem support_degreeEdges (vs : List V) (d : V → ℕ)
    {E : Finset (V × V)} (h : E ∈ degreeEdges vs d) :
    ∀ p ∈ E, p.1 ∈ vs.toFinset ∧ p.2 ∈ vs.toFinset := by
  induction vs generalizing E d with
  | nil =>
      have he : E = ∅ := mem_singleton.mp h
      subst E
      simp
  | cons v vs ih =>
      simp only [degreeEdges] at h
      obtain ⟨N, hN, hE⟩ := mem_biUnion.mp h
      obtain ⟨F, hF, rfl⟩ := mem_image.mp hE
      have hn := (mem_powersetCard.mp (mem_filter.mp hN).1).1
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨ha,hb⟩ := ih _ hF p hp
        simpa only [List.toFinset_cons, mem_insert] using
          And.intro (Or.inr ha) (Or.inr hb)
      · obtain ⟨u,hu,rfl⟩ := mem_image.mp hp
        simp only [List.toFinset_cons, mem_insert, true_or, true_and]
        exact Or.inr (hn hu)

/-- Every induced simple graph with the given degree vector is represented by
the row-by-row enumeration. The two orientations of an edge are identified
by this statement. -/
theorem complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hvs : vs.Nodup) (d : V → ℕ)
    (hd : ∀ v ∈ vs.toFinset, d v = (vs.toFinset.filter (G.Adj v)).card) :
    ∃ E ∈ degreeEdges vs d, ∀ a ∈ vs.toFinset, ∀ b ∈ vs.toFinset,
      G.Adj a b ↔ (a,b) ∈ E ∨ (b,a) ∈ E := by
  induction vs generalizing d with
  | nil => exact ⟨∅, by simp [degreeEdges], by simp⟩
  | cons v vs ih =>
      have hv : v ∉ vs.toFinset := by
        simpa only [List.mem_toFinset] using (List.nodup_cons.mp hvs).1
      have htail : vs.Nodup := (List.nodup_cons.mp hvs).2
      let A := vs.toFinset
      let N := A.filter (G.Adj v)
      have hN : N.card = d v := by
        rw [hd v (by simp)]
        simp [N,A,List.toFinset_cons, filter_insert, G.irrefl]
      have hpos : ∀ u ∈ N, 0 < d u := by
        intro u hu
        have hmem : u ∈ A := (mem_filter.mp hu).1
        have ha : G.Adj u v := (mem_filter.mp hu).2.symm
        rw [hd u (by simp [A] at hmem ⊢; exact Or.inr hmem)]
        exact card_pos.mpr ⟨v, mem_filter.mpr ⟨by simp, ha⟩⟩
      let q (u : V) := d u - if u ∈ N then 1 else 0
      have hq : ∀ u ∈ A, q u = (A.filter (G.Adj u)).card := by
        intro u hu
        have hdeg := hd u (by simp only [List.toFinset_cons, mem_insert]; exact Or.inr hu)
        by_cases ha : G.Adj u v
        · have hn : u ∈ N := mem_filter.mpr ⟨hu, ha.symm⟩
          rw [List.toFinset_cons, filter_insert, if_pos ha,
            card_insert_of_notMem (fun he => hv (mem_filter.mp he).1)] at hdeg
          simp only [q, if_pos hn, hdeg, A]
          omega
        · have hn : u ∉ N := fun he => ha (mem_filter.mp he).2.symm
          rw [List.toFinset_cons, filter_insert, if_neg ha] at hdeg
          simp only [q, if_neg hn, Nat.sub_zero, hdeg, A]
      obtain ⟨F,hF,hcover⟩ := ih htail q hq
      let E := F ∪ N.image (fun u => (v,u))
      have hE : E ∈ degreeEdges (v::vs) d := by
        apply mem_biUnion.mpr
        refine ⟨N, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨filter_subset _ _, hN⟩,hpos⟩, ?_⟩
        exact mem_image.mpr ⟨F,hF,rfl⟩
      have hnotL (u : V) : (v,u) ∉ F := fun he => hv (support_degreeEdges vs q hF _ he).1
      have hnotR (u : V) : (u,v) ∉ F := fun he => hv (support_degreeEdges vs q hF _ he).2
      have hNnot : v ∉ N := fun he => hv (mem_filter.mp he).1
      refine ⟨E,hE,?_⟩
      intro a ha b hb
      simp only [List.toFinset_cons, mem_insert] at ha hb
      rcases ha with ha | ha
      · subst a
        rcases hb with hb | hb
        · subst b
          simp [E,hnotL,hNnot,G.irrefl]
        · have hbne : b ≠ v := fun he => hv (he ▸ hb)
          simp [E,hnotL,hnotR,hbne,Ne.symm hbne,N,A,List.mem_toFinset.mp hb]
      · rcases hb with hb | hb
        · subst b
          have hane : a ≠ v := fun he => hv (he ▸ ha)
          simp [E,hnotL,hnotR,hane,Ne.symm hane,N,A,List.mem_toFinset.mp ha,G.adj_comm]
        · have hane : a ≠ v := fun he => hv (he ▸ ha)
          have hbne : b ≠ v := fun he => hv (he ▸ hb)
          simpa [E,hane,hbne,Ne.symm hane,Ne.symm hbne] using hcover a ha b hb

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeRows
