/- GID: D5/S3/Combinatorics/Graph/StarForming/ClauseSizes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClauseSizes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The actual subcubic clause model has at most five-n variables and nine-n constraints. -/

import D5.S3.Combinatorics.Graph.StarForming.ClauseModel

namespace D5.S3.Combinatorics.Graph.StarForming.ClauseModel
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual duplicate-free clause count in a graph of bounded maximum degree. -/
theorem clauses_card_le (d : ℕ) (hd : ∀ v, DegreeCapacity.degree G v ≤ d) :
    (clauses G).card ≤ (d+1)*Fintype.card V := by
  have hc : (Finset.univ.image (closed G)).card ≤ Fintype.card V :=
    Finset.card_image_le.trans_eq (Finset.card_univ)
  have ho : (Finset.univ.biUnion (fun u =>
      (Finset.univ.filter (G.Adj u)).image (oriented G u))).card ≤ d*Fintype.card V := by
    calc
      _ ≤ ∑ u : V, ((Finset.univ.filter (G.Adj u)).image (oriented G u)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _u : V, d := by
        apply Finset.sum_le_sum
        intro u _
        exact Finset.card_image_le.trans (hd u)
      _ = _ := by simp [Nat.mul_comm]
  exact (Finset.card_union_le _ _).trans (by nlinarith)

/-- Every actual clause has size at most five in a subcubic graph. -/
theorem subcubic_clause_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3)
    (E : Finset V) (hE : E ∈ clauses G) : E.card ≤ 5 := by
  rcases Finset.mem_union.mp hE with hc | ho
  · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hc
    have h := Finset.card_insert_le u (Finset.univ.filter (G.Adj u))
    have hu := hd u
    change (Finset.univ.filter (G.Adj u)).card ≤ 3 at hu
    unfold closed
    omega
  · obtain ⟨u,_,h⟩ := Finset.mem_biUnion.mp ho
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
    have huv := (Finset.mem_filter.mp hv).2
    have hmu : u ∈ Finset.univ.filter (G.Adj v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,G.adj_symm huv⟩
    have hu := hd u
    have hvd := hd v
    change (Finset.univ.filter (G.Adj u)).card ≤ 3 at hu
    change (Finset.univ.filter (G.Adj v)).card ≤ 3 at hvd
    have he1 := Finset.card_erase_add_one hv
    have he2 := Finset.card_erase_add_one hmu
    have hcu := Finset.card_union_le
      ((Finset.univ.filter (G.Adj u)).erase v) ((Finset.univ.filter (G.Adj v)).erase u)
    have hci := Finset.card_insert_le u
      (((Finset.univ.filter (G.Adj u)).erase v) ∪ ((Finset.univ.filter (G.Adj v)).erase u))
    unfold oriented
    omega

/-- Counts for the literal constraints in Feasible: two per clause, one per
vertex, and one binary variable per vertex and per distinct clause. -/
theorem subcubic_model_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3) :
    (clauses G).card ≤ 4*Fintype.card V ∧
      Fintype.card V + (clauses G).card ≤ 5*Fintype.card V ∧
      2*(clauses G).card + Fintype.card V ≤ 9*Fintype.card V := by
  have h := clauses_card_le G 3 hd
  constructor
  · simpa using h
  · constructor <;> omega

end D5.S3.Combinatorics.Graph.StarForming.ClauseModel
