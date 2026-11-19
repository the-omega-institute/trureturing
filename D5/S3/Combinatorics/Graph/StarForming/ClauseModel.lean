/- GID: D5/S3/Combinatorics/Graph/StarForming/ClauseModel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClauseModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact finite private-clause binary model and actual graph constraints. -/

import D5.S3.Combinatorics.Graph.StarForming.PrivateClauses
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import D5.S3.Combinatorics.Graph.StarForming.DisjointUnion

/-! The integer model in PRIVATE_CLAUSES_AND_BOUNDARY_ACCOUNTING, received
from subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Clauses are actual vertex sets, with duplicates removed. The
auxiliary variable means a singleton intersection, not a solver oracle. -/
namespace D5.S3.Combinatorics.Graph.StarForming.ClauseModel
open StarFormingDissociationRefutation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def closed (u : V) : Finset V := insert u (Finset.univ.filter (G.Adj u))
def oriented (u v : V) : Finset V :=
  insert u (((Finset.univ.filter (G.Adj u)).erase v) ∪
    ((Finset.univ.filter (G.Adj v)).erase u))

def clauses : Finset (Finset V) :=
  Finset.univ.image (closed G) ∪
    Finset.univ.biUnion (fun u => (Finset.univ.filter (G.Adj u)).image (oriented G u))

private theorem closed_mem (u : V) : closed G u ∈ clauses G := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)

private theorem oriented_mem (u v : V) (huv : G.Adj u v) : oriented G u v ∈ clauses G := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,Finset.mem_image.mpr
    ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv⟩,rfl⟩⟩

private theorem clause_cases (E : Finset V) (hE : E ∈ clauses G) :
    (∃ u, E = closed G u) ∨ (∃ u v, G.Adj u v ∧ E = oriented G u v) := by
  rcases Finset.mem_union.mp hE with h | h
  · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨u,rfl⟩
  · obtain ⟨u,_,h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨u,v,(Finset.mem_filter.mp hv).2,rfl⟩

private theorem mem_closed (u w : V) :
    w ∈ closed G u ↔ PrivateClauses.Support G.Adj (.closed u) w := by
  simp [closed,PrivateClauses.Support]

private theorem mem_oriented (u v w : V) :
    w ∈ oriented G u v ↔ PrivateClauses.Support G.Adj (.oriented u v) w := by
  simp [oriented,PrivateClauses.Support,and_comm]

/-- All actual clauses are nonempty, including at isolated vertices. -/
theorem clause_nonempty (E : Finset V) (hE : E ∈ clauses G) : E.Nonempty := by
  rcases clause_cases G E hE with ⟨u,rfl⟩ | ⟨u,v,_,rfl⟩ <;>
    exact ⟨u,Finset.mem_insert_self _ _⟩

/-- The finite set model keeps exactly the source's valid clauses. -/
theorem minimal_iff_private (S : Finset V) :
    IsMinimalStarForming G 2 S ↔
      (∀ E ∈ clauses G, (S ∩ E).Nonempty) ∧
      ∀ v ∈ S, ∃ E ∈ clauses G, S ∩ E = {v} := by
  rw [← regular_minimal_iff,PrivateClauses.minimal_iff_private]
  constructor
  · rintro ⟨hh,hp⟩
    constructor
    · intro E hE
      rcases clause_cases G E hE with ⟨u,rfl⟩ | ⟨u,v,huv,rfl⟩
      · obtain ⟨w,hw,hs⟩ := hh (.closed u) trivial
        exact ⟨w,Finset.mem_inter.mpr ⟨hw,(mem_closed G u w).mpr hs⟩⟩
      · obtain ⟨w,hw,hs⟩ := hh (.oriented u v) huv
        exact ⟨w,Finset.mem_inter.mpr ⟨hw,(mem_oriented G u v w).mpr hs⟩⟩
    · intro v hv
      obtain ⟨c,hvalid,hs,hu⟩ := hp v hv
      cases c with
      | closed u =>
        refine ⟨closed G u,closed_mem G u,?_⟩
        ext w
        simp only [Finset.mem_inter,Finset.mem_singleton]
        constructor
        · rintro ⟨hw,hc⟩
          exact hu w hw ((mem_closed G u w).mp hc)
        · rintro rfl
          exact ⟨hv,(mem_closed G u w).mpr hs⟩
      | oriented u w =>
        refine ⟨oriented G u w,oriented_mem G u w hvalid,?_⟩
        ext t
        simp only [Finset.mem_inter,Finset.mem_singleton]
        constructor
        · rintro ⟨ht,hc⟩
          exact hu t ht ((mem_oriented G u w t).mp hc)
        · rintro rfl
          exact ⟨hv,(mem_oriented G u w t).mpr hs⟩
  · rintro ⟨hh,hp⟩
    constructor
    · intro c hc
      cases c with
      | closed u =>
        obtain ⟨v,hv⟩ := hh (closed G u) (closed_mem G u)
        exact ⟨v,(Finset.mem_inter.mp hv).1,
          (mem_closed G u v).mp (Finset.mem_inter.mp hv).2⟩
      | oriented u v =>
        obtain ⟨w,hw⟩ := hh (oriented G u v) (oriented_mem G u v hc)
        exact ⟨w,(Finset.mem_inter.mp hw).1,
          (mem_oriented G u v w).mp (Finset.mem_inter.mp hw).2⟩
    · intro v hv
      obtain ⟨E,hE,he⟩ := hp v hv
      have hvm : v ∈ E := (Finset.mem_inter.mp (he.symm ▸ Finset.mem_singleton_self v)).2
      have hu : ∀ w ∈ S, w ∈ E → w = v := by
        intro w hw hc
        exact Finset.mem_singleton.mp (he ▸ Finset.mem_inter.mpr ⟨hw,hc⟩)
      rcases clause_cases G E hE with ⟨u,rfl⟩ | ⟨u,w,hadj,rfl⟩
      · exact ⟨.closed u,trivial,(mem_closed G u v).mp hvm,
          fun t ht hs => hu t ht ((mem_closed G u t).mpr hs)⟩
      · exact ⟨.oriented u w,hadj,(mem_oriented G u w v).mp hvm,
          fun t ht hs => hu t ht ((mem_oriented G u w t).mpr hs)⟩

/-- Binary integer variables, written as Bool to retain literal integrality. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

def Feasible (S : Finset V) (p : Finset V → Bool) : Prop :=
  (∀ E ∈ clauses G, 1 ≤ (S ∩ E).card ∧
    (S ∩ E).card + (E.card-1)*bit (p E) ≤ E.card) ∧
  ∀ v ∈ S, 1 ≤ ∑ E ∈ (clauses G).filter (fun E => v ∈ E), bit (p E)

/-- The displayed binary constraints characterize minimal formation exactly.
No optimization algorithm, finite-size restriction or extra hypothesis is used. -/
theorem feasible_iff_minimal (S : Finset V) :
    (∃ p, Feasible G S p) ↔ IsMinimalStarForming G 2 S := by
  classical
  rw [minimal_iff_private]
  constructor
  · rintro ⟨p,hc,hv⟩
    refine ⟨fun E hE => Finset.card_pos.mp (hc E hE).1,?_⟩
    intro v hs
    have hpos := hv v hs
    have hex : ∃ E ∈ (clauses G).filter (fun E => v ∈ E), 0 < bit (p E) := by
      by_contra hn
      have hz : (∑ E ∈ (clauses G).filter (fun E => v ∈ E), bit (p E)) = 0 := by
        apply Finset.sum_eq_zero
        intro E hE
        have hh : ¬ 0 < bit (p E) := fun he => hn ⟨E,hE,he⟩
        omega
      omega
    obtain ⟨E,hE,hp⟩ := hex
    rcases Finset.mem_filter.mp hE with ⟨hE,hm⟩
    have hb : bit (p E) = 1 := by cases h : p E <;> simp_all [bit]
    have hn := hc E hE
    have hepos := (clause_nonempty G E hE).card_pos
    have hcard : (S ∩ E).card = 1 := by rw [hb] at hn; omega
    refine ⟨E,hE,?_⟩
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hs,hm⟩,
      fun w hw => Finset.card_le_one.mp hcard.le w hw v (Finset.mem_inter.mpr ⟨hs,hm⟩)⟩
  · rintro ⟨hh,hv⟩
    let p : Finset V → Bool := fun E => decide ((S ∩ E).card = 1)
    refine ⟨p,?_,?_⟩
    · intro E hE
      have hsub : (S ∩ E).card ≤ E.card := Finset.card_le_card Finset.inter_subset_right
      refine ⟨(hh E hE).card_pos,?_⟩
      by_cases h : (S ∩ E).card = 1
      · simp only [p,h,decide_true,bit,ite_true]
        have hepos := (clause_nonempty G E hE).card_pos
        omega
      · simpa [p,h,bit] using hsub
    · intro v hs
      obtain ⟨E,hE,he⟩ := hv v hs
      have hmem : E ∈ (clauses G).filter (fun E => v ∈ E) :=
        Finset.mem_filter.mpr ⟨hE,(Finset.mem_inter.mp (he.symm ▸
          Finset.mem_singleton_self v)).2⟩
      have hp : bit (p E) = 1 := by simp [p,he,bit]
      have hn := Finset.single_le_sum (fun E _ => Nat.zero_le (bit (p E))) hmem
      simpa only [hp] using hn

/-- The objective maximum is SF, with an actual feasible optimizer. -/
theorem objective_attained :
    (∃ S p, Feasible G S p ∧ S.card = SF G 2) ∧
    ∀ S p, Feasible G S p → S.card ≤ SF G 2 := by
  classical
  constructor
  · obtain ⟨S,hS,he⟩ := sf_attained G 2
    obtain ⟨p,hp⟩ := (feasible_iff_minimal G S).mpr hS
    exact ⟨S,p,hp,he⟩
  · intro S p hp
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      (feasible_iff_minimal G S).mp ⟨p,hp⟩⟩)

end D5.S3.Combinatorics.Graph.StarForming.ClauseModel
