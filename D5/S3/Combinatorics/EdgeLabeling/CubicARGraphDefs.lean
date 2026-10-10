/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Additive rigidity for edge labels and the local obstruction at degree three. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs

/-- Def. 1.1: every subset of the edges at v has a different label sum. -/
def IsARVertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V → ℕ) (v : V) : Prop :=
  Set.InjOn (fun S : Finset (Sym2 V) => ∑ e ∈ S, f e) ↑(G.incidenceFinset v).powerset

/-- Def. 1.3: an AR-labeling onto {1, …, |E|}. -/
def IsARGraph {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ f : Sym2 V → ℕ, Set.BijOn f G.edgeSet (Set.Icc 1 G.edgeFinset.card) ∧ ∀ v, IsARVertex G f v

private theorem triple_subset_sums_injective {α : Type} [DecidableEq α] (f : α → ℕ)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : 0 < f a) (habf : f a < f b) (hbcf : f b < f c)
    (hadd : f a + f b ≠ f c) :
    Set.InjOn (fun S : Finset α => ∑ e ∈ S, f e) ↑({a, b, c} : Finset α).powerset := by
  intro S hS T hT hsum
  have hc : ({c} : Finset α).powerset = {∅, {c}} := by
    rw [show ({c} : Finset α) = insert c ∅ from rfl,
      Finset.powerset_insert, Finset.powerset_empty]
    simp
  simp only [Finset.mem_coe, Finset.powerset_insert,
    hc, Finset.image_union, Finset.image_insert,
    Finset.image_singleton, Finset.insert_empty, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hS hT
  simp only [or_assoc] at hS hT
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hsum ⊢ <;> omega

/-- With three increasing positive labels, the only possible collision is the sum
of the two smaller labels against the largest label. -/
private theorem triple_subset_sums_injective_iff {α : Type} [DecidableEq α] (f : α → ℕ)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : 0 < f a) (habf : f a < f b) (hbcf : f b < f c) :
    Set.InjOn (fun S : Finset α => ∑ e ∈ S, f e) ↑({a, b, c} : Finset α).powerset ↔
      f a + f b ≠ f c := by
  constructor
  · intro h hsum
    have hleft : ({a, b} : Finset α) ∈ ({a, b, c} : Finset α).powerset := by
      simp [Finset.mem_powerset, Finset.subset_iff]
    have hright : ({c} : Finset α) ∈ ({a, b, c} : Finset α).powerset := by
      simp [Finset.mem_powerset, Finset.subset_iff]
    have heq := h hleft hright (by simpa [hab] using hsum)
    have hamem : a ∈ ({c} : Finset α) := heq ▸ (by simp)
    exact hac (by simpa using hamem)
  · exact triple_subset_sums_injective f a b c hab hac hbc ha habf hbcf

/-- A cubic vertex is additively rigid when its incident labels are positive and
distinct and no two of them sum to the third. -/
theorem ar_vertex_of_no_additive_relation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℕ) (v : V)
    (hdegree : G.degree v = 3)
    (hpositive : ∀ e ∈ G.incidenceFinset v, 0 < f e)
    (hinjective : Set.InjOn f ↑(G.incidenceFinset v))
    (hno : ∀ a ∈ G.incidenceFinset v, ∀ b ∈ G.incidenceFinset v,
      ∀ c ∈ G.incidenceFinset v, a ≠ b → a ≠ c → b ≠ c → f a + f b ≠ f c) :
    IsARVertex G f v := by
  obtain ⟨a, b, c, hab, hac, hbc, htriple⟩ :=
    Finset.card_eq_three.mp ((G.card_incidenceFinset_eq_degree v).trans hdegree)
  have ha : a ∈ G.incidenceFinset v := by simp [htriple]
  have hb : b ∈ G.incidenceFinset v := by simp [htriple]
  have hc : c ∈ G.incidenceFinset v := by simp [htriple]
  have habf : f a ≠ f b := fun h => hab (hinjective ha hb h)
  have hacf : f a ≠ f c := fun h => hac (hinjective ha hc h)
  have hbcf : f b ≠ f c := fun h => hbc (hinjective hb hc h)
  have horder :
      (f a < f b ∧ f b < f c) ∨ (f a < f c ∧ f c < f b) ∨
      (f b < f a ∧ f a < f c) ∨ (f b < f c ∧ f c < f a) ∨
      (f c < f a ∧ f a < f b) ∨ (f c < f b ∧ f b < f a) := by omega
  unfold IsARVertex
  rw [htriple]
  rcases horder with ⟨habv, hbcv⟩ | ⟨hacv, hcbv⟩ | ⟨hbav, hacv⟩ |
    ⟨hbcv, hcav⟩ | ⟨hcav, habv⟩ | ⟨hcbv, hbav⟩
  · exact (triple_subset_sums_injective_iff f a b c hab hac hbc
      (hpositive a ha) habv hbcv).mpr (hno a ha b hb c hc hab hac hbc)
  · have heq : ({a, c, b} : Finset (Sym2 V)) = {a, b, c} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact (triple_subset_sums_injective_iff f a c b hac hab hbc.symm
      (hpositive a ha) hacv hcbv).mpr (hno a ha c hc b hb hac hab hbc.symm)
  · have heq : ({b, a, c} : Finset (Sym2 V)) = {a, b, c} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact (triple_subset_sums_injective_iff f b a c hab.symm hbc hac
      (hpositive b hb) hbav hacv).mpr (hno b hb a ha c hc hab.symm hbc hac)
  · have heq : ({b, c, a} : Finset (Sym2 V)) = {a, b, c} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact (triple_subset_sums_injective_iff f b c a hbc hab.symm hac.symm
      (hpositive b hb) hbcv hcav).mpr (hno b hb c hc a ha hbc hab.symm hac.symm)
  · have heq : ({c, a, b} : Finset (Sym2 V)) = {a, b, c} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact (triple_subset_sums_injective_iff f c a b hac.symm hbc.symm hab
      (hpositive c hc) hcav habv).mpr (hno c hc a ha b hb hac.symm hbc.symm hab)
  · have heq : ({c, b, a} : Finset (Sym2 V)) = {a, b, c} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact (triple_subset_sums_injective_iff f c b a hbc.symm hac.symm hab.symm
      (hpositive c hc) hcbv hbav).mpr (hno c hc b hb a ha hbc.symm hac.symm hab.symm)
/-- The degree-sum identity specialized to a cubic graph. -/
theorem cubic_card_identity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 3) :
    3 * Fintype.card V = 2 * G.edgeFinset.card := by
  have h := G.sum_degrees_eq_twice_card_edges
  simpa [hdegree, mul_comm] using h

/-- A nonempty simple cubic graph has at least four vertices and an even order. -/
theorem cubic_order_constraints {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 3)
    (hne : 0 < Fintype.card V) : 4 ≤ Fintype.card V ∧ Even (Fintype.card V) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hne
  have hlt := G.degree_lt_card_verts v
  rw [hdegree v] at hlt
  have hcard := cubic_card_identity G hdegree
  refine ⟨hlt, ?_⟩
  rw [Nat.even_iff]
  omega

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs
