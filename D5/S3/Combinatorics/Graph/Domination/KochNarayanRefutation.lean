/- GID: D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/KochNarayanRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.claim; result=D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result; claim=D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.claim
   digest: A fourteen-vertex bipartite graph refutes the Koch-Narayan edge bound. -/

import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Set.Card

/-!
Source: Garrison Koch and Darren Narayan, Maximal bipartite graphs with a unique
minimum dominating set, arXiv:2511.01719v1, Conjecture 1.
https://arxiv.org/html/2511.01719v1#Thmthm1

The domination predicates, minimum and attainment/upper-bound lemmas are imported
from GraphCoverDomination, whose scoped formal-conjectures source port retains
its Apache-2.0 attribution and license. No domination definition is duplicated.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.KochNarayanRefutation

open scoped BigOperators

/-- The printed ceiling, with exact rational division. -/
noncomputable def halfCeil (k : ℕ) : ℤ := ⌈(k : ℚ) / 2⌉

/-- The printed floor, with exact rational division. -/
noncomputable def halfFloor (k : ℕ) : ℤ := ⌊(k : ℚ) / 2⌋

/-- The printed positive part is taken in integers before the sum is indexed. -/
noncomputable def phi (n gamma : ℕ) : ℤ :=
  max 0 ((n : ℤ) - 3 * gamma - 2 * halfCeil gamma - halfFloor gamma + 1)

/-- The exact printed bound, including the inclusive sum from one to Phi. -/
noncomputable def bound (n gamma : ℕ) : ℤ :=
  2 * gamma + 2 * halfCeil gamma * halfFloor gamma +
    min ((n : ℤ) - 3 * gamma) (2 * halfCeil gamma - halfFloor gamma + 1) *
      (2 * halfCeil gamma + 1) +
    ∑ i ∈ Finset.Icc (1 : ℤ) (phi n gamma),
      ((2 * halfCeil gamma + 1) + ⌈(i : ℚ) / 2⌉)

/-- Conjecture 1 over all finite simple graphs and all minimum attaining sets. -/
def claim : Prop := by
  classical
  exact ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsBipartite → (∀ v, ¬ G.IsIsolated v) →
    (∃! D : Set V, G.IsDominating D ∧ D.ncard = G.dominationNumber) →
    2 ≤ G.dominationNumber → 3 * G.dominationNumber ≤ Fintype.card V →
    (G.edgeFinset.card : ℤ) ≤ bound (Fintype.card V) G.dominationNumber

/-- The oriented edge families, always from the left part to the right part. -/
def forward (u v : Fin 14) : Prop :=
  (u = 0 ∧ (v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13)) ∨
  ((u = 1 ∨ u = 2) ∧ v = 7) ∨
  ((u = 3 ∨ u = 4) ∧ v = 8) ∨
  ((u = 5 ∨ u = 6) ∧ v = 9) ∨
  (1 ≤ u.val ∧ u.val ≤ 6 ∧ (v = 10 ∨ v = 12 ∨ v = 13))

instance (u v : Fin 14) : Decidable (forward u v) := by
  unfold forward
  infer_instance

/-- The actual simple graph with the three disjoint edge families. -/
def graph : SimpleGraph (Fin 14) where
  Adj u v := forward u v ∨ forward v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The four centers. -/
def centers : Finset (Fin 14) := {0, 7, 8, 9}

private def block (v : Fin 14) : Fin 4 :=
  if v = 1 ∨ v = 2 ∨ v = 7 then 1
  else if v = 3 ∨ v = 4 ∨ v = 8 then 2
  else if v = 5 ∨ v = 6 ∨ v = 9 then 3 else 0

private def center (i : Fin 4) : Fin 14 := ![0, 7, 8, 9] i

private theorem closed_block : ∀ (i : Fin 4) (v : Fin 14),
    v = center i ∨ graph.Adj (center i) v → block v = i := by
  decide +kernel

private theorem dominates : graph.IsDominating centers := by
  unfold SimpleGraph.IsDominating
  decide +kernel

private theorem image_blocks (S : Finset (Fin 14)) (hS : graph.IsDominating S) :
    S.image block = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rcases hS (center i) with h | ⟨v, hv, hadj⟩
  · exact Finset.mem_image.mpr ⟨center i, h, closed_block i _ (Or.inl rfl)⟩
  · exact Finset.mem_image.mpr ⟨v, hv, closed_block i _ (Or.inr hadj)⟩

private theorem minimum_card (S : Finset (Fin 14)) (hS : graph.IsDominating S) :
    4 ≤ S.card := by
  have h := Finset.card_image_le (s := S) (f := block)
  rw [image_blocks S hS] at h
  simpa using h

private theorem gamma_eq : graph.dominationNumber = 4 := by
  apply Nat.le_antisymm
  · have h := graph.dominationNumber_le_of_isDominating centers dominates
    exact h.trans_eq (by decide +kernel)
  · obtain ⟨S, hS⟩ := graph.exists_isNDominatingSet_dominationNumber
    exact (minimum_card S hS.isDominating).trans_eq hS.card_eq

private theorem unique_four (S : Finset (Fin 14)) (hS : graph.IsDominating S)
    (hcard : S.card = 4) : S = centers := by
  have hinj : Set.InjOn block (S : Set (Fin 14)) :=
    Finset.card_image_iff.mp (by rw [image_blocks S hS, hcard]; decide +kernel)
  obtain ⟨t, ht, ht0⟩ : ∃ t ∈ S, t = 0 ∨ t = 11 := by
    rcases hS 11 with h | ⟨v, hv, hadj⟩
    · exact ⟨11, h, Or.inr rfl⟩
    · refine ⟨v, hv, Or.inl ?_⟩
      have : ∀ v : Fin 14, graph.Adj 11 v → v = 0 := by decide +kernel
      exact this v hadj
  have hubs_absent : ∀ v : Fin 14, v = 10 ∨ v = 12 ∨ v = 13 → v ∉ S := by
    intro v hv hmem
    have hb : block v = block t := by
      rcases ht0 with rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> decide +kernel
    have heq := hinj hmem ht hb
    rcases ht0 with rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> contradiction
  have pair_forces : ∀ (y a b : Fin 14),
      block a = block y → block b = block y → a ≠ b →
      (∀ v, graph.Adj a v → v = y ∨ v = 10 ∨ v = 12 ∨ v = 13) →
      (∀ v, graph.Adj b v → v = y ∨ v = 10 ∨ v = 12 ∨ v = 13) → y ∈ S := by
    intro y a b hay hby hab ha hb
    by_contra hy
    have hdom : ∀ x, (∀ v, graph.Adj x v → v = y ∨ v = 10 ∨ v = 12 ∨ v = 13) →
        x ∈ S := by
      intro x hx
      rcases hS x with h | ⟨v, hv, hadj⟩
      · exact h
      · rcases hx v hadj with rfl | hh
        · exact False.elim (hy hv)
        · exact False.elim (hubs_absent v hh hv)
    exact hab (hinj (hdom a ha) (hdom b hb) (hay.trans hby.symm))
  have h7 : (7 : Fin 14) ∈ S := pair_forces 7 1 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h8 : (8 : Fin 14) ∈ S := pair_forces 8 3 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h9 : (9 : Fin 14) ∈ S := pair_forces 9 5 6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have small_absent : ∀ v : Fin 14, 1 ≤ v.val → v.val ≤ 6 → v ∉ S := by
    intro v h1 h6 hv
    have small_blocks : ∀ v : Fin 14, 1 ≤ v.val → v.val ≤ 6 →
        block v = block 7 ∨ block v = block 8 ∨ block v = block 9 := by
      decide +kernel
    have hwhich := small_blocks v h1 h6
    rcases hwhich with h | h | h
    · have := hinj hv h7 h
      subst v
      norm_num at h6
    · have := hinj hv h8 h
      subst v
      norm_num at h6
    · have := hinj hv h9 h
      subst v
      norm_num at h6
  have h0 : (0 : Fin 14) ∈ S := by
    rcases ht0 with rfl | rfl
    · exact ht
    · rcases hS 10 with h | ⟨v, hv, hadj⟩
      · exact False.elim (hubs_absent 10 (Or.inl rfl) h)
      · have hv0 : v = 0 ∨ (1 ≤ v.val ∧ v.val ≤ 6) := by
          have : ∀ v : Fin 14, graph.Adj 10 v → v = 0 ∨ (1 ≤ v.val ∧ v.val ≤ 6) :=
            by decide +kernel
          exact this v hadj
        rcases hv0 with rfl | ⟨h1, h6⟩
        · exact hv
        · exact False.elim (small_absent v h1 h6 hv)
  have hsub : centers ⊆ S := by
    intro v hv
    simp only [centers, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa [centers] using hcard.le)).symm

private theorem minimum_sets {V : Type} [Finite V] (G : SimpleGraph V) (D : Set V) :
    (G.IsDominating D ∧ D.ncard = G.dominationNumber) ↔
    (G.IsDominating D ∧ ∀ S : Set V, G.IsDominating S → D.ncard ≤ S.ncard) := by
  classical
  letI := Fintype.ofFinite V
  constructor
  · rintro ⟨hD, hc⟩
    refine ⟨hD, fun S hS => ?_⟩
    rw [hc, Set.ncard_eq_toFinset_card']
    apply G.dominationNumber_le_of_isDominating
    simpa using hS
  · rintro ⟨hD, hmin⟩
    refine ⟨hD, Nat.le_antisymm ?_ ?_⟩
    · obtain ⟨S, hS⟩ := G.exists_isNDominatingSet_dominationNumber
      simpa [hS.card_eq] using hmin S hS.isDominating
    · rw [Set.ncard_eq_toFinset_card']
      apply G.dominationNumber_le_of_isDominating
      simpa using hD

private theorem unique_minimum :
    ∃! D : Set (Fin 14), graph.IsDominating D ∧ D.ncard = graph.dominationNumber := by
  classical
  refine ⟨centers, ⟨dominates, by simp [gamma_eq, centers]⟩, ?_⟩
  intro S hS
  have hmin := (minimum_sets graph S).mp hS
  have hSdom : graph.IsDominating S.toFinset := by simpa using hmin.1
  have hScard : S.toFinset.card = 4 := by
    apply Nat.le_antisymm
    · have hu := hmin.2 centers dominates
      simpa [Set.ncard_eq_toFinset_card', centers] using hu
    · exact minimum_card S.toFinset hSdom
  have heq : S.toFinset = centers := unique_four S.toFinset hSdom hScard
  simpa using congrArg (fun s : Finset (Fin 14) => (s : Set (Fin 14))) heq

private theorem bipartite : graph.IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite (s := {v | v.val < 7})
    (t := {v | 7 ≤ v.val})
  constructor
  · exact Set.disjoint_left.mpr (by
      intro v h1 h2
      change v.val < 7 at h1
      change 7 ≤ v.val at h2
      omega)
  · decide +kernel

private theorem no_isolates : ∀ v, ¬ graph.IsIsolated v := by
  unfold SimpleGraph.IsIsolated
  decide +kernel

private theorem edge_count : graph.edgeFinset.card = 28 := by
  decide +kernel

/-- The whole printed universal conjecture is false. -/
theorem result : ¬ claim := by
  intro h
  have hbound := h (Fin 14) graph bipartite no_isolates unique_minimum
    (by rw [gamma_eq]; decide) (by rw [gamma_eq]; decide)
  have hedges := edge_count
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hedges hbound
  rw [hedges, gamma_eq] at hbound
  norm_num [bound, phi, halfCeil, halfFloor] at hbound

#print axioms result

end D5.S3.Combinatorics.Graph.Domination.KochNarayanRefutation
