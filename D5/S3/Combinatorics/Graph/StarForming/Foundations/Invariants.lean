/- GID: D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Foundations/Invariants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Finite graph independence and star formation on arbitrary vertex types. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases

namespace D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of the selected set has fewer than k selected neighbours. -/
def IsKIndependent (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (I : Finset V) : Prop := ∀ v ∈ I, (I.filter (G.Adj v)).card < k

instance (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (I : Finset V) :
    Decidable (IsKIndependent G k I) :=
  inferInstanceAs (Decidable (∀ v ∈ I, (I.filter (G.Adj v)).card < k))

/-- Maximum size of a k-independent set, with value zero for an empty family. -/
def beta (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (IsKIndependent G k)).sup Finset.card

/-- A (not necessarily induced) k-leaf star in S plus each outside vertex,
containing that vertex. The centre is distinct from all leaves. -/
def IsStarForming (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∃ (c : V) (L : Finset V), L.card = k ∧ c ∉ L ∧
    insert c L ⊆ insert v S ∧ (∀ ℓ ∈ L, G.Adj c ℓ) ∧ v ∈ insert c L

/-- Inclusion-minimality, not minimum cardinality. -/
def IsMinimalStarForming (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  IsStarForming G k S ∧ ∀ T : Finset V, T ⊂ S → ¬ IsStarForming G k T

/-- Maximum cardinality among inclusion-minimal k-star-forming sets. -/
noncomputable def SF (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.powerset.filter (IsMinimalStarForming G k)).sup Finset.card

/-- The local criterion in Lemma 2.2 for k = 2. -/
def LocalTwo (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ v, v ∉ S → 2 ≤ (S.filter (G.Adj v)).card ∨
    ∃ u ∈ S, G.Adj v u ∧ 1 ≤ (S.filter (G.Adj u)).card

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Decidable (LocalTwo G S) := inferInstanceAs (Decidable
      (∀ v, v ∉ S → 2 ≤ (S.filter (G.Adj v)).card ∨
        ∃ u ∈ S, G.Adj v u ∧ 1 ≤ (S.filter (G.Adj u)).card))

omit [Fintype V] in
/-- A two-leaf star containing an outside vertex has that vertex either at
its centre or at a leaf. Conversely either local alternative constructs a star. -/
theorem starForming_two_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : IsStarForming G 2 S ↔ LocalTwo G S := by
  constructor
  · intro h v hv
    obtain ⟨c, L, hcard, hc, hsub, hadj, hvin⟩ := h v hv
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := hadj a (by simp)
    have hb := hadj b (by simp)
    have ca : c ≠ a := by simpa using fun h => hc (by simp [h])
    have cb : c ≠ b := by simpa using fun h => hc (by simp [h])
    have hin (x : V) (hx : x ∈ insert c {a, b}) : x = v ∨ x ∈ S :=
      Finset.mem_insert.mp (hsub hx)
    rcases Finset.mem_insert.mp hvin with hvc | hvl
    · subst c
      have has : a ∈ S := (hin a (by simp)).resolve_left (Ne.symm ca)
      have hbs : b ∈ S := (hin b (by simp)).resolve_left (Ne.symm cb)
      left
      have htwo : 1 < (S.filter (G.Adj v)).card := Finset.one_lt_card.mpr
        ⟨a, Finset.mem_filter.mpr ⟨has, ha⟩,
          b, Finset.mem_filter.mpr ⟨hbs, hb⟩, hab⟩
      omega
    · have hcs : c ∈ S := (hin c (by simp)).resolve_left (by
        intro hcv; subst c; exact hc hvl)
      rcases Finset.mem_insert.mp hvl with hva | hvb
      · subst a
        have hbs : b ∈ S := (hin b (by simp)).resolve_left (Ne.symm hab)
        exact Or.inr ⟨c, hcs, G.adj_symm ha,
          Finset.one_le_card.mpr ⟨b, Finset.mem_filter.mpr ⟨hbs, hb⟩⟩⟩
      · have hvb' : v = b := Finset.mem_singleton.mp hvb
        subst b
        have has : a ∈ S := (hin a (by simp)).resolve_left hab
        exact Or.inr ⟨c, hcs, G.adj_symm hb,
          Finset.one_le_card.mpr ⟨a, Finset.mem_filter.mpr ⟨has, ha⟩⟩⟩
  · intro h v hv
    rcases h v hv with htwo | ⟨u, hu, hvu, hone⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
        1 < (S.filter (G.Adj v)).card)
      rcases Finset.mem_filter.mp ha with ⟨has, hva⟩
      rcases Finset.mem_filter.mp hb with ⟨hbs, hvb⟩
      refine ⟨v, {a, b}, by simp [hab], ?_, ?_, ?_, by simp⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h => h.elim (fun h => hv (h ▸ has)) (fun h => hv (h ▸ hbs))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr has
        · exact Or.inr hbs
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
    · obtain ⟨w, hw⟩ := Finset.one_le_card.mp hone
      rcases Finset.mem_filter.mp hw with ⟨hws, huw⟩
      have hvw : v ≠ w := fun h => hv (h ▸ hws)
      refine ⟨u, {v, w}, by simp [hvw], ?_, ?_, ?_, by simp⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h => h.elim (fun h => G.irrefl (h ▸ G.adj_symm hvu))
          (fun h => G.irrefl (h ▸ huw))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inr hu
        · exact Or.inl rfl
        · exact Or.inr hws
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact G.adj_symm hvu
        · exact huw

end D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
open D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dissociation means that two selected neighbors of a selected vertex coincide.
This is also the relation-level predicate used by graph-cover arguments. -/
theorem independent_iff {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (S : Finset W) :
    IsKIndependent G 2 S ↔ ∀ v ∈ S, ∀ a ∈ S, ∀ b ∈ S,
      G.Adj v a → G.Adj v b → a = b := by
  simp only [IsKIndependent, Nat.lt_succ_iff, Finset.card_le_one]
  constructor
  · intro h v hv a ha b hb hva hvb
    exact h v hv a (Finset.mem_filter.mpr ⟨ha,hva⟩) b (Finset.mem_filter.mpr ⟨hb,hvb⟩)
  · intro h v hv a ha b hb
    exact h v hv a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

end D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
