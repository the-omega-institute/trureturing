/- GID: D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarFormingDissociationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Max]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim; result=D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result; claim=D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim
   digest: A ten-vertex bipartite graph refutes equality of 2-independence and upper 2-star formation. -/

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

/-- Conjecture 4.2, with finite vertex types represented by Fin n. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.Colorable 2 → beta G 2 = SF G 2

private def edges : Finset (Fin 10 × Fin 10) :=
  {(0,5), (0,6), (0,9), (1,5), (1,6), (1,8), (2,8), (2,9),
   (3,6), (3,7), (3,8), (3,9), (4,5), (4,7), (4,8), (4,9)}

private def counterGraph : SimpleGraph (Fin 10) where
  Adj i j := (i, j) ∈ edges ∨ (j, i) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i h; fin_cases i <;> simp [edges] at h⟩

private instance : DecidableRel counterGraph.Adj :=
  inferInstanceAs (DecidableRel (fun i j => (i, j) ∈ edges ∨ (j, i) ∈ edges))

private def selected : Finset (Fin 10) := {0, 1, 2, 5, 6, 7}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expand and independently verify all 1024 subset implications.
/-- The bipartite equality fails: beta is at most five, while a minimal
2-star-forming set has six vertices. -/
theorem result : ¬ claim := by
  have coloring : counterGraph.Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 5 then 0 else 1) ?_⟩
    change ∀ i j : Fin 10, counterGraph.Adj i j →
      (if i.val < 5 then (0 : Fin 2) else 1) ≠ (if j.val < 5 then 0 else 1)
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hlocal : LocalTwo counterGraph selected := by
    intro v
    fin_cases v <;> decide +kernel
  have proper : ∀ T ∈ selected.powerset, T ≠ selected → ¬ LocalTwo counterGraph T := by
    simp only [selected, ← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have minimal : IsMinimalStarForming counterGraph 2 selected := by
    refine ⟨(starForming_two_iff counterGraph selected).mpr hlocal, ?_⟩
    intro T hT hstar
    exact proper T (Finset.mem_powerset.mpr hT.subset) hT.ne
      ((starForming_two_iff counterGraph T).mp hstar)
  have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by
    decide +kernel
  have subsets : ∀ T ∈ ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).powerset,
      T.card = 6 → ¬ IsKIndependent counterGraph 2 T := by
    simp only [← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have six : ∀ T ∈ (Finset.univ : Finset (Fin 10)).powersetCard 6,
      ¬ IsKIndependent counterGraph 2 T := by
    intro T hT
    apply subsets T
    · rw [← huniv]
      exact Finset.mem_powerset.mpr (Finset.subset_univ T)
    · exact (Finset.mem_powersetCard.mp hT).2
  have upper : beta counterGraph 2 ≤ 5 := by
    apply Finset.sup_le
    intro I hI
    have hi := (Finset.mem_filter.mp hI).2
    by_contra hcard
    obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 6 ≤ I.card)
    apply six T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩)
    intro v hv
    exact lt_of_le_of_lt
      (Finset.card_le_card (Finset.filter_subset_filter (counterGraph.Adj v) hTI))
      (hi v (hTI hv))
  have lower : 6 ≤ SF counterGraph 2 := by
    classical
    have hmem : selected ∈ Finset.univ.powerset.filter
        (IsMinimalStarForming counterGraph 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), minimal⟩
    have hcard : selected.card = 6 := by decide +kernel
    exact hcard ▸ Finset.le_sup (f := Finset.card) hmem
  intro hclaim
  have heq := hclaim 10 counterGraph coloring
  omega

end D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
