/- GID: D5/S3/Combinatorics/Graph/StarForming/DisjointUnion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/DisjointUnion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Componentwise star minimality and additivity of finite graph maxima. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Sum

namespace D5.S3.Combinatorics.Graph.StarForming
open StarFormingDissociationRefutation

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

noncomputable instance (G : SimpleGraph V) (H : SimpleGraph W) :
    DecidableRel (G ⊕g H).Adj := Classical.decRel _

/-- Restrict every star to its actual disjoint component. -/
theorem starForming_sum_left (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ)
    (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) :
    IsStarForming G k S.toLeft := by
  intro v hv
  obtain ⟨c,L,hcard,hc,hsub,hadj,hvin⟩ := h (.inl v) (by simpa using hv)
  cases c with
  | inl c =>
    have hright : L.toRight = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      simpa using hadj (.inr w) (Finset.mem_toRight.mp hw)
    have hleft : L.toLeft.card = k := by
      have hh := Finset.card_toLeft_add_card_toRight (u := L)
      rw [hright,Finset.card_empty,Nat.add_zero,hcard] at hh
      exact hh
    refine ⟨c,L.toLeft,hleft,?_,?_,?_,?_⟩
    · simpa using hc
    · intro x hx
      have hx' : Sum.inl x ∈ insert (Sum.inl c) L := by simpa using hx
      simpa using hsub hx'
    · intro x hx
      exact hadj (.inl x) (Finset.mem_toLeft.mp hx)
    · simpa using hvin
  | inr c =>
    rcases Finset.mem_insert.mp hvin with heq | hin
    · cases heq
    · have hh := hadj (.inl v) hin
      simp at hh

/-- The right-component restriction has the same complete star semantics. -/
theorem starForming_sum_right (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ)
    (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) :
    IsStarForming H k S.toRight := by
  intro v hv
  obtain ⟨c,L,hcard,hc,hsub,hadj,hvin⟩ := h (.inr v) (by simpa using hv)
  cases c with
  | inr c =>
    have hleft : L.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      simpa using hadj (.inl w) (Finset.mem_toLeft.mp hw)
    have hright : L.toRight.card = k := by
      have hh := Finset.card_toLeft_add_card_toRight (u := L)
      rw [hleft,Finset.card_empty,Nat.zero_add,hcard] at hh
      exact hh
    refine ⟨c,L.toRight,hright,?_,?_,?_,?_⟩
    · simpa using hc
    · intro x hx
      have hx' : Sum.inr x ∈ insert (Sum.inr c) L := by simpa using hx
      simpa using hsub hx'
    · intro x hx
      exact hadj (.inr x) (Finset.mem_toRight.mp hx)
    · simpa using hvin
  | inl c =>
    rcases Finset.mem_insert.mp hvin with heq | hin
    · cases heq
    · have hh := hadj (.inr v) hin
      simp at hh

/-- Formation is componentwise, including zero stars and empty components. -/
theorem starForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ)
    (S : Finset (V ⊕ W)) :
    IsStarForming (G ⊕g H) k S ↔
      IsStarForming G k S.toLeft ∧ IsStarForming H k S.toRight := by
  constructor
  · intro h
    exact ⟨starForming_sum_left G H k S h,starForming_sum_right G H k S h⟩
  · rintro ⟨hl,hr⟩ (v | v) hv
    · obtain ⟨c,L,hcard,hc,hsub,hadj,hvin⟩ := hl v (by simpa using hv)
      refine ⟨.inl c,L.map Function.Embedding.inl,by simpa using hcard,?_,?_,?_,?_⟩
      · simpa using hc
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa using hsub (Finset.mem_insert_self c L)
        · obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
          simpa using hsub (Finset.mem_insert_of_mem ha)
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
        exact hadj a ha
      · simpa using hvin
    · obtain ⟨c,L,hcard,hc,hsub,hadj,hvin⟩ := hr v (by simpa using hv)
      refine ⟨.inr c,L.map Function.Embedding.inr,by simpa using hcard,?_,?_,?_,?_⟩
      · simpa using hc
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa using hsub (Finset.mem_insert_self c L)
        · obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
          simpa using hsub (Finset.mem_insert_of_mem ha)
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
        exact hadj a ha
      · simpa using hvin

/-- A minimal selection is minimal separately in every component. -/
theorem minimalStarForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ)
    (S : Finset (V ⊕ W)) :
    IsMinimalStarForming (G ⊕g H) k S ↔
      IsMinimalStarForming G k S.toLeft ∧ IsMinimalStarForming H k S.toRight := by
  constructor
  · rintro ⟨hf,hm⟩
    have hh := (starForming_sum_iff G H k S).mp hf
    constructor
    · refine ⟨hh.1,?_⟩
      intro T hT hforms
      apply hm (T.disjSum S.toRight)
      · simpa only [Finset.toLeft_disjSum_toRight] using
          Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset hT
            (Finset.Subset.refl S.toRight)
      · apply (starForming_sum_iff G H k _).mpr
        simpa using And.intro hforms hh.2
    · refine ⟨hh.2,?_⟩
      intro T hT hforms
      apply hm (S.toLeft.disjSum T)
      · simpa only [Finset.toLeft_disjSum_toRight] using
          Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset
            (Finset.Subset.refl S.toLeft) hT
      · apply (starForming_sum_iff G H k _).mpr
        simpa using And.intro hh.1 hforms
  · rintro ⟨⟨hl,hml⟩,⟨hr,hmr⟩⟩
    refine ⟨(starForming_sum_iff G H k S).mpr ⟨hl,hr⟩,?_⟩
    intro T hT hforms
    have ht := (starForming_sum_iff G H k T).mp hforms
    have hle := Finset.toLeft_subset_toLeft hT.1
    have hre := Finset.toRight_subset_toRight hT.1
    by_cases heql : T.toLeft = S.toLeft
    · by_cases heqr : T.toRight = S.toRight
      · have heq : T = S := by
          rw [← Finset.toLeft_disjSum_toRight (u := T),
            ← Finset.toLeft_disjSum_toRight (u := S),heql,heqr]
        exact hT.2 (heq ▸ Finset.Subset.refl _)
      · exact hmr T.toRight (Finset.ssubset_iff_subset_ne.mpr ⟨hre,heqr⟩) ht.2
    · exact hml T.toLeft (Finset.ssubset_iff_subset_ne.mpr ⟨hle,heql⟩) ht.1

/-- Finite maximal cardinalities have actual attaining selections. -/
theorem beta_attained (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ∃ S : Finset V, IsKIndependent G k S ∧ S.card = beta G k := by
  classical
  have hn : (Finset.univ.powerset.filter (IsKIndependent G k)).Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨by simp,?_⟩⟩
    intro v hv
    simp at hv
  obtain ⟨S,hS,hcard⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨S,(Finset.mem_filter.mp hS).2,hcard.symm⟩

/-- Every finite graph has a minimal forming set, even when no star exists. -/
theorem minimalStarForming_exists (G : SimpleGraph V) (k : ℕ) :
    ∃ S : Finset V, IsMinimalStarForming G k S := by
  classical
  let F := Finset.univ.powerset.filter (IsStarForming G k)
  have hn : F.Nonempty := by
    refine ⟨Finset.univ,Finset.mem_filter.mpr ⟨by simp,?_⟩⟩
    intro v hv
    exact False.elim (hv (Finset.mem_univ v))
  obtain ⟨S,hS,hmin⟩ := Finset.exists_min_image F Finset.card hn
  refine ⟨S,(Finset.mem_filter.mp hS).2,?_⟩
  intro T hT hf
  have hc := hmin T (Finset.mem_filter.mpr ⟨by simp,hf⟩)
  exact (Nat.not_le_of_lt (Finset.card_lt_card hT)) hc

/-- The upper forming number is attained, with its original finite maximum. -/
theorem sf_attained (G : SimpleGraph V) (k : ℕ) :
    ∃ S : Finset V, IsMinimalStarForming G k S ∧ S.card = SF G k := by
  classical
  obtain ⟨S,hS⟩ := minimalStarForming_exists G k
  have hn : (Finset.univ.powerset.filter (IsMinimalStarForming G k)).Nonempty :=
    ⟨S,Finset.mem_filter.mpr ⟨by simp,hS⟩⟩
  obtain ⟨T,hT,hcard⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨T,(Finset.mem_filter.mp hT).2,hcard.symm⟩

/-- Selected degree is computed entirely within the relevant component. -/
theorem independent_sum_iff (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) (S : Finset (V ⊕ W)) :
    IsKIndependent (G ⊕g H) k S ↔
      IsKIndependent G k S.toLeft ∧ IsKIndependent H k S.toRight := by
  classical
  have left (v : V) : (S.filter ((G ⊕g H).Adj (.inl v))).card =
      (S.toLeft.filter (G.Adj v)).card := by
    have hl : (S.filter ((G ⊕g H).Adj (.inl v))).toLeft =
        S.toLeft.filter (G.Adj v) := by ext x; simp
    have hr : (S.filter ((G ⊕g H).Adj (.inl v))).toRight = ∅ := by ext x; simp
    have hc := Finset.card_toLeft_add_card_toRight
      (u := S.filter ((G ⊕g H).Adj (.inl v)))
    rw [hl,hr,Finset.card_empty,Nat.add_zero] at hc
    exact hc.symm
  have right (v : W) : (S.filter ((G ⊕g H).Adj (.inr v))).card =
      (S.toRight.filter (H.Adj v)).card := by
    have hl : (S.filter ((G ⊕g H).Adj (.inr v))).toLeft = ∅ := by ext x; simp
    have hr : (S.filter ((G ⊕g H).Adj (.inr v))).toRight =
        S.toRight.filter (H.Adj v) := by ext x; simp
    have hc := Finset.card_toLeft_add_card_toRight
      (u := S.filter ((G ⊕g H).Adj (.inr v)))
    rw [hl,hr,Finset.card_empty,Nat.zero_add] at hc
    exact hc.symm
  constructor
  · intro h
    constructor
    · intro v hv
      rw [← left v]
      exact h (.inl v) (Finset.mem_toLeft.mp hv)
    · intro v hv
      rw [← right v]
      exact h (.inr v) (Finset.mem_toRight.mp hv)
  · rintro ⟨hl,hr⟩ (v | v) hv
    · rw [left v]
      exact hl v (Finset.mem_toLeft.mpr hv)
    · rw [right v]
      exact hr v (Finset.mem_toRight.mpr hv)

/-- The k-independence maximum is additive for disjoint finite graphs. -/
theorem beta_sum (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) :
    beta (G ⊕g H) k = beta G k + beta H k := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    have hi := (independent_sum_iff G H k S).mp (Finset.mem_filter.mp hS).2
    have hl : S.toLeft.card ≤ beta G k := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi.1⟩)
    have hr : S.toRight.card ≤ beta H k := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi.2⟩)
    rw [← Finset.card_toLeft_add_card_toRight (u := S)]
    exact Nat.add_le_add hl hr
  · obtain ⟨A,hA,hca⟩ := beta_attained G k
    obtain ⟨B,hB,hcb⟩ := beta_attained H k
    have hi : IsKIndependent (G ⊕g H) k (A.disjSum B) := by
      apply (independent_sum_iff G H k _).mpr
      simpa using And.intro hA hB
    rw [← hca,← hcb,← Finset.card_disjSum]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

/-- The upper k-star-forming maximum is additive on disjoint finite graphs. -/
theorem sf_sum (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) :
    SF (G ⊕g H) k = SF G k + SF H k := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    have hi := (minimalStarForming_sum_iff G H k S).mp (Finset.mem_filter.mp hS).2
    have hl : S.toLeft.card ≤ SF G k := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi.1⟩)
    have hr : S.toRight.card ≤ SF H k := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi.2⟩)
    rw [← Finset.card_toLeft_add_card_toRight (u := S)]
    exact Nat.add_le_add hl hr
  · obtain ⟨A,hA,hca⟩ := sf_attained G k
    obtain ⟨B,hB,hcb⟩ := sf_attained H k
    have hi : IsMinimalStarForming (G ⊕g H) k (A.disjSum B) := by
      apply (minimalStarForming_sum_iff G H k _).mpr
      simpa using And.intro hA hB
    rw [← hca,← hcb,← Finset.card_disjSum]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

end D5.S3.Combinatorics.Graph.StarForming
