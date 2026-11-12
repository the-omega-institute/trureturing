/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank
   mirror-E: none(waiver:actual-catalan-rank-succession)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Actual Catalan-pair prefixes have the Catalan rank succession rule. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanSites
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck
import Mathlib.Data.Finset.Sort

/-! The site shape is proved on actual avoiding words and retained at their
one-letter producers. It is not an assumed generating-tree predicate. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank

open OrdinaryAscentSemantics OrdinaryAscentCatalanSites
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)

/-- The last letter and the fresh bound are the two largest sites. -/
theorem sites_shape (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ []) :
    ∀ y ∈ sites w, y ≤ w.getD (w.length - 1) 0 ∨ y = asc w + 1 := by
  induction w using List.reverseRecOn with
  | nil => contradiction
  | append_singleton w x ih =>
    by_cases he : w = []
    · subst w
      have hx := hw.1 0 (by simp)
      have hx0 : x = 0 := by simpa [IsAscent] using hx
      subst x
      intro y hy
      have hb := (mem_sites _ _).mp hy
      simp only [List.nil_append, asc, List.length_singleton, Nat.sub_self,
        Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add,
        List.getD_cons_zero] at hb ⊢
      omega
    · obtain ⟨hp, hx⟩ := (catalan_append_iff w he x).mp hw
      have hlast : (w ++ [x]).getD ((w ++ [x]).length - 1) 0 = x := by simp
      intro y hy
      rw [hlast]
      have hd := (mem_sites_append w he x y).mp hy
      have hs := ih hp he x hx
      have hc := asc_append w x
      simp only [if_neg he] at hc
      by_cases hu : w.getD (w.length - 1) 0 < x
      · have hxv : x = asc w + 1 := by omega
        rw [if_pos hu] at hc
        omega
      · rw [if_neg hu, Nat.add_zero] at hc
        have hyold : y ∈ sites w := (mem_sites w y).mpr ⟨by omega, hd.2.1⟩
        have hys := ih hp he y hyold
        omega

/-- The complete site update, uniformly for descent, repetition, and fresh ascent. -/
theorem sites_append (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ [])
    (x : ℕ) (hx : x ∈ sites w) :
    sites (w ++ [x]) = insert (asc (w ++ [x]) + 1) ((sites w).filter (· ≤ x)) := by
  have hcword := (catalan_append_iff w hne x).mpr ⟨hw, hx⟩
  have hc := asc_append w x
  simp only [if_neg hne] at hc
  have hxs := sites_shape w hw hne x hx
  ext y
  constructor
  · intro hy
    by_cases hf : y = asc (w ++ [x]) + 1
    · exact Finset.mem_insert.mpr (Or.inl hf)
    · have hd := (mem_sites_append w hne x y).mp hy
      have hyb : y ≤ asc (w ++ [x]) := by omega
      have hyold : y ∈ sites w := by
        apply (mem_sites _ _).mpr
        refine ⟨?_, hd.2.1⟩
        split_ifs at hc <;> omega
      have hys := sites_shape w hw hne y hyold
      have hyx : y ≤ x := by split_ifs at hc <;> omega
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyold, hyx⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hf | hy
    · rw [hf]
      exact fresh_mem_sites _ hcword.1
    · obtain ⟨hyold, hyx⟩ := Finset.mem_filter.mp hy
      have hd := (mem_sites w y).mp hyold
      apply (mem_sites_append w hne x y).mpr
      refine ⟨?_, hd.2, Or.inl hyx⟩
      split_ifs at hc <;> omega

/-- Zero-based rank among the actual admissible letters. -/
def rank (w : List ℕ) (x : ℕ) : ℕ := ((sites w).filter (· < x)).card

/-- Appending the letter of rank `i` produces exactly `i+2` sites. -/
theorem card_sites_append (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ [])
    (x : ℕ) (hx : x ∈ sites w) :
    (sites (w ++ [x])).card = rank w x + 2 := by
  have hcword := (catalan_append_iff w hne x).mpr ⟨hw, hx⟩
  have hbound := entry_le_asc (w ++ [x]) hcword.1 w.length (by simp)
  simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
    List.getD_cons_zero] at hbound
  have hnot : asc (w ++ [x]) + 1 ∉ (sites w).filter (· ≤ x) := by
    simp only [Finset.mem_filter]
    omega
  have hfilter : (sites w).filter (· ≤ x) = insert x ((sites w).filter (· < x)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hyx⟩
      by_cases heq : y = x
      · exact Or.inl heq
      · exact Or.inr ⟨hy, by omega⟩
    · rintro (rfl | ⟨hy, hyx⟩)
      · exact ⟨hx, le_refl _⟩
      · exact ⟨hy, by omega⟩
  rw [sites_append w hw hne x hx, Finset.card_insert_of_notMem hnot, hfilter]
  have hself : x ∉ (sites w).filter (· < x) := by simp
  rw [Finset.card_insert_of_notMem hself]
  rfl

theorem rank_lt_card (w : List ℕ) (x : ℕ) (hx : x ∈ sites w) :
    rank w x < (sites w).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have : x ∈ (sites w).filter (· < x) := heq.symm ▸ hx
  simpa using this

theorem rank_strictMono (w : List ℕ) {x y : ℕ} (hx : x ∈ sites w)
    (hxy : x < y) : rank w x < rank w y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz, hzx.trans hxy⟩
  · intro heq
    have : x ∈ (sites w).filter (· < x) :=
      heq.symm ▸ Finset.mem_filter.mpr ⟨hx, hxy⟩
    simpa using this

/-- Rank and unranking are inverse on the actual set of legal appended values. -/
def rankedSites (w : List ℕ) : (sites w) ≃ Fin (sites w).card := by
  classical
  let f : (sites w) → Fin (sites w).card := fun x =>
    ⟨rank w x.val, rank_lt_card w x.val x.property⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨?_, by simp⟩
  intro x y h
  have heq : rank w x.val = rank w y.val := congrArg Fin.val h
  apply Subtype.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have := rank_strictMono w x.property hlt
    omega
  · have := rank_strictMono w y.property hgt
    omega

/-- Total unranking, with an irrelevant default outside the actual rank interval. -/
def unrank (w : List ℕ) (i : ℕ) : ℕ :=
  if hi : i < (sites w).card then ((rankedSites w).symm ⟨i, hi⟩).val else 0

theorem unrank_spec (w : List ℕ) (i : ℕ) (hi : i < (sites w).card) :
    unrank w i ∈ sites w ∧ rank w (unrank w i) = i := by
  classical
  rw [unrank, dif_pos hi]
  refine ⟨((rankedSites w).symm ⟨i, hi⟩).property, ?_⟩
  exact congrArg Fin.val ((rankedSites w).apply_symm_apply ⟨i, hi⟩)

theorem unrank_rank (w : List ℕ) (x : ℕ) (hx : x ∈ sites w) :
    unrank w (rank w x) = x := by
  have hs := unrank_spec w (rank w x) (rank_lt_card w x hx)
  have he : rankedSites w ⟨unrank w (rank w x), hs.1⟩ = rankedSites w ⟨x, hx⟩ := by
    apply Fin.ext
    exact hs.2
  exact congrArg Subtype.val ((rankedSites w).injective he)

theorem card_sites_le (w : List ℕ) (hne : w ≠ []) :
    (sites w).card ≤ w.length + 1 := by
  classical
  have hb : (sites w).card ≤ asc w + 2 :=
    (Finset.card_le_card (show sites w ⊆ Finset.range (asc w + 2) from by
      intro y hy
      have := ((mem_sites w y).mp hy).1
      exact Finset.mem_range.mpr (by omega))).trans_eq (Finset.card_range _)
  have hc := asc_le w
  have hp := List.length_pos_iff.mpr hne
  omega

theorem singleton_word (x : ℕ) : CatalanWord [x] ↔ x = 0 := by
  constructor
  · intro h
    have hx := h.1 0 (by simp)
    simpa using hx
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp
    all_goals rintro ⟨i, k, hik, hk, _⟩; simp only [List.length_singleton] at hk; omega

theorem root_sites : sites [0] = {0, 1} := by
  classical
  ext x
  rw [mem_sites]
  simp [asc]
  omega

/-- Counts of preceding downsteps for the rev3 rightmost-peak construction. -/
def eastCode (w : List ℕ) : List ℕ :=
  w.reverseRec [] (fun pre x code => code ++ [pre.length - rank pre x])

theorem eastCode_append (w : List ℕ) (x : ℕ) :
    eastCode (w ++ [x]) = eastCode w ++ [w.length - rank w x] := by
  simp [eastCode]

theorem eastCode_length (w : List ℕ) : (eastCode w).length = w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [eastCode]
  | append_singleton w x ih => simp [eastCode_append, ih]

/-- The actual avoidance invariant produces a nondecreasing inversion sequence;
its last entry records the complement of the terminal-descent label. -/
theorem eastCode_valid (w : List ℕ) (hw : CatalanWord w) :
    D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq (eastCode w) ∧
    (eastCode w).Pairwise (· ≤ ·) ∧
    (w ≠ [] → (sites w).card + (eastCode w).getLastD 0 = w.length + 1) := by
  induction w using List.reverseRecOn with
  | nil => simp [eastCode, D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq]
  | append_singleton w x ih =>
    by_cases he : w = []
    · subst w
      have hx : x = 0 := (singleton_word x).mp hw
      subst x
      have hec : eastCode [0] = [0] := by simpa [eastCode] using eastCode_append [] 0
      simp only [List.nil_append]
      rw [hec, root_sites]
      norm_num [D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq]
    · obtain ⟨hp, hx⟩ := (catalan_append_iff w he x).mp hw
      obtain ⟨hinv, hmono, hlabel⟩ := ih hp
      have hi := rank_lt_card w x hx
      have hcard := card_sites_le w he
      have hlabel := hlabel he
      have hr : rank w x ≤ w.length := by omega
      have hlast : (eastCode w).getLastD 0 ≤ w.length - rank w x := by omega
      rw [eastCode_append]
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        by_cases hjw : j < (eastCode w).length
        · rw [List.getD_append _ _ _ _ hjw]
          exact hinv j hjw
        · have hjn : j = (eastCode w).length := by
            simp only [List.length_append, List.length_singleton] at hj
            omega
          subst j
          simpa [eastCode_length] using (Nat.sub_le w.length (rank w x))
      · apply List.pairwise_append.mpr
        refine ⟨hmono, by simp, ?_⟩
        intro a ha b hb
        have hb : b = w.length - rank w x := by simpa using hb
        subst b
        have hane : eastCode w ≠ [] := List.ne_nil_of_mem ha
        have halast := hmono.rel_getLast ha
        have hget : (eastCode w).getLastD 0 = (eastCode w).getLast hane :=
          by simp [List.getLast?_eq_getLast hane]
        omega
      · intro _
        rw [card_sites_append w hp he x hx]
        simp only [List.getLastD_concat,
          List.length_append, List.length_singleton]
        omega

/-- Reconstruct letters from the actual site ranks, keeping the unique root. -/
def fromEastCode (e : List ℕ) : List ℕ :=
  e.reverseRec [] (fun pre v word =>
    if pre = [] then [0] else word ++ [unrank word (pre.length - v)])

theorem fromEastCode_append (e : List ℕ) (v : ℕ) :
    fromEastCode (e ++ [v]) =
      if e = [] then [0] else fromEastCode e ++ [unrank (fromEastCode e) (e.length - v)] := by
  simp [fromEastCode]

theorem fromEastCode_eastCode (w : List ℕ) (hw : CatalanWord w) :
    fromEastCode (eastCode w) = w := by
  induction w using List.reverseRecOn with
  | nil => simp [eastCode, fromEastCode]
  | append_singleton w x ih =>
    by_cases he : w = []
    · subst w
      have hx : x = 0 := (singleton_word x).mp hw
      subst x
      have hec : eastCode ([] ++ [0]) = [0] := by rw [eastCode_append]; simp [eastCode]
      rw [hec]
      change fromEastCode ([] ++ [0]) = [0]
      rw [fromEastCode_append]
      simp
    · obtain ⟨hp, hx⟩ := (catalan_append_iff w he x).mp hw
      have hcode : eastCode w ≠ [] := by
        intro hn
        have := eastCode_length w
        simp only [hn, List.length_nil] at this
        exact he (List.length_eq_zero_iff.mp this.symm)
      have hr : rank w x ≤ w.length := by
        have := rank_lt_card w x hx
        have := card_sites_le w he
        omega
      rw [eastCode_append, fromEastCode_append, if_neg hcode, ih hp, eastCode_length]
      rw [Nat.sub_sub_self hr, unrank_rank w x hx]

/-- The inverse preserves the actual ordinary-word predicate, and recovers every
nondecreasing inversion sequence, including the empty sequence. -/
theorem fromEastCode_valid (e : List ℕ)
    (he : D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq e)
    (hm : e.Pairwise (· ≤ ·)) :
    (fromEastCode e).length = e.length ∧ CatalanWord (fromEastCode e) ∧
    eastCode (fromEastCode e) = e := by
  induction e using List.reverseRecOn with
  | nil =>
    simp [fromEastCode, eastCode, CatalanWord, IsAscent, Contains]
  | append_singleton e v ih =>
    have hev := he e.length (by simp)
    have hv : v ≤ e.length := by simpa using hev
    by_cases he0 : e = []
    · subst e
      have hv0 : v = 0 := by simpa using hv
      subst v
      have hd : fromEastCode ([] ++ [0]) = [0] := by rw [fromEastCode_append]; simp
      simp only [List.nil_append] at hd ⊢
      rw [hd]
      refine ⟨rfl, (singleton_word 0).mpr rfl, ?_⟩
      simpa [eastCode] using eastCode_append [] 0
    · have hei : D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq e := by
        intro j hj
        have hh := he j (by simp; omega)
        rwa [List.getD_append _ _ _ _ hj] at hh
      obtain ⟨hmen, _, hcross⟩ := List.pairwise_append.mp hm
      obtain ⟨hlen, hword, hcode⟩ := ih hei hmen
      have hword0 : fromEastCode e ≠ [] := by
        intro hn
        have : e.length = 0 := by simpa [hn] using hlen.symm
        exact he0 (List.length_eq_zero_iff.mp this)
      have hlast : e.getLastD 0 ≤ v := by
        simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast he0, Option.getD_some]
        exact hcross _ (List.getLast_mem he0) v (by simp)
      have hlabel := (eastCode_valid (fromEastCode e) hword).2.2 hword0
      rw [hcode, hlen] at hlabel
      have hi : e.length - v < (sites (fromEastCode e)).card := by omega
      have hs := unrank_spec (fromEastCode e) (e.length - v) hi
      rw [fromEastCode_append, if_neg he0]
      refine ⟨by simp [hlen], ?_, ?_⟩
      · exact (catalan_append_iff _ hword0 _).mpr ⟨hword, hs.1⟩
      · rw [eastCode_append, hcode, hlen, hs.2, Nat.sub_sub_self hv]

theorem mem_catalan_avoiders (n : ℕ) (w : List ℕ) :
    w ∈ avoiders n {.p101, .p201} ↔ w.length = n ∧ CatalanWord w := by
  simp [avoiders, CatalanWord, and_assoc]

/-- The rank-complement encoding is a genuine equivalence of actual ordinary
avoiders with nondecreasing inversion sequences; it is not a proxy for avoidance. -/
def catalanMonoEquiv (n : ℕ) :
    (avoiders n {.p101, .p201}) ≃
      {e : List ℕ // e.length = n ∧
        D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq e ∧
        e.Pairwise (· ≤ ·)} where
  toFun w := ⟨eastCode w.val,
    (eastCode_length w.val).trans ((mem_catalan_avoiders n w.val).mp w.property).1,
    (eastCode_valid w.val ((mem_catalan_avoiders n w.val).mp w.property).2).1,
    (eastCode_valid w.val ((mem_catalan_avoiders n w.val).mp w.property).2).2.1⟩
  invFun e := ⟨fromEastCode e.val, (mem_catalan_avoiders n _).mpr
    ⟨((fromEastCode_valid e.val e.property.2.1 e.property.2.2).1).trans e.property.1,
    (fromEastCode_valid e.val e.property.2.1 e.property.2.2).2.1⟩⟩
  left_inv w := Subtype.ext (fromEastCode_eastCode w.val
    ((mem_catalan_avoiders n w.val).mp w.property).2)
  right_inv e := Subtype.ext (fromEastCode_valid e.val e.property.2.1 e.property.2.2).2.2

/-- The ordinary `{10-1,20-1}` avoiders correspond to actual Mathlib Dyck words. -/
def dyckEquiv (n : ℕ) : (avoiders n {.p101, .p201}) ≃
    {p : DyckWord // p.semilength = n} :=
  (catalanMonoEquiv n).trans
    (Classical.choose (D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck.monoDyckEquiv n))

theorem dyckEquiv_forward (n : ℕ) (w : avoiders n {.p101, .p201}) :
    (dyckEquiv n w).val.toList =
      D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck.dyckSteps n 0 (eastCode w.val) := by
  exact (Classical.choose_spec
    (D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck.monoDyckEquiv n)).1 _

/-- All lengths, including the empty word, have the actual Catalan cardinality. -/
theorem card_catalan_avoiders (n : ℕ) :
    (avoiders n {.p101, .p201}).ncard = catalan n := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (dyckEquiv n), Nat.card_eq_fintype_card]
  exact DyckWord.card_dyckWord_semilength_eq_catalan n

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank
