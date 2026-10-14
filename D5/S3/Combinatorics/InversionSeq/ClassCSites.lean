/- GID: D5/S3/Combinatorics/InversionSeq/ClassCSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/ClassCSites
   mirror-E: none(waiver:structural-inversion-sequence-site-characterization)
   anchors: [mathlib/module/Mathlib.Data.List.MinMax]
   utility: none
   digest: Exact append exclusions and admissible-value updates for class C. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.ClassCSites

open D5.S3.Combinatorics Nonnesting InversionSeqOccurs

/-- Pattern ranks shift by one; inversion-sequence entries do not shift. -/
def patterns : List (List ℕ) := [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 2, 1]]

abbrev Avoids (w : List ℕ) : Prop := ∀ σ ∈ patterns, ¬ NonnestingDefs.Occurs σ w

/-- Safety excludes forbidden patterns, independently of the inversion bound. -/
def Safe (w : List ℕ) (x : ℕ) : Prop := Avoids (w ++ [x])

def ForbiddenTriple (a b x : ℕ) : Prop :=
  (b < a ∧ (x ≤ b ∨ x = a)) ∨ (a = b ∧ x < a)

def maximum (w : List ℕ) : ℕ := w.foldr max 0

private theorem forbidden_iff (w : List ℕ) :
    (∃ σ ∈ patterns, NonnestingDefs.Occurs σ w) ↔
      ∃ i j k : ℕ, i < j ∧ j < k ∧ k < w.length ∧
        ForbiddenTriple (w.getD i 0) (w.getD j 0) (w.getD k 0) := by
  have h211 := occurs_three_iff 2 1 1 w (by omega) (by omega) (by omega)
    (by intro rank hlo hhi; simp at hhi; omega)
  have h212 := occurs_three_iff 2 1 2 w (by omega) (by omega) (by omega)
    (by intro rank hlo hhi; simp at hhi; omega)
  have h221 := occurs_three_iff 2 2 1 w (by omega) (by omega) (by omega)
    (by intro rank hlo hhi; simp at hhi; omega)
  have h321 := occurs_three_iff 3 2 1 w (by omega) (by omega) (by omega)
    (by intro rank hlo hhi; simp at hhi; omega)
  constructor
  · rintro ⟨σ, hσ, ho⟩
    simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · obtain ⟨i, j, k, hij, hjk, hk, hr⟩ := h211.mp ho
      refine ⟨i, j, k, hij, hjk, hk, ?_⟩
      norm_num only [true_iff, false_iff] at hr
      clear h211 h212 h221 h321 ho
      dsimp [ForbiddenTriple]
      omega
    · obtain ⟨i, j, k, hij, hjk, hk, hr⟩ := h212.mp ho
      refine ⟨i, j, k, hij, hjk, hk, ?_⟩
      norm_num only [true_iff, false_iff] at hr
      clear h211 h212 h221 h321 ho
      dsimp [ForbiddenTriple]
      omega
    · obtain ⟨i, j, k, hij, hjk, hk, hr⟩ := h221.mp ho
      refine ⟨i, j, k, hij, hjk, hk, ?_⟩
      norm_num only [true_iff, false_iff] at hr
      clear h211 h212 h221 h321 ho
      dsimp [ForbiddenTriple]
      omega
    · obtain ⟨i, j, k, hij, hjk, hk, hr⟩ := h321.mp ho
      refine ⟨i, j, k, hij, hjk, hk, ?_⟩
      norm_num only [true_iff, false_iff] at hr
      clear h211 h212 h221 h321 ho
      dsimp [ForbiddenTriple]
      omega
  · rintro ⟨i, j, k, hij, hjk, hk, hbad⟩
    rcases hbad with ⟨hba, hx⟩ | ⟨hab, hx⟩
    · rcases hx with hxb | hxa
      · rcases lt_or_eq_of_le hxb with hxb | hxb
        · refine ⟨[3, 2, 1], by simp [patterns], h321.mpr ?_⟩
          refine ⟨i, j, k, hij, hjk, hk, ?_⟩
          norm_num only [true_iff, false_iff]; clear h211 h212 h221 h321; omega
        · refine ⟨[2, 1, 1], by simp [patterns], h211.mpr ?_⟩
          refine ⟨i, j, k, hij, hjk, hk, ?_⟩
          norm_num only [true_iff, false_iff]; clear h211 h212 h221 h321; omega
      · refine ⟨[2, 1, 2], by simp [patterns], h212.mpr ?_⟩
        refine ⟨i, j, k, hij, hjk, hk, ?_⟩
        norm_num only [true_iff, false_iff]; clear h211 h212 h221 h321; omega
    · refine ⟨[2, 2, 1], by simp [patterns], h221.mpr ?_⟩
      refine ⟨i, j, k, hij, hjk, hk, ?_⟩
      norm_num only [true_iff, false_iff]; clear h211 h212 h221 h321; omega

private theorem avoids_iff (w : List ℕ) : Avoids w ↔
    ∀ i j k : ℕ, i < j → j < k → k < w.length →
      ¬ ForbiddenTriple (w.getD i 0) (w.getD j 0) (w.getD k 0) := by
  have := not_congr (forbidden_iff w)
  simpa only [Avoids, not_exists, not_and, not_not] using this

/-- Each forbidden occurrence created by append ends at the appended position. -/
theorem safe_append_iff (w : List ℕ) (x : ℕ) : Safe w x ↔
    Avoids w ∧ ∀ i j : ℕ, i < j → j < w.length →
      ¬ ForbiddenTriple (w.getD i 0) (w.getD j 0) x := by
  rw [Safe, avoids_iff]
  constructor
  · intro h
    constructor
    · apply (avoids_iff w).mpr
      intro i j k hij hjk hk
      have ht := h i j k hij hjk (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.getD_append w [x] 0 i (by omega),
        List.getD_append w [x] 0 j (by omega), List.getD_append w [x] 0 k hk] using ht
    · intro i j hij hj
      have ht := h i j w.length hij hj (by simp)
      simpa only [List.getD_append w [x] 0 i (by omega), List.getD_append w [x] 0 j hj,
        List.getD_append_right w [x] 0 w.length (le_refl _), Nat.sub_self, List.getD_cons_zero] using ht
  · rintro ⟨havoid, hpairs⟩ i j k hij hjk hk
    have hlen : k ≤ w.length := by
      simp only [List.length_append, List.length_singleton] at hk
      omega
    rcases lt_or_eq_of_le hlen with hlt | rfl
    · have ht := (avoids_iff w).mp havoid i j k hij hjk hlt
      simpa only [List.getD_append w [x] 0 i (by omega),
        List.getD_append w [x] 0 j (by omega), List.getD_append w [x] 0 k hlt] using ht
    · simpa only [List.getD_append w [x] 0 i (by omega),
        List.getD_append w [x] 0 j hjk,
        List.getD_append_right w [x] 0 w.length (le_refl _), Nat.sub_self, List.getD_cons_zero] using hpairs i j hij hjk

private theorem getD_mem (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    w.getD i 0 ∈ w := by
  rw [List.getD_eq_getElem w 0 hi]
  exact List.getElem_mem hi

private theorem mem_getD (w : List ℕ) (a : ℕ) (ha : a ∈ w) :
    ∃ i, i < w.length ∧ w.getD i 0 = a := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
  exact ⟨i, hi, by simpa only [List.getD_eq_getElem w 0 hi] using heq⟩

private theorem safe_update_pairs (w : List ℕ) (x y : ℕ) (hx : Safe w x) :
    Safe (w ++ [x]) y ↔ Safe w y ∧ ∀ a ∈ w, ¬ ForbiddenTriple a x y := by
  have hw := (safe_append_iff w x).mp hx
  rw [safe_append_iff]
  constructor
  · rintro ⟨_, h⟩
    constructor
    · apply (safe_append_iff w y).mpr
      refine ⟨hw.1, ?_⟩
      intro i j hij hj
      have ht := h i j hij (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.getD_append w [x] 0 i (by omega),
        List.getD_append w [x] 0 j hj] using ht
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := mem_getD w a ha
      have ht := h i w.length hi (by simp)
      simpa only [List.getD_append w [x] 0 i hi,
        List.getD_append_right w [x] 0 w.length (le_refl _), Nat.sub_self, List.getD_cons_zero] using ht
  · rintro ⟨hy, hnew⟩
    refine ⟨hx, ?_⟩
    intro i j hij hj
    have hlen : j ≤ w.length := by
      simp only [List.length_append, List.length_singleton] at hj
      omega
    rcases lt_or_eq_of_le hlen with hlt | rfl
    · have ht := (safe_append_iff w y).mp hy |>.2 i j hij hlt
      simpa only [List.getD_append w [x] 0 i (by omega),
        List.getD_append w [x] 0 j hlt] using ht
    · simpa only [List.getD_append w [x] 0 i hij,
        List.getD_append_right w [x] 0 w.length (le_refl _), Nat.sub_self, List.getD_cons_zero] using
        hnew (w.getD i 0) (getD_mem w i hij)

private theorem maximum_mem (w : List ℕ) (hw : w ≠ []) : maximum w ∈ w := by
  induction w with
  | nil => contradiction
  | cons a w ih =>
    by_cases he : w = []
    · simp [maximum, he]
    · have ht := ih he
      change max a (maximum w) ∈ a :: w
      rcases le_total a (maximum w) with h | h
      · simpa [max_eq_right h] using List.mem_cons_of_mem a ht
      · simp [max_eq_left h]

private theorem le_maximum (w : List ℕ) (a : ℕ) (ha : a ∈ w) : a ≤ maximum w :=
  List.le_max_of_le ha (le_refl a)

/-- A legal safe append preserves old exclusions and has exactly these new exclusions. -/
theorem safe_update (w : List ℕ) (x y : ℕ) (hw : w ≠ []) (hx : Safe w x) :
    Safe (w ++ [x]) y ↔ Safe w y ∧
      (if x < maximum w then x < y ∧ y ∉ w
       else if x = maximum w then maximum w ≤ y else True) := by
  rw [safe_update_pairs w x y hx]
  have hm := maximum_mem w hw
  by_cases hlt : x < maximum w
  · simp only [hlt, if_true]
    apply and_congr_right
    intro _
    constructor
    · intro h
      have ht := h (maximum w) hm
      have hy : x < y := by simp only [ForbiddenTriple] at ht; omega
      refine ⟨hy, ?_⟩
      intro hym
      have ht := h y hym
      dsimp [ForbiddenTriple] at ht
      omega
    · rintro ⟨hy, hyn⟩ a ha hbad
      simp only [ForbiddenTriple] at hbad
      rcases hbad with ⟨hax, hyy | hya⟩ | ⟨hax, hya⟩
      · omega
      · exact hyn (hya ▸ ha)
      · omega
  · by_cases heq : x = maximum w
    · rw [if_neg hlt, if_pos heq]
      subst x
      apply and_congr_right
      intro _
      constructor
      · intro h
        have ht := h (maximum w) hm
        dsimp [ForbiddenTriple] at ht
        omega
      · intro hy a ha hbad
        have hle := le_maximum w a ha
        dsimp [ForbiddenTriple] at hbad
        omega
    · simp only [hlt, heq, if_false, and_true]
      apply and_iff_left_of_imp
      intro _ a ha hbad
      have hle := le_maximum w a ha
      simp only [ForbiddenTriple] at hbad
      omega

private theorem safe_newmax (w : List ℕ) (x : ℕ) (hw : Avoids w)
    (hx : maximum w < x) : Safe w x := by
  apply (safe_append_iff w x).mpr
  refine ⟨hw, ?_⟩
  intro i j hij hj hbad
  have hi := le_maximum w (w.getD i 0) (getD_mem w i (by omega))
  have hj' := le_maximum w (w.getD j 0) (getD_mem w j hj)
  dsimp [ForbiddenTriple] at hbad
  omega

private theorem maximum_append (w : List ℕ) (x : ℕ) :
    maximum (w ++ [x]) = max (maximum w) x := by
  induction w with
  | nil => simp [maximum]
  | cons a w ih =>
    simpa only [maximum, List.cons_append, List.foldr, max_assoc] using (congrArg (max a) ih)

/-- Old admissible values retain their numeric identities before site labels are forgotten. -/
noncomputable def admissible (w : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (maximum w + 1)).filter (Safe w)

noncomputable def values (w : List ℕ) : List ℕ := (admissible w).sort (· ≤ ·)

inductive Site where
  | U
  | S
  deriving DecidableEq

noncomputable def label (w : List ℕ) (a : ℕ) : Site := by
  classical
  exact if a ∈ w then .S else .U

noncomputable def siteWord (w : List ℕ) : List Site := (values w).map (label w)

private theorem mem_values (w : List ℕ) (a : ℕ) :
    a ∈ values w ↔ a ≤ maximum w ∧ Safe w a := by
  classical
  simp only [values, Finset.mem_sort, admissible, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private theorem values_sorted (w : List ℕ) : (values w).SortedLT :=
  Finset.sortedLT_sort _

private theorem mem_range'_1 (start size a : ℕ) :
    a ∈ List.range' start size ↔ start ≤ a ∧ a < start + size := by
  rw [List.mem_range']
  simp only [Nat.one_mul]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨a - start, by omega, by omega⟩

private theorem values_lower (w : List ℕ) (x : ℕ) (hw : w ≠ [])
    (hx : Safe w x) (hlt : x < maximum w) :
    values (w ++ [x]) = (values w).filter (fun a => decide (x < a ∧ a ∉ w)) := by
  classical
  apply List.SortedLT.eq_of_mem_iff (values_sorted _) ((values_sorted w).pairwise.filter _).sortedLT
  intro a
  simp only [mem_values, List.mem_filter, decide_eq_true_eq]
  rw [maximum_append, max_eq_left (by omega), safe_update w x a hw hx, if_pos hlt]
  tauto

private theorem values_repeat (w : List ℕ) (hw : w ≠ []) (hx : Safe w (maximum w)) :
    values (w ++ [maximum w]) = [maximum w] := by
  apply List.SortedLT.eq_of_mem_iff (values_sorted _) (by rw [List.sortedLT_iff_pairwise]; simp)
  intro a
  rw [mem_values, maximum_append, max_self,
    safe_update w (maximum w) a hw hx]
  simp only [lt_self_iff_false, if_false, if_true, List.mem_singleton]
  constructor
  · rintro ⟨hle, _, hge⟩
    omega
  · rintro rfl
    exact ⟨le_refl _, hx, le_refl _⟩

private theorem values_newmax (w : List ℕ) (x : ℕ) (hw : w ≠ [])
    (hx : Safe w x) (hlt : maximum w < x) :
    values (w ++ [x]) = values w ++ List.range' (maximum w + 1) (x - maximum w) := by
  apply List.SortedLT.eq_of_mem_iff (values_sorted _)
  · rw [List.sortedLT_iff_pairwise]
    apply List.pairwise_append.mpr
    refine ⟨(values_sorted w).pairwise, (List.sortedLT_range' _ _ (by omega)).pairwise, ?_⟩
    intro a ha b hb
    have hma := (mem_values w a).mp ha
    have hmb := (mem_range'_1 _ _ _).mp hb
    omega
  · intro a
    rw [mem_values, maximum_append, max_eq_right (by omega),
      safe_update w x a hw hx]
    simp only [show ¬ x < maximum w by omega, show ¬ x = maximum w by omega,
      if_false, and_true, List.mem_append, mem_values, mem_range'_1]
    constructor
    · rintro ⟨hle, hsafe⟩
      by_cases hm : a ≤ maximum w
      · exact Or.inl ⟨hm, hsafe⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rintro (⟨hle, hsafe⟩ | ⟨hlo, hhi⟩)
      · exact ⟨by omega, hsafe⟩
      · exact ⟨by omega, safe_newmax w a ((safe_append_iff w x).mp hx).1 (by omega)⟩

private theorem label_lower (w : List ℕ) (x : ℕ) (a : ℕ)
    (ha : x < a ∧ a ∉ w) : label (w ++ [x]) a = .U := by
  classical
  simp only [label, List.mem_append, List.mem_singleton]
  simp only [ha.2, show a ≠ x by omega, or_self, if_false]

/-- The full sorted site word after each append, before any identification of equal children. -/
theorem site_word_succession (w : List ℕ) (x : ℕ) (hw : w ≠ []) (hx : Safe w x) :
    (x < maximum w → siteWord (w ++ [x]) =
      List.replicate ((values w).filter (fun a => decide (x < a ∧ a ∉ w))).length .U) ∧
    (x = maximum w → siteWord (w ++ [x]) = [.S]) ∧
    (maximum w < x → siteWord (w ++ [x]) =
      siteWord w ++ List.replicate (x - maximum w - 1) .U ++ [.S]) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    rw [siteWord, values_lower w x hw hx hlt]
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact label_lower w x v ((List.mem_filter.mp hv).2 |> of_decide_eq_true)
  · rintro rfl
    rw [siteWord, values_repeat w hw hx]
    simp [label]
  · intro hlt
    rw [siteWord, values_newmax w x hw hx hlt, List.map_append]
    have hlen : x - maximum w = (x - maximum w - 1) + 1 := by omega
    have hsplit := List.range'_1_concat (s := maximum w + 1) (n := x - maximum w - 1)
    rw [← hlen] at hsplit
    rw [hsplit, List.map_append]
    have hlast : maximum w + 1 + (x - maximum w - 1) = x := by omega
    rw [hlast]
    have hmap : (List.range' (maximum w + 1) (x - maximum w - 1)).map
        (label (w ++ [x])) = List.replicate (x - maximum w - 1) .U := by
      apply List.eq_replicate_iff.mpr
      refine ⟨by simp, ?_⟩
      intro a ha
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      have hb := (mem_range'_1 _ _ _).mp hv
      have hnot : v ∉ w := by
        intro hvw
        have := le_maximum w v hvw
        omega
      have hnotx : v ≠ x := by
        rcases hb with ⟨hlo, hhi⟩
        omega
      simp only [label, List.mem_append, List.mem_singleton, hnot, hnotx, or_self, if_false]
    rw [hmap]
    have hold : (values w).map (label (w ++ [x])) = siteWord w := by
      apply List.map_congr_left
      intro a ha
      have hb := (mem_values w a).mp ha
      simp only [label, List.mem_append, List.mem_singleton]
      simp only [show a ≠ x by have := hb.1; omega, or_false]
    rw [hold]
    simp [label]

abbrev Legal (w : List ℕ) := {x : ℕ // x ≤ w.length ∧ Safe w x}

abbrev Choice (w : List ℕ) := Fin (values w).length ⊕ Fin (w.length - maximum w)

/-- The inverse numeric correspondence retains every old position and every new maximum. -/
noncomputable def choiceValue (w : List ℕ) : Choice w → ℕ
  | .inl i => (values w).get i
  | .inr j => maximum w + j.val + 1

private theorem maximum_lt_length (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) : maximum w < w.length := by
  obtain ⟨i, hi, hval⟩ := mem_getD w (maximum w) (maximum_mem w hw)
  have hb := hinv i hi
  omega

private theorem choice_legal (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) (havoid : Avoids w) (c : Choice w) :
    choiceValue w c ≤ w.length ∧ Safe w (choiceValue w c) := by
  have hm := maximum_lt_length w hw hinv
  cases c with
  | inl i =>
    have ha := (mem_values w _).mp (List.get_mem (values w) i)
    exact ⟨by change (values w).get i ≤ w.length; have := ha.1; omega, ha.2⟩
  | inr j =>
    have hj := j.is_lt
    exact ⟨by dsimp [choiceValue]; omega, safe_newmax w _ havoid (by simp [choiceValue])⟩

private theorem choice_injective (w : List ℕ) : Function.Injective (choiceValue w) := by
  intro c d heq
  have hnd : (values w).Nodup := Finset.sort_nodup _ _
  cases c with
  | inl i =>
    have hi := (mem_values w _).mp (List.get_mem (values w) i)
    cases d with
    | inl j => exact congrArg Sum.inl (hnd.injective_get heq)
    | inr j =>
      change (values w).get i = maximum w + j.val + 1 at heq
      have hb := hi.1
      omega
  | inr i =>
    cases d with
    | inl j =>
      have hj := (mem_values w _).mp (List.get_mem (values w) j)
      change maximum w + i.val + 1 = (values w).get j at heq
      have hb := hj.1
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      change maximum w + i.val + 1 = maximum w + j.val + 1 at heq
      omega

/-- Legal numeric appends correspond bijectively to the labelled old and new choices. -/
noncomputable def choiceEquiv (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) (havoid : Avoids w) : Choice w ≃ Legal w := by
  classical
  let choose : Choice w → Legal w := fun c => ⟨choiceValue w c, choice_legal w hw hinv havoid c⟩
  apply Equiv.ofBijective choose
  constructor
  · intro c d heq
    exact choice_injective w (congrArg Subtype.val heq)
  · intro x
    by_cases hx : x.val ≤ maximum w
    · have hv : x.val ∈ values w := (mem_values w _).mpr ⟨hx, x.property.2⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      exact ⟨.inl i, Subtype.ext hi⟩
    · let j : Fin (w.length - maximum w) := ⟨x.val - maximum w - 1, by
        have hm := maximum_lt_length w hw hinv
        have hb := x.property.1
        omega⟩
      refine ⟨.inr j, Subtype.ext ?_⟩
      dsimp [choose, choiceValue, j]
      omega

private theorem filter_gt_getD (l : List ℕ) (hs : l.Pairwise (· < ·))
    (i : ℕ) (hi : i < l.length) :
    l.filter (fun a => decide (l.getD i 0 < a)) = l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, lt_self_iff_false, decide_false,
        List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true,
        Nat.zero_add, List.drop_succ_cons, List.drop_zero]
      apply List.filter_eq_self.mpr
      intro b hb
      exact of_decide_eq_true (by simpa using hhead b hb)
    | succ i =>
      have hil : i < l.length := by simpa using hi
      have hmem := getD_mem l i hil
      have hlt := hhead (l.getD i 0) hmem
      simp only [List.getD_cons_succ, List.filter_cons]
      rw [if_neg (by simpa using (show ¬ l.getD i 0 < a by omega))]
      simpa only [List.drop_succ_cons] using ih htail i hil

private theorem unused_right (w : List ℕ) (i : Fin (values w).length) :
    ((values w).filter (fun a => decide ((values w).get i < a ∧ a ∉ w))).length =
      ((siteWord w).drop (i.val + 1)).count .U := by
  classical
  have hdrop := filter_gt_getD (values w) (values_sorted w).pairwise i.val i.is_lt
  rw [List.getD_eq_get] at hdrop
  rw [siteWord, ← List.map_drop, List.count, List.countP_map, List.countP_eq_length_filter]
  rw [← hdrop, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  by_cases hm : a ∈ w <;> simp [label, hm, Bool.and_comm]

private theorem sorted_last (l : List ℕ) (hs : l.Pairwise (· < ·)) (M : ℕ)
    (hm : M ∈ l) (hbound : ∀ a ∈ l, a ≤ M) : ∃ q, l = q ++ [M] := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hm with heq | hmem
    · subst a
      have he : l = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro b hb
        have hlt := hhead b hb
        have hle := hbound b (List.mem_cons_of_mem _ hb)
        omega
      exact ⟨[], by simp [he]⟩
    · obtain ⟨q, hq⟩ := ih htail hmem (fun b hb => hbound b (List.mem_cons_of_mem _ hb))
      exact ⟨a :: q, by simp [hq]⟩

/-- Coherent formal states include words that are not realized by actual prefixes. -/
@[ext] structure State where
  p : List Site
  s : ℕ
  hs : 1 ≤ s
  h : Bool
  coherent : h = true → ∃ q, p = q ++ [.S]

noncomputable def stateOf (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) : State := by
  classical
  exact {
    p := siteWord w
    s := w.length - maximum w
    hs := by have := maximum_lt_length w hw hinv; omega
    h := decide (Safe w (maximum w))
    coherent := by
      classical
      intro hh
      have hs : Safe w (maximum w) := of_decide_eq_true hh
      have hm : maximum w ∈ values w := (mem_values w _).mpr ⟨le_refl _, hs⟩
      obtain ⟨q, hq⟩ := sorted_last (values w) (values_sorted w).pairwise (maximum w) hm
        (fun a ha => ((mem_values w a).mp ha).1)
      refine ⟨q.map (label w), ?_⟩
      simp [siteWord, hq, label, maximum_mem w hw] }

abbrev StateChoice (q : State) := Fin q.p.length ⊕ Fin q.s

def lowerState (k s : ℕ) (hs : 1 ≤ s) : State :=
  ⟨List.replicate k .U, s, hs, false, by simp⟩

def repeatState (s : ℕ) (hs : 1 ≤ s) : State :=
  ⟨[.S], s, hs, true, fun _ => ⟨[], rfl⟩⟩

def child (q : State) : StateChoice q → State
  | .inl i =>
    if q.h = true ∧ i.val + 1 = q.p.length then repeatState (q.s + 1) (by omega)
    else lowerState ((q.p.drop (i.val + 1)).count .U) (q.s + 1) (by omega)
  | .inr j =>
    ⟨q.p ++ List.replicate j.val .U ++ [.S], q.s - j.val, by have := j.is_lt; omega,
      true, fun _ => ⟨q.p ++ List.replicate j.val .U, rfl⟩⟩

noncomputable def liftChoice (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) : Choice w ≃ StateChoice (stateOf w hw hinv) where
  toFun
    | .inl i => .inl ⟨i.val, by simpa [stateOf, siteWord] using i.is_lt⟩
    | .inr j => .inr j
  invFun
    | .inl i => .inl ⟨i.val, by simpa [stateOf, siteWord] using i.is_lt⟩
    | .inr j => .inr j
  left_inv := by rintro (i | j) <;> rfl
  right_inv := by rintro (i | j) <;> rfl

private theorem inversion_append (w : List ℕ) (x : ℕ)
    (hinv : InversionSeqDefs.IsInversionSeq w) (hx : x ≤ w.length) :
    InversionSeqDefs.IsInversionSeq (w ++ [x]) := by
  intro i hi
  by_cases hlo : i < w.length
  · rw [List.getD_append w [x] 0 i hlo]
    exact hinv i hlo
  · have heq : i = w.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa only [List.getD_append_right w [x] 0 w.length (le_refl _),
      Nat.sub_self, List.getD_cons_zero] using hx

private theorem old_repeat_iff (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) (i : Fin (values w).length) :
    ((stateOf w hw hinv).h = true ∧ i.val + 1 = (siteWord w).length) ↔
      (values w).get i = maximum w := by
  classical
  have hi := (mem_values w _).mp (List.get_mem (values w) i)
  constructor
  · rintro ⟨hflag, hlast⟩
    have hsafe : Safe w (maximum w) := of_decide_eq_true hflag
    have hm := (mem_values w _).mpr ⟨le_refl _, hsafe⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    have hlen : i.val + 1 = (values w).length := by simpa [siteWord] using hlast
    by_cases heq : i = j
    · simpa [heq] using hj
    · have hlt : j < i := by have := j.is_lt; change j.val < i.val; omega
      have hstrict := values_sorted w hlt
      rw [hj] at hstrict
      have hbound := hi.1
      omega
  · intro heq
    refine ⟨by simpa only [stateOf, heq, decide_eq_true_eq] using hi.2, ?_⟩
    have hlen : i.val + 1 = (values w).length := by
      by_contra hne
      have hnext : i.val + 1 < (values w).length := by have := i.is_lt; omega
      let j : Fin (values w).length := ⟨i.val + 1, hnext⟩
      have hstrict := values_sorted w (show i < j by change i.val < i.val + 1; omega)
      have hbound := ((mem_values w _).mp (List.get_mem (values w) j)).1
      rw [heq] at hstrict
      omega
    simpa [siteWord] using hlen

/-- The sorted actual state follows the complete formal transition at every numeric choice. -/
theorem native_succession (w : List ℕ) (hw : w ≠ [])
    (hinv : InversionSeqDefs.IsInversionSeq w) (havoid : Avoids w) (c : Choice w) :
    stateOf (w ++ [choiceValue w c]) (by simp)
      (inversion_append w _ hinv (choice_legal w hw hinv havoid c).1) =
      child (stateOf w hw hinv) (liftChoice w hw hinv c) := by
  classical
  have hx := choice_legal w hw hinv havoid c
  have hm := maximum_lt_length w hw hinv
  cases c with
  | inl i =>
    change (values w).get i ≤ w.length ∧ Safe w ((values w).get i) at hx
    have hv := ((mem_values w _).mp (List.get_mem (values w) i)).1
    have hrepeat := old_repeat_iff w hw hinv i
    by_cases heq : (values w).get i = maximum w
    · have hr := hrepeat.mpr heq
      have hc : child (stateOf w hw hinv) (liftChoice w hw hinv (.inl i)) =
          repeatState ((stateOf w hw hinv).s + 1) (by omega) := by
        change (if _ then _ else _) = _
        simp only [Fin.val_mk, show (stateOf w hw hinv).p = siteWord w from rfl, if_pos hr]
      rw [hc]
      have hs := (site_word_succession w _ hw hx.2).2.1 heq
      have hsafety : Safe (w ++ [(values w).get i]) (maximum w) := by
        rw [safe_update w _ _ hw hx.2, heq]
        simpa only [lt_self_iff_false, if_false, if_true, le_refl, and_true, heq] using hx.2
      apply State.ext
      · exact hs
      · change (w ++ [(values w).get i]).length - maximum (w ++ [(values w).get i]) =
          w.length - maximum w + 1
        rw [maximum_append, heq, max_self]
        simp only [List.length_append, List.length_singleton]
        omega
      · change decide (Safe (w ++ [(values w).get i])
          (maximum (w ++ [(values w).get i]))) = true
        rw [maximum_append, heq, max_self]
        simpa only [heq, decide_eq_true_eq] using hsafety
    · have hlt : (values w).get i < maximum w := by omega
      have hr := hrepeat.not.mpr heq
      have hc : child (stateOf w hw hinv) (liftChoice w hw hinv (.inl i)) =
          lowerState (((siteWord w).drop (i.val + 1)).count .U)
            ((stateOf w hw hinv).s + 1) (by omega) := by
        change (if _ then _ else _) = _
        simp only [Fin.val_mk, show (stateOf w hw hinv).p = siteWord w from rfl, if_neg hr]
      rw [hc]
      have hs := (site_word_succession w _ hw hx.2).1 hlt
      rw [unused_right w i] at hs
      have hsafety : ¬ Safe (w ++ [(values w).get i]) (maximum w) := by
        rw [safe_update w _ _ hw hx.2, if_pos hlt]
        intro h
        exact h.2.2 (maximum_mem w hw)
      apply State.ext
      · exact hs
      · change (w ++ [(values w).get i]).length - maximum (w ++ [(values w).get i]) =
          w.length - maximum w + 1
        rw [maximum_append, max_eq_left hv]
        simp only [List.length_append, List.length_singleton]
        omega
      · change decide (Safe (w ++ [(values w).get i])
          (maximum (w ++ [(values w).get i]))) = false
        rw [maximum_append, max_eq_left hv]
        exact decide_eq_false hsafety
  | inr j =>
    change maximum w + j.val + 1 ≤ w.length ∧ Safe w (maximum w + j.val + 1) at hx
    have hlt : maximum w < maximum w + j.val + 1 := by omega
    have hs := (site_word_succession w (maximum w + j.val + 1) hw hx.2).2.2 hlt
    have hsafety : Safe (w ++ [maximum w + j.val + 1]) (maximum w + j.val + 1) := by
      rw [safe_update w _ _ hw hx.2]
      simp only [show ¬ maximum w + j.val + 1 < maximum w by omega,
        show ¬ maximum w + j.val + 1 = maximum w by omega, if_false, and_true]
      exact hx.2
    apply State.ext
    · change siteWord (w ++ [maximum w + j.val + 1]) =
        siteWord w ++ List.replicate j.val .U ++ [.S]
      simpa only [show maximum w + j.val + 1 - maximum w - 1 = j.val by omega] using hs
    · change (w ++ [maximum w + j.val + 1]).length -
        maximum (w ++ [maximum w + j.val + 1]) = (w.length - maximum w) - j.val
      rw [maximum_append, max_eq_right (by omega)]
      simp only [List.length_append, List.length_singleton]
      have hj := j.is_lt
      omega
    · change decide (Safe (w ++ [maximum w + j.val + 1])
        (maximum (w ++ [maximum w + j.val + 1]))) = true
      rw [maximum_append, max_eq_right (by omega)]
      exact decide_eq_true hsafety

/-- Native nonempty valid prefixes carry the hypotheses needed for every further append. -/
structure Prefix where
  word : List ℕ
  nonempty : word ≠ []
  inversion : InversionSeqDefs.IsInversionSeq word
  avoidance : Avoids word

noncomputable def Prefix.state (q : Prefix) : State := stateOf q.word q.nonempty q.inversion

def Prefix.append (q : Prefix) (x : Legal q.word) : Prefix :=
  ⟨q.word ++ [x.val], by simp, inversion_append q.word x.val q.inversion x.property.1,
    x.property.2⟩

end D5.S3.Combinatorics.InversionSeq.ClassCSites
