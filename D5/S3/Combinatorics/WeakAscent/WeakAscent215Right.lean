/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Right
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Right
   mirror-E: none(waiver:intrinsic-right-structure-and-numeric-children)
   anchors: []
   utility: none
   digest: Intrinsic right avoidance and exact numeric append choices for Class 215. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
import D5.S3.Combinatorics.WeakAscent.WeakAscentQuadrupleDefs
import D5.S3.Combinatorics.WeakAscent.WeakAscentGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Right

open D5.S3.Combinatorics
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs (Occurs)
open InversionSeq.InversionSeqOccurs WeakAscentDefs WeakAscentQuadrupleDefs

theorem intrinsic_right_iff (w : List ℕ) (hhead : w.getD 0 0 = 0) :
    (∀ pattern ∈ [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]],
      ¬ Occurs pattern w) ↔
    (∀ first second : ℕ, first < second → second < w.length →
      0 < w.getD first 0 → 0 < w.getD second 0 →
      w.getD first 0 ≤ w.getD second 0) ∧
    (∀ first middle last : ℕ, first < middle → middle < last → last < w.length →
      0 < w.getD first 0 → w.getD middle 0 = 0 →
      w.getD first 0 ≠ w.getD last 0) := by
  have h132 := occurs_three_iff 1 3 2 w (by omega) (by omega) (by omega)
    (by intro rank hpos hbound; norm_num at hbound; omega)
  have h212 := occurs_three_iff 2 1 2 w (by omega) (by omega) (by omega)
    (by intro rank hpos hbound; norm_num at hbound; omega)
  have h312 := occurs_three_iff 3 1 2 w (by omega) (by omega) (by omega)
    (by intro rank hpos hbound; norm_num at hbound; omega)
  have h321 := occurs_three_iff 3 2 1 w (by omega) (by omega) (by omega)
    (by intro rank hpos hbound; norm_num at hbound; omega)
  constructor
  · intro havoid
    constructor
    · intro first second hfs hs hfirst hsecond
      by_contra hdecrease
      have hindex : 0 < first := by
        by_contra hzero
        have : first = 0 := by omega
        subst first
        omega
      apply havoid [1, 3, 2] (by simp)
      apply h132.mpr
      refine ⟨0, first, second, hindex, hfs, hs, ?_⟩
      rw [hhead]
      omega
    · intro first middle last hfm hml hl hfirst hmiddle hequal
      apply havoid [2, 1, 2] (by simp)
      apply h212.mpr
      refine ⟨first, middle, last, hfm, hml, hl, ?_⟩
      rw [hmiddle, ← hequal]
      omega
  · rintro ⟨hmono, hgap⟩ pattern hpattern hoccurs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl | rfl | rfl
    · rcases h132.mp hoccurs with
        ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩
      clear h132 h212 h312 h321
      have hlt : w.getD third 0 < w.getD second 0 := by omega
      have hpos : 0 < w.getD third 0 := by omega
      have := hmono second third hst ht (by omega) hpos
      omega
    · rcases h212.mp hoccurs with
        ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩
      clear h132 h212 h312 h321
      have hlt : w.getD second 0 < w.getD first 0 := by omega
      by_cases hzero : w.getD second 0 = 0
      · exact hgap first second third hfs hst ht (by omega) hzero (heac.mp rfl)
      · have := hmono first second hfs (by omega) (by omega) (by omega)
        omega
    · rcases h312.mp hoccurs with
        ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩
      clear h132 h212 h312 h321
      have hlt : w.getD third 0 < w.getD first 0 := by omega
      have hpos : 0 < w.getD third 0 := by omega
      have := hmono first third (by omega) ht (by omega) hpos
      omega
    · rcases h321.mp hoccurs with
        ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩
      clear h132 h212 h312 h321
      have hlt : w.getD second 0 < w.getD first 0 := by omega
      have hpos : 0 < w.getD second 0 := by omega
      have := hmono first second hfs (by omega) (by omega) hpos
      omega

theorem right_append_iff (w : List ℕ) (letter : ℕ) (hnonempty : w ≠ [])
    (hparent : w ∈ avoiders w.length [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]]) :
    w ++ [letter] ∈
      avoiders (w.length + 1) [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]] ↔
    letter ≤ 1 + wasc w ∧
      (letter = 0 ∨ w.foldr max 0 < letter ∨
        letter = w.foldr max 0 ∧ 0 < w.getLast?.getD 0) := by
  classical
  obtain ⟨_, hweak, havoid⟩ := hparent
  have hlength : 0 < w.length := List.length_pos_iff.mpr hnonempty
  have hhead : w.getD 0 0 = 0 := by
    have := hweak 0 hlength
    change w.getD 0 0 ≤ 0 at this
    omega
  obtain ⟨hmono, hgap⟩ := (intrinsic_right_iff w hhead).mp havoid
  have hprefix (index : ℕ) (hi : index < w.length) :
      (w ++ [letter]).getD index 0 = w.getD index 0 :=
    List.getD_append _ _ _ _ hi
  have hnew : (w ++ [letter]).getD w.length 0 = letter := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
  have hchildhead : (w ++ [letter]).getD 0 0 = 0 :=
    (hprefix 0 hlength).trans hhead
  have hlast : w.getD (w.length - 1) 0 = w.getLast?.getD 0 := by
    rw [List.getD_eq_getElem w 0 (by omega), List.getLast?_eq_some_getLast hnonempty]
    simp only [Option.getD_some, List.getLast_eq_getElem]
  have hmax (index : ℕ) (hi : index < w.length) :
      w.getD index 0 ≤ w.foldr max 0 := by
    rw [List.getD_eq_getElem w 0 hi]
    exact List.le_max_of_le (List.getElem_mem hi) (Nat.le_refl _)
  have hattained : ∃ index : ℕ, index < w.length ∧
      w.getD index 0 = w.foldr max 0 := by
    have hmem : w.foldr max 0 ∈ w := by
      apply List.maximum_mem
      exact (List.foldr_max_of_ne_nil hnonempty).symm
    obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨index, hi, (List.getD_eq_getElem w 0 hi).trans heq⟩
  have hweak_append : IsWeakAscent (w ++ [letter]) ↔ letter ≤ 1 + wasc w := by
    constructor
    · intro hchild
      have hbound := hchild w.length (by simp)
      rw [hnew, List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hbound
      simpa only [if_neg (by omega : w.length ≠ 0)] using hbound
    · intro hbound index hi
      by_cases hindex : index < w.length
      · rw [hprefix index hindex, List.take_append_of_le_length (Nat.le_of_lt hindex)]
        exact hweak index hindex
      · have heq : index = w.length := by
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst index
        rw [hnew, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        simpa only [if_neg (by omega : w.length ≠ 0)] using hbound
  constructor
  · rintro ⟨_, hchildweak, hchildavoid⟩
    refine ⟨hweak_append.mp hchildweak, ?_⟩
    by_cases hzero : letter = 0
    · exact Or.inl hzero
    right
    have hpositive : 0 < letter := by omega
    obtain ⟨hchildmono, hchildgap⟩ :=
      (intrinsic_right_iff (w ++ [letter]) hchildhead).mp hchildavoid
    have hupper (index : ℕ) (hi : index < w.length) : w.getD index 0 ≤ letter := by
      by_cases hpos : 0 < w.getD index 0
      · have hle := hchildmono index w.length hi (by simp)
          (by rw [hprefix index hi]; exact hpos) (by rw [hnew]; exact hpositive)
        rwa [hprefix index hi, hnew] at hle
      · omega
    obtain ⟨index, hi, heq⟩ := hattained
    have hmaxle : w.foldr max 0 ≤ letter := by
      rw [← heq]
      exact hupper index hi
    by_cases hrecord : w.foldr max 0 < letter
    · exact Or.inl hrecord
    right
    have hequal : letter = w.foldr max 0 := by omega
    refine ⟨hequal, ?_⟩
    by_contra hlastzero
    have hlastzero' : w.getD (w.length - 1) 0 = 0 := by rw [hlast]; omega
    have hindex : index < w.length - 1 := by
      by_contra hnot
      have : index = w.length - 1 := by omega
      subst index
      omega
    apply hchildgap index (w.length - 1) w.length hindex (by omega) (by simp)
    · rw [hprefix index hi, heq]
      omega
    · rw [hprefix (w.length - 1) (by omega)]
      exact hlastzero'
    · rw [hprefix index hi, hnew, heq, hequal]
  · rintro ⟨hbound, hchoice⟩
    refine ⟨by simp, hweak_append.mpr hbound, ?_⟩
    apply (intrinsic_right_iff (w ++ [letter]) hchildhead).mpr
    constructor
    · intro first second hfs hs hfirst hsecond
      have hfirstindex : first < w.length := by
        simp only [List.length_append, List.length_singleton] at hs
        omega
      by_cases hsecondindex : second < w.length
      · rw [hprefix first hfirstindex] at hfirst
        rw [hprefix second hsecondindex] at hsecond
        rw [hprefix first hfirstindex, hprefix second hsecondindex]
        exact hmono first second hfs hsecondindex hfirst hsecond
      · have hsecondlast : second = w.length := by
          simp only [List.length_append, List.length_singleton] at hs
          omega
        subst second
        rw [hprefix first hfirstindex, hnew]
        rw [hnew] at hsecond
        have hle := hmax first hfirstindex
        rcases hchoice with hzero | hrecord | ⟨hequal, _⟩ <;> omega
    · intro first middle last hfm hml hl hfirst hmiddle hequal
      have hmiddleindex : middle < w.length := by
        simp only [List.length_append, List.length_singleton] at hl
        omega
      have hfirstindex : first < w.length := by omega
      rw [hprefix first hfirstindex] at hfirst
      rw [hprefix middle hmiddleindex] at hmiddle
      by_cases hlastindex : last < w.length
      · rw [hprefix first hfirstindex, hprefix last hlastindex] at hequal
        exact hgap first middle last hfm hml hlastindex hfirst hmiddle hequal
      · have hlastnew : last = w.length := by
          simp only [List.length_append, List.length_singleton] at hl
          omega
        subst last
        rw [hprefix first hfirstindex, hnew] at hequal
        have hfirstmax := hmax first hfirstindex
        rcases hchoice with hzero | hrecord | ⟨hrepeat, hlastpositive⟩
        · omega
        · omega
        · have hmiddlelast : middle < w.length - 1 := by
            by_contra hnot
            have : middle = w.length - 1 := by omega
            subst middle
            rw [hlast] at hmiddle
            omega
          have hlastpos : 0 < w.getD (w.length - 1) 0 := by
            rw [hlast]
            exact hlastpositive
          have hle := hmono first (w.length - 1) (by omega) (by omega) hfirst hlastpos
          have hlastmax := hmax (w.length - 1) (by omega)
          apply hgap first middle (w.length - 1) hfm hmiddlelast (by omega) hfirst hmiddle
          omega

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Right
