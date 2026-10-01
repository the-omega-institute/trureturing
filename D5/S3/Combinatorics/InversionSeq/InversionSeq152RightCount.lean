/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152RightCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152RightCount
   mirror-E: none(waiver:last-zero-counting-bijection)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution]
   utility: none
   digest: The last-zero bijection and locally finite specialization enumerate right avoiders. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Right
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Prefix
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck
import D5.S3.Combinatorics.InversionSeq.InversionSeq152FinalSeries
import D5.S3.Combinatorics.InversionSeq.InversionSeq152SuffixSeries
import Mathlib.RingTheory.PowerSeries.Substitution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152RightCount

open D5.S3.Combinatorics Nonnesting
open scoped BigOperators PowerSeries.WithPiTopology
open D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Right

open D5.S3.Combinatorics.InversionSeq

set_option maxHeartbeats 2400000 in
theorem right_avoider_enumeration :
    let counts := 1 + PowerSeries.X * PowerSeries.mk fun size =>
      (Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 1)
        [[1, 2, 2], [3, 1, 2], [3, 2, 1]]} : ℚ)
    let catalan := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
    let t := PowerSeries.X * catalan
    2 * (1 - PowerSeries.X) * (1 - 2 * t) * (counts - 1) =
      PowerSeries.X * (2 - 2 * t) := by
  classical
  have hcount (size : ℕ) :
    Nat.card {word : List ℕ //
      word ∈ InversionSeqDefs.avoiders (size + 1) [[1, 2, 2], [3, 1, 2], [3, 2, 1]]} =
    ∑ last : Fin (size + 1), ∑ path : {path : DyckWord // path.semilength = last.val},
      Nat.card {suffix : List ℕ // suffix.length = size - last.val ∧ suffix.Nodup ∧
        (∀ value ∈ suffix,
          last.val - (path.val.toList.reverse.takeWhile (· == DyckStep.D)).length < value) ∧
        (∀ index < suffix.length, suffix.getD index 0 ≤ last.val + 1 + index) ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] suffix ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] suffix} := by
    classical
    let Avoid := {word : List ℕ //
      word ∈ InversionSeqDefs.avoiders (size + 1) [[1, 2, 2], [3, 1, 2], [3, 2, 1]]}
    let Prefix (last : Fin (size + 1)) := {word : List ℕ // word.length = last.val ∧
      InversionSeqDefs.IsInversionSeq word ∧
      word.Pairwise (fun first second => first = 0 ∨ second = 0 ∨ first < second)}
    let Suffix (last : Fin (size + 1)) (initialWord : Prefix last) :=
      {suffix : List ℕ // suffix.length = size - last.val ∧ suffix.Nodup ∧
        (∀ value ∈ suffix, initialWord.val.foldr max 0 < value) ∧
        (∀ index < suffix.length, suffix.getD index 0 ≤ last.val + 1 + index) ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] suffix ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] suffix}
    let Splits := Σ last : Fin (size + 1), Σ initialWord : Prefix last, Suffix last initialWord
    have hmax : ∀ word : List ℕ, ∀ value ∈ word, value ≤ word.foldr max 0 := by
      intro word
      induction word with
      | nil => simp
      | cons first rest ih =>
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · exact le_max_left _ _
        · exact le_trans (ih value hvalue) (le_max_right _ _)
    have hmaxlt : ∀ word : List ℕ, ∀ value : ℕ, 0 < value →
        (∀ entry ∈ word, entry < value) → word.foldr max 0 < value := by
      intro word
      induction word with
      | nil => intro value hpos _; exact hpos
      | cons first rest ih =>
        intro value hpos hall
        exact max_lt (hall first (by simp)) (ih value hpos
          (fun entry hentry => hall entry (by simp [hentry])))
    have hbad (word : List ℕ) (hn : word.Nodup)
        (h201 : ¬ NonnestingDefs.Occurs [3, 1, 2] word)
        (h210 : ¬ NonnestingDefs.Occurs [3, 2, 1] word) :
        ∀ first second third, first < second → second < third → third < word.length →
          word.getD second 0 < word.getD first 0 →
          word.getD third 0 < word.getD first 0 → False := by
      intro first second third hfs hst hthird hsecond hthirdVal
      have hne : word.getD second 0 ≠ word.getD third 0 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hthird]
        exact fun heq => (Nat.ne_of_lt hst) ((hn.getElem_inj_iff).mp heq)
      by_cases hlt : word.getD second 0 < word.getD third 0
      · apply h201
        apply (occurs_three_iff 3 1 2 word (by omega) (by omega) (by omega)
          (by intro rank hrank hupper; omega)).mpr
        exact ⟨first, second, third, hfs, hst, hthird,
          by omega, by omega, by omega, by omega, by omega, by omega⟩
      · apply h210
        apply (occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
          (by intro rank hrank hupper; omega)).mpr
        exact ⟨first, second, third, hfs, hst, hthird,
          by omega, by omega, by omega, by omega, by omega, by omega⟩
    let join (data : Splits) : Avoid := by
      obtain ⟨last, initialWord, suffix⟩ := data
      let word := initialWord.1 ++ 0 :: suffix.1
      have hlength : word.length = size + 1 := by
        simp only [word, List.length_append, List.length_cons, initialWord.2.1, suffix.2.1]
        have := last.isLt
        omega
      have hpre (index : ℕ) (hindex : index < last.val) :
          word.getD index 0 = initialWord.1.getD index 0 := by
        exact List.getD_append _ _ _ _ (by rw [initialWord.2.1]; exact hindex)
      have hzero : word.getD last.val 0 = 0 := by
        rw [show last.val = initialWord.1.length from initialWord.2.1.symm]
        simp [word]
      have hsuf (index : ℕ) : word.getD (last.val + 1 + index) 0 =
          suffix.1.getD index 0 := by
        dsimp only [word]
        rw [List.getD_append_right _ _ _ _ (by rw [initialWord.2.1]; omega)]
        rw [initialWord.2.1, show last.val + 1 + index - last.val = index + 1 by omega]
        simp
      have hpositive (index : ℕ) (hindex : index < suffix.1.length) :
          0 < suffix.1.getD index 0 := by
        have := suffix.2.2.2.1 (suffix.1.getD index 0) (by
          rw [List.getD_eq_getElem _ _ hindex]; exact List.getElem_mem hindex)
        omega
      have hseq : InversionSeqDefs.IsInversionSeq word := by
        intro index hindex
        by_cases hlt : index < last.val
        · rw [hpre index hlt]
          exact initialWord.2.2.1 index (by rw [initialWord.2.1]; exact hlt)
        · by_cases heq : index = last.val
          · subst index; rw [hzero]; omega
          · have hi : index = last.val + 1 + (index - last.val - 1) := by omega
            rw [hi, hsuf]
            exact suffix.2.2.2.2.1 _ (by
              rw [hlength] at hindex
              rw [suffix.2.1]
              omega)
      have hnzero : ∀ position, last.val < position → position < word.length →
          word.getD position 0 ≠ 0 := by
        intro position hpos hlength'
        have hi : position = last.val + 1 + (position - last.val - 1) := by omega
        rw [hi, hsuf]
        exact Nat.ne_of_gt (hpositive _ (by
          rw [hlength] at hlength'
          rw [suffix.2.1]
          omega))
      have hsep : ∀ preindex ≤ last.val, ∀ after, last.val < after → after < word.length →
          word.getD preindex 0 < word.getD after 0 := by
        intro preindex hpreindex after hafter hlength'
        have hi : after = last.val + 1 + (after - last.val - 1) := by omega
        have hbound : after - last.val - 1 < suffix.1.length := by
          rw [hlength] at hlength'
          rw [suffix.2.1]
          omega
        have hv := suffix.2.2.2.1 (suffix.1.getD (after - last.val - 1) 0) (by
          rw [List.getD_eq_getElem _ _ hbound]; exact List.getElem_mem hbound)
        rw [hi, hsuf]
        by_cases heq : preindex = last.val
        · subst preindex; rw [hzero]; omega
        · have hpreindex' : preindex < last.val := by omega
          rw [hpre _ hpreindex']
          exact lt_of_le_of_lt (hmax initialWord.1 _ (by
            rw [List.getD_eq_getElem _ _ (by rw [initialWord.2.1]; exact hpreindex')]
            exact List.getElem_mem _)) hv
      have hprefix : ∀ first second, first < second → second ≤ last.val →
          0 < word.getD first 0 → 0 < word.getD second 0 →
          word.getD first 0 < word.getD second 0 := by
        intro first second hfs hsecond hfirstPos hsecondPos
        have hsecond' : second < last.val := by
          by_contra hnot
          have heq : second = last.val := by omega
          rw [heq, hzero] at hsecondPos
          omega
        have hfirst' : first < last.val := by omega
        rw [hpre _ hfirst', hpre _ hsecond'] at *
        have hp := List.pairwise_iff_getElem.mp initialWord.2.2.2 first second
          (by rw [initialWord.2.1]; exact hfirst') (by rw [initialWord.2.1]; exact hsecond') hfs
        rw [List.getD_eq_getElem _ _ (by rw [initialWord.2.1]; exact hfirst')] at hfirstPos
        rw [List.getD_eq_getElem _ _ (by rw [initialWord.2.1]; exact hsecond')] at hsecondPos
        rw [List.getD_eq_getElem _ _ (by rw [initialWord.2.1]; exact hfirst'),
          List.getD_eq_getElem _ _ (by rw [initialWord.2.1]; exact hsecond')]
        rcases hp with hp | hp | hp <;> omega
      have hdistinct : ∀ first second, first < second → second < word.length →
          0 < word.getD first 0 → word.getD first 0 ≠ word.getD second 0 := by
        intro first second hfs hsecond hfirstPos heq
        have hsecondPos : 0 < word.getD second 0 := by omega
        by_cases hpre : second ≤ last.val
        · have := hprefix first second hfs hpre hfirstPos hsecondPos
          omega
        · by_cases hfirst : first ≤ last.val
          · have := hsep first hfirst second (by omega) hsecond
            omega
          · have hf : first = last.val + 1 + (first - last.val - 1) := by omega
            have hs : second = last.val + 1 + (second - last.val - 1) := by omega
            rw [hf, hs, hsuf, hsuf] at heq
            have hflen : first - last.val - 1 < suffix.1.length := by
              rw [suffix.2.1]; rw [hlength] at hsecond; omega
            have hslen : second - last.val - 1 < suffix.1.length := by
              rw [suffix.2.1]; rw [hlength] at hsecond; omega
            rw [List.getD_eq_getElem _ _ hflen, List.getD_eq_getElem _ _ hslen] at heq
            have := (suffix.2.2.1.getElem_inj_iff).mp heq
            omega
      have htriples : ∀ first second third, last.val < first → first < second →
          second < third → third < word.length →
          ¬ (word.getD second 0 < word.getD first 0 ∧
            word.getD third 0 < word.getD first 0) := by
        rintro first second third hfirst hfs hst hthird ⟨hsecondVal, hthirdVal⟩
        have hf : first = last.val + 1 + (first - last.val - 1) := by omega
        have hs : second = last.val + 1 + (second - last.val - 1) := by omega
        have ht : third = last.val + 1 + (third - last.val - 1) := by omega
        rw [hf, hs, hsuf, hsuf] at hsecondVal
        rw [hf, ht, hsuf, hsuf] at hthirdVal
        exact hbad suffix.1 suffix.2.2.1 suffix.2.2.2.2.2.1 suffix.2.2.2.2.2.2
          _ _ _ (by omega) (by omega) (by rw [suffix.2.1]; rw [hlength] at hthird; omega)
          hsecondVal hthirdVal
      have hav := (right_last_zero_structure word hseq last.val
        (by rw [hlength]; exact last.isLt) hzero hnzero).mpr
          ⟨hdistinct, hprefix, hsep, htriples⟩
      refine ⟨word, hlength, hseq, ?_⟩
      simpa using hav
    have hcertificate (data : Splits) : (join data).1.getD data.1.val 0 = 0 ∧
        ∀ index, data.1.val < index → index < (join data).1.length →
          (join data).1.getD index 0 ≠ 0 := by
      obtain ⟨last, initialWord, suffix⟩ := data
      change (initialWord.1 ++ 0 :: suffix.1).getD last.val 0 = 0 ∧ _
      constructor
      · simpa only [initialWord.2.1] using
          (show (initialWord.1 ++ 0 :: suffix.1).getD initialWord.1.length 0 = 0 by simp)
      · intro index hindex hlength
        change last.val < index at hindex
        change (initialWord.1 ++ 0 :: suffix.1).getD index 0 ≠ 0
        have hi : index = initialWord.1.length + 1 + (index - last.val - 1) := by
          rw [initialWord.2.1]; omega
        rw [hi, List.getD_append_right _ _ _ _ (by omega)]
        rw [show initialWord.1.length + 1 + (index - last.val - 1) - initialWord.1.length =
          (index - last.val - 1) + 1 by omega, List.getD_cons_succ]
        have hbound : index - last.val - 1 < suffix.1.length := by
          change index < (initialWord.1 ++ 0 :: suffix.1).length at hlength
          simp only [List.length_append, List.length_cons, initialWord.2.1] at hlength
          omega
        have hv := suffix.2.2.2.1 (suffix.1.getD (index - last.val - 1) 0) (by
          rw [List.getD_eq_getElem _ _ hbound]; exact List.getElem_mem hbound)
        omega
    have hsurjective : Function.Surjective join := by
      intro word
      have hlength := word.2.1
      have hseq := word.2.2.1
      have hav : ¬ NonnestingDefs.Occurs [1, 2, 2] word.1 ∧
          ¬ NonnestingDefs.Occurs [3, 1, 2] word.1 ∧
          ¬ NonnestingDefs.Occurs [3, 2, 1] word.1 := by
        simpa using word.2.2.2
      have hfirst : word.1.getD 0 0 = 0 := by
        have := hseq 0 (by rw [hlength]; omega)
        omega
      let last := Nat.findGreatest (fun index => word.1.getD index 0 = 0) size
      have hlastle : last ≤ size := Nat.findGreatest_le _
      have hlast : last < word.1.length := by omega
      have hzero : word.1.getD last 0 = 0 := Nat.findGreatest_spec
        (P := fun index => word.1.getD index 0 = 0) (m := 0) (n := size) (by omega) hfirst
      have hnonzero : ∀ index, last < index → index < word.1.length →
          word.1.getD index 0 ≠ 0 := by
        intro index hindex hib
        exact Nat.findGreatest_is_greatest
          (P := fun index => word.1.getD index 0 = 0) hindex (by omega)
      obtain ⟨hdistinct, hincreasing, hseparated, htriples⟩ :=
        (right_last_zero_structure word.1 hseq last hlast hzero hnonzero).mp hav
      let lastFin : Fin (size + 1) := ⟨last, by omega⟩
      have htakeLen : (word.1.take last).length = last :=
        List.length_take_of_le (by omega)
      have htake (index : ℕ) (hindex : index < last) :
          (word.1.take last).getD index 0 = word.1.getD index 0 := by
        rw [List.getD_eq_getElem _ _ (by rw [htakeLen]; exact hindex), List.getElem_take,
          List.getD_eq_getElem _ _ (by omega)]
      have hdrop (index : ℕ) (hindex : index < (word.1.drop (last + 1)).length) :
          (word.1.drop (last + 1)).getD index 0 = word.1.getD (last + 1 + index) 0 := by
        rw [List.getD_eq_getElem _ _ hindex, List.getElem_drop,
          List.getD_eq_getElem _ _ (by simp only [List.length_drop] at hindex; omega)]
      let initialWord : Prefix lastFin := ⟨word.1.take last, htakeLen, by
        intro index hi
        have hi' : index < last := by omega
        rw [htake _ hi']
        exact hseq index (by omega), by
        apply List.pairwise_iff_getElem.mpr
        intro first second hfirst hsecond hfs
        simp only [List.getElem_take]
        by_cases hf : word.1[first] = 0
        · exact Or.inl hf
        · by_cases hs : word.1[second] = 0
          · exact Or.inr (Or.inl hs)
          · apply Or.inr; apply Or.inr
            have hp := hincreasing first second hfs (by omega) (by
              rw [List.getD_eq_getElem _ _ (by omega)]; omega) (by
              rw [List.getD_eq_getElem _ _ (by omega)]; omega)
            rw [List.getD_eq_getElem _ _ (by omega),
              List.getD_eq_getElem _ _ (by omega)] at hp
            exact hp⟩
      have hsufPositive (index : ℕ) (hi : index < (word.1.drop (last + 1)).length) :
          0 < (word.1.drop (last + 1)).getD index 0 := by
        rw [hdrop _ hi]
        have := hnonzero (last + 1 + index) (by omega)
          (by simp only [List.length_drop] at hi; omega)
        omega
      have hdropAvoid (pattern : List ℕ) (ha : ¬ NonnestingDefs.Occurs pattern word.1) :
          ¬ NonnestingDefs.Occurs pattern (word.1.drop (last + 1)) := by
        rintro ⟨values, hstep, hmem, hsub, _⟩
        apply ha
        refine ⟨values, hstep, ?_, hsub.trans (List.drop_sublist _ _), by simp⟩
        intro rank hrank hmax
        exact (List.drop_sublist _ _).subset (hmem rank hrank hmax)
      let suffix : Suffix lastFin initialWord := by
        refine ⟨word.1.drop (last + 1), ?_, ?_, ?_, ?_,
          hdropAvoid _ hav.2.1, hdropAvoid _ hav.2.2⟩
        · simp only [List.length_drop, hlength, lastFin]
          omega
        · apply List.pairwise_iff_getElem.mpr
          intro first second hfirst hsecond hfs heq
          have hp := hsufPositive first hfirst
          have hval : (word.1.drop (last + 1)).getD first 0 =
              (word.1.drop (last + 1)).getD second 0 := by
            rw [List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond]
            exact heq
          rw [hdrop _ hfirst, hdrop _ hsecond] at hval
          rw [hdrop _ hfirst] at hp
          exact hdistinct _ _ (by omega) (by simp only [List.length_drop] at hsecond; omega)
            hp hval
        · intro value hvalue
          obtain ⟨index, hi, hvalueEq⟩ := List.mem_iff_getElem.mp hvalue
          have hpos := hsufPositive index hi
          rw [List.getD_eq_getElem _ _ hi, hvalueEq] at hpos
          apply hmaxlt initialWord.1 value hpos
          intro entry hentry
          obtain ⟨preindex, hpi, hentryEq⟩ := List.mem_iff_getElem.mp hentry
          change preindex < (word.1.take last).length at hpi
          have hsep := hseparated preindex (by omega) (last + 1 + index) (by omega)
            (by simp only [List.length_drop] at hi; omega)
          change (word.1.take last)[preindex] = entry at hentryEq
          rw [← htake preindex (by omega), ← hdrop index hi,
            List.getD_eq_getElem _ _ hpi, hentryEq, List.getD_eq_getElem _ _ hi, hvalueEq] at hsep
          exact hsep
        · intro index hi
          rw [hdrop index hi]
          exact hseq _ (by simp only [List.length_drop] at hi; omega)
      refine ⟨⟨lastFin, initialWord, suffix⟩, ?_⟩
      apply Subtype.ext
      change word.1.take last ++ 0 :: word.1.drop (last + 1) = word.1
      have hsplit := List.take_append_drop (last + 1) word.1
      rw [List.take_succ_eq_append_getElem hlast,
        ← List.getD_eq_getElem _ _ hlast, hzero, List.append_assoc,
        List.singleton_append] at hsplit
      exact hsplit
    have hinjective : Function.Injective join := by
      intro first second heq
      have hword := congrArg Subtype.val heq
      obtain ⟨hfzero, hfnot⟩ := hcertificate first
      obtain ⟨hszero, hsnot⟩ := hcertificate second
      have hlast : first.1.val = second.1.val := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hbound : second.1.val < (join first).1.length := by
            rw [hword]; exact Nat.lt_of_lt_of_le second.1.isLt (by rw [(join second).2.1])
          have := hfnot _ hlt hbound
          rw [hword, hszero] at this
          exact this rfl
        · have hbound : first.1.val < (join second).1.length := by
            rw [← hword]; exact Nat.lt_of_lt_of_le first.1.isLt (by rw [(join first).2.1])
          have := hsnot _ hgt hbound
          rw [← hword, hfzero] at this
          exact this rfl
      obtain ⟨flast, fprefix, fsuffix⟩ := first
      obtain ⟨slast, sprefix, ssuffix⟩ := second
      have hlastEq : flast = slast := Fin.ext hlast
      subst slast
      change fprefix.1 ++ 0 :: fsuffix.1 = sprefix.1 ++ 0 :: ssuffix.1 at hword
      have hp := congrArg (List.take flast.val) hword
      have hftake : (fprefix.1 ++ 0 :: fsuffix.1).take flast.val = fprefix.1 :=
        List.take_left' fprefix.2.1
      have hstake : (sprefix.1 ++ 0 :: ssuffix.1).take flast.val = sprefix.1 :=
        List.take_left' sprefix.2.1
      rw [hftake, hstake] at hp
      have hprefixEq : fprefix = sprefix := Subtype.ext hp
      subst sprefix
      have hs := List.cons.inj (List.append_cancel_left hword)
      have hsuffixEq : fsuffix = ssuffix := Subtype.ext hs.2
      subst ssuffix
      rfl
    let Mono (last : Fin (size + 1)) := {word : List ℕ // word.length = last.val ∧
      InversionSeqDefs.IsInversionSeq word ∧ word.Pairwise (· ≤ ·)}
    let Suf (last : Fin (size + 1)) (maximum : ℕ) := {suffix : List ℕ //
      suffix.length = size - last.val ∧ suffix.Nodup ∧
      (∀ value ∈ suffix, maximum < value) ∧
      (∀ index < suffix.length, suffix.getD index 0 ≤ last.val + 1 + index) ∧
      ¬ NonnestingDefs.Occurs [3, 1, 2] suffix ∧ ¬ NonnestingDefs.Occurs [3, 2, 1] suffix}
    have hprefixEquiv (last : Fin (size + 1)) :
        ∃ equivalence : Prefix last ≃ Mono last,
          ∀ initialWord, (equivalence initialWord).1.foldr max 0 = initialWord.1.foldr max 0 := by
      let pfiber (maximum : ℕ) := {initialWord : Prefix last //
        initialWord.1.foldr max 0 = maximum}
      let mfiber (maximum : ℕ) := {initialWord : Mono last //
        initialWord.1.foldr max 0 = maximum}
      have hfiber (maximum : ℕ) : Nonempty (pfiber maximum ≃ mfiber maximum) := by
        obtain ⟨fixed⟩ := InversionSeq152Prefix.catalan_prefix_bijection last.val maximum
        let pfix : pfiber maximum ≃ {word : List ℕ // word.length = last.val ∧
            InversionSeqDefs.IsInversionSeq word ∧
            word.Pairwise (fun first second => first = 0 ∨ second = 0 ∨ first < second) ∧
            word.foldr max 0 = maximum} :=
          { toFun := fun data => ⟨data.1.1, data.1.2.1, data.1.2.2.1, data.1.2.2.2, data.2⟩
            invFun := fun data =>
              ⟨⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1⟩, data.2.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        let mfix : mfiber maximum ≃ {word : List ℕ // word.length = last.val ∧
            InversionSeqDefs.IsInversionSeq word ∧ word.Pairwise (· ≤ ·) ∧
            word.foldr max 0 = maximum} :=
          { toFun := fun data => ⟨data.1.1, data.1.2.1, data.1.2.2.1, data.1.2.2.2, data.2⟩
            invFun := fun data =>
              ⟨⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1⟩, data.2.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        exact ⟨pfix.trans (fixed.trans mfix.symm)⟩
      let fibers (maximum : ℕ) : pfiber maximum ≃ mfiber maximum :=
        Classical.choice (hfiber maximum)
      let equivalence :=
        (Equiv.sigmaFiberEquiv (fun initialWord : Prefix last =>
          initialWord.1.foldr max 0)).symm.trans
          ((Equiv.sigmaCongrRight fibers).trans
            (Equiv.sigmaFiberEquiv (fun initialWord : Mono last => initialWord.1.foldr max 0)))
      refine ⟨equivalence, ?_⟩
      intro initialWord
      exact (fibers (initialWord.1.foldr max 0) ⟨initialWord, rfl⟩).2
    have hmaxle : ∀ word : List ℕ, ∀ bound : ℕ,
        (∀ value ∈ word, value ≤ bound) → word.foldr max 0 ≤ bound := by
      intro word
      induction word with
      | nil => intro bound _; exact Nat.zero_le bound
      | cons first rest ih =>
        intro bound hall
        exact max_le (hall first (by simp)) (ih bound
          (fun value hvalue => hall value (by simp [hvalue])))
    let Paths (last : Fin (size + 1)) := {path : DyckWord // path.semilength = last.val}
    let PathSuffix (last : Fin (size + 1)) (path : Paths last) :=
      Suf last (last.val - (path.1.toList.reverse.takeWhile (· == DyckStep.D)).length)
    have hpathCounts (last : Fin (size + 1)) :
        Nonempty ((Σ initialWord : Prefix last, Suffix last initialWord) ≃
          Σ path : Paths last, PathSuffix last path) := by
      obtain ⟨prefEquiv, hmaximum⟩ := hprefixEquiv last
      obtain ⟨dyckEquiv, _, _, hfinal, _⟩ := InversionSeq152Dyck.monoDyckEquiv last.val
      let equivalence := prefEquiv.trans dyckEquiv
      have hheight (initialWord : Prefix last) :
          initialWord.1.foldr max 0 =
            last.val - ((equivalence initialWord).1.toList.reverse.takeWhile
              (· == DyckStep.D)).length := by
        have hb : initialWord.1.foldr max 0 ≤ last.val := by
          apply hmaxle
          intro value hvalue
          obtain ⟨index, hi, hvalueEq⟩ := List.mem_iff_getElem.mp hvalue
          have hbound := initialWord.2.2.1 index hi
          rw [List.getD_eq_getElem _ _ hi, hvalueEq] at hbound
          rw [initialWord.2.1] at hi
          omega
        have hf := hfinal (prefEquiv initialWord)
        rw [hmaximum] at hf
        change ((equivalence initialWord).1.toList.reverse.takeWhile
          (· == DyckStep.D)).length = last.val - initialWord.1.foldr max 0 at hf
        omega
      refine ⟨Equiv.sigmaCongr equivalence (fun initialWord => ?_)⟩
      change Suf last (initialWord.1.foldr max 0) ≃
        Suf last (last.val - ((equivalence initialWord).1.toList.reverse.takeWhile
          (· == DyckStep.D)).length)
      exact Equiv.cast (congrArg (Suf last) (hheight initialWord))
    have hsufFinite (last : Fin (size + 1)) (maximum : ℕ) : Finite (Suf last maximum) := by
      let encode (suffix : Suf last maximum) :
          List.Vector (Fin (size + 2)) (size - last.val) :=
        ⟨suffix.1.map (Fin.ofNat (size + 2)), by simp [suffix.2.1]⟩
      apply Finite.of_injective encode
      intro first second heq
      apply Subtype.ext
      have hlist := congrArg (fun vector : List.Vector (Fin (size + 2))
        (size - last.val) => vector.1) heq
      apply List.ext_getElem
      · exact first.2.1.trans second.2.1.symm
      · intro index hfirst hsecond
        have hbfirst := first.2.2.2.2.1 index hfirst
        have hbsecond := second.2.2.2.2.1 index hsecond
        rw [List.getD_eq_getElem _ _ hfirst] at hbfirst
        rw [List.getD_eq_getElem _ _ hsecond] at hbsecond
        have hifirst : first.1[index] < size + 2 := by
          have := first.2.1
          omega
        have hisecond : second.1[index] < size + 2 := by
          have := second.2.1
          omega
        have hget := congrArg (fun word : List (Fin (size + 2)) => word.getD index 0) hlist
        change (first.1.map (Fin.ofNat (size + 2))).getD index 0 =
          (second.1.map (Fin.ofNat (size + 2))).getD index 0 at hget
        rw [List.getD_eq_getElem _ _ (by simpa using hfirst), List.getElem_map,
          List.getD_eq_getElem _ _ (by simpa using hsecond), List.getElem_map] at hget
        have hvalues := congrArg Fin.val hget
        simpa [Fin.ofNat, Nat.mod_eq_of_lt hifirst, Nat.mod_eq_of_lt hisecond] using hvalues
    have (last : Fin (size + 1)) (path : Paths last) : Finite (PathSuffix last path) :=
      hsufFinite _ _
    let pathFintype (last : Fin (size + 1)) : Fintype (Paths last) :=
      inferInstanceAs (Fintype {path : DyckWord // path.semilength = last.val})
    let _ : ∀ last : Fin (size + 1), Fintype (Paths last) := pathFintype
    have (last : Fin (size + 1)) : Finite (Σ path : Paths last, PathSuffix last path) :=
      inferInstance
    let pathEquiv (last : Fin (size + 1)) := Classical.choice (hpathCounts last)
    rw [Nat.card_congr (Equiv.ofBijective join ⟨hinjective, hsurjective⟩).symm,
      Nat.card_congr (Equiv.sigmaCongrRight pathEquiv), Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro last _
    exact Nat.card_sigma

  let : UniformSpace ℚ := ⊥
  let : DiscreteTopology ℚ := ⟨rfl⟩
  let diagonal := PowerSeries.eval₂Hom (φ := RingHom.id (PowerSeries ℚ))
    continuous_id PowerSeries.HasEval.X
  have hdiagonal (f : PowerSeries (PowerSeries ℚ)) (degree : ℕ) :
      PowerSeries.coeff degree (diagonal f) =
        ∑ index ∈ Finset.range (degree + 1),
          PowerSeries.coeff (degree - index) (PowerSeries.coeff index f) := by
    have hs := PowerSeries.hasSum_eval₂ (φ := RingHom.id (PowerSeries ℚ))
      continuous_id PowerSeries.HasEval.X f
    have hsc := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ |>.mp hs) degree
    have hzero (index : ℕ) (hnot : index ∉ Finset.range (degree + 1)) :
        PowerSeries.coeff degree
          (PowerSeries.coeff index f * (PowerSeries.X : PowerSeries ℚ) ^ index) = 0 := by
      simp only [Finset.mem_range, not_lt] at hnot
      rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
    have hfinite := hasSum_sum_of_ne_finset_zero
      (L := SummationFilter.unconditional ℕ) hzero
    have heq : (∑ index ∈ Finset.range (degree + 1),
        PowerSeries.coeff degree
          (PowerSeries.coeff index f * (PowerSeries.X : PowerSeries ℚ) ^ index)) =
        ∑ index ∈ Finset.range (degree + 1),
          PowerSeries.coeff (degree - index) (PowerSeries.coeff index f) := by
      apply Finset.sum_congr rfl
      intro index hi
      rw [PowerSeries.coeff_mul_X_pow', if_pos (by
        simp only [Finset.mem_range] at hi
        omega)]
    rw [heq] at hfinite
    simpa only [diagonal, PowerSeries.coe_eval₂Hom, RingHom.id_apply]
      using hsc.unique hfinite
  let C := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
  let binary : PowerSeries ℚ := PowerSeries.mk fun size => (2 : ℚ) ^ size
  let height (path : DyckWord) :=
    (path.toList.reverse.takeWhile (· == DyckStep.D)).length
  let Paths (size : ℕ) := {path : DyckWord // path.semilength = size}
  let Suffix (lower height size : ℕ) := {word : List ℕ // word.length = size ∧
    word.Nodup ∧ (∀ value ∈ word, lower < value) ∧
    (∀ index < word.length, word.getD index 0 ≤ lower + height + 1 + index) ∧
    ¬ NonnestingDefs.Occurs [3, 1, 2] word ∧
    ¬ NonnestingDefs.Occurs [3, 2, 1] word}
  let U (lower height : ℕ) : PowerSeries ℚ :=
    1 + PowerSeries.X * PowerSeries.mk fun size =>
      (Nat.card (Suffix lower height (size + 1)) : ℚ)
  have hU (lower height : ℕ) :
      2 * (1 - PowerSeries.X) * U lower height = 1 + binary ^ height :=
    InversionSeq152SuffixSeries.first_label_suffix_enumeration lower height
  have hUcoeff (lower height degree : ℕ) :
      PowerSeries.coeff degree (U lower height) = (Nat.card (Suffix lower height degree) : ℚ) :=
    by
    cases degree with
    | zero =>
      let equiv : Suffix lower height 0 ≃ PUnit.{1} :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => ⟨[], by
            simp [NonnestingDefs.Occurs, ArrowWilfDefs.Contains]⟩
          left_inv := fun word => Subtype.ext (List.length_eq_zero_iff.mp word.2.1).symm
          right_inv := fun _ => rfl }
      rw [Nat.card_congr equiv]
      simp [U]
    | succ degree => simp [U, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
  have hheight (path : DyckWord) : height path ≤ path.semilength := by
    have hsub := List.takeWhile_sublist (l := path.toList.reverse)
      (fun step => step == DyckStep.D)
    have hall : ∀ step ∈ path.toList.reverse.takeWhile (· == DyckStep.D),
        step = DyckStep.D := by
      intro step hs
      exact beq_iff_eq.mp ((List.all_eq_true.mp (List.all_takeWhile
        (l := path.toList.reverse) (p := (· == DyckStep.D)))) step hs)
    have heq : (path.toList.reverse.takeWhile (· == DyckStep.D)).count DyckStep.D =
        height path := by
      apply List.count_eq_length.mpr
      exact fun step hs => (hall step hs).symm
    rw [← heq, DyckWord.semilength_eq_count_D]
    simpa only [List.count_reverse] using List.Sublist.count_le DyckStep.D hsub
  let V : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
    ∑ path : Paths size, U (size - height path.val) (height path.val)
  let H : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
    ∑ path : Paths size, binary ^ height path.val
  let Couter := PowerSeries.map (Nat.castRingHom (PowerSeries ℚ)) PowerSeries.catalanSeries
  have hcast (size : ℕ) : (size : PowerSeries ℚ) = PowerSeries.C (size : ℚ) :=
    (map_natCast PowerSeries.C size).symm
  have hCdiagonal : diagonal Couter = C := by
    ext degree
    rw [hdiagonal]
    simp only [Couter, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff, C]
    rw [Finset.sum_eq_single degree]
    · rw [Nat.sub_self]
      change PowerSeries.coeff 0 (catalan degree : PowerSeries ℚ) = _
      rw [hcast, PowerSeries.coeff_zero_C]
      rfl
    · intro index hi hne
      simp only [Finset.mem_range] at hi
      have hn : degree - index ≠ 0 := by omega
      change PowerSeries.coeff (degree - index) (catalan index : PowerSeries ℚ) = 0
      rw [hcast, PowerSeries.coeff_C_of_ne_zero hn]
    · simp
  have hCX (value : PowerSeries ℚ) : diagonal (PowerSeries.C value) = value := by
    dsimp only [diagonal]
    rw [PowerSeries.coe_eval₂Hom]
    exact PowerSeries.eval₂_C _ _ value
  have hX : diagonal PowerSeries.X = (PowerSeries.X : PowerSeries ℚ) := by
    dsimp only [diagonal]
    rw [PowerSeries.coe_eval₂Hom]
    exact PowerSeries.eval₂_X _ _
  have hV : 2 * PowerSeries.C (1 - (PowerSeries.X : PowerSeries ℚ)) * V =
      Couter + H := by
    ext degree
    have htwo : (2 : PowerSeries (PowerSeries ℚ)) *
        PowerSeries.C (1 - (PowerSeries.X : PowerSeries ℚ)) =
        PowerSeries.C (2 * (1 - (PowerSeries.X : PowerSeries ℚ))) := by
      rw [map_mul, map_ofNat]
    rw [htwo, PowerSeries.coeff_C_mul, map_add]
    simp only [V, H, Couter, PowerSeries.coeff_mk, PowerSeries.coeff_map,
      PowerSeries.catalanSeries_coeff]
    rw [Finset.mul_sum]
    simp_rw [hU]
    rw [Finset.sum_add_distrib]
    simp [Paths, DyckWord.card_dyckWord_semilength_eq_catalan]
  have hactual : diagonal V = PowerSeries.mk fun size =>
      (Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 1)
        [[1, 2, 2], [3, 1, 2], [3, 2, 1]]} : ℚ) := by
    ext degree
    rw [hdiagonal, PowerSeries.coeff_mk,
      hcount]
    simp only [Nat.cast_sum]
    let total (index : ℕ) : ℚ := ∑ path : Paths index,
      (Nat.card {suffix : List ℕ // suffix.length = degree - index ∧ suffix.Nodup ∧
        (∀ value ∈ suffix, index - height path.val < value) ∧
        (∀ position < suffix.length, suffix.getD position 0 ≤ index + 1 + position) ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] suffix ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] suffix} : ℚ)
    change _ = ∑ index : Fin (degree + 1), total index.val
    rw [Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro index hi
    simp only [V, PowerSeries.coeff_mk]
    dsimp only [total]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro path hp
    rw [hUcoeff]
    have hh : height path.val ≤ index := (hheight path.val).trans_eq path.property
    have heq : index - height path.val + height path.val = index := by omega
    simp only [Suffix, heq]
  have hfinal : (1 - PowerSeries.C binary * PowerSeries.X * Couter) * H = 1 :=
    InversionSeq152FinalSeries.final_descent_enumeration binary
  have hfinaldiag : (1 - binary * PowerSeries.X * C) * diagonal H = 1 := by
    have hh := congrArg diagonal hfinal
    simpa only [map_mul, map_sub, map_one, hCX, hX, hCdiagonal] using hh
  have hVdiag : 2 * (1 - PowerSeries.X) * diagonal V = C + diagonal H := by
    have hh := congrArg diagonal hV
    simpa only [map_mul, map_add, map_ofNat, hCX, hCdiagonal] using hh
  have hbinary : (1 - 2 * PowerSeries.X) * binary = 1 := by
    ext degree
    cases degree with
    | zero => simp [binary]
    | succ degree =>
      have heq : (1 - 2 * (PowerSeries.X : PowerSeries ℚ)) * binary =
          binary - 2 * (PowerSeries.X * binary) := by ring
      rw [heq, map_sub]
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp [binary, pow_succ]
      ring
  have hcat : C * (1 - PowerSeries.X * C) = 1 := by
    have hh := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simp only [map_add, map_mul, map_one, PowerSeries.map_X, map_pow] at hh
    dsimp [C]
    linear_combination -hh
  dsimp only
  rw [← hactual]
  have hxcat : PowerSeries.X * C * (1 - PowerSeries.X * C) = PowerSeries.X := by
    linear_combination PowerSeries.X * hcat
  have hdH : (1 - 2 * PowerSeries.X - PowerSeries.X * C) * diagonal H =
      1 - 2 * PowerSeries.X := by
    linear_combination (1 - 2 * PowerSeries.X) * hfinaldiag +
      PowerSeries.X * C * diagonal H * hbinary
  have hcD : C * (1 - 2 * PowerSeries.X - PowerSeries.X * C) =
      1 - 2 * PowerSeries.X * C := by
    linear_combination (1 - 2 * PowerSeries.X * C) * hcat + 2 * C * hxcat
  change 2 * (1 - PowerSeries.X) * (1 - 2 * (PowerSeries.X * C)) *
    (1 + PowerSeries.X * diagonal V - 1) = PowerSeries.X * (2 - 2 * (PowerSeries.X * C))
  linear_combination
    PowerSeries.X * C * (1 - 2 * PowerSeries.X - PowerSeries.X * C) * hVdiag +
    PowerSeries.X * C * hdH +
    (PowerSeries.X * C - 2 * PowerSeries.X * (1 - PowerSeries.X) * diagonal V) * hcD +
    2 * PowerSeries.X * (1 - PowerSeries.X * C) * hcat + 2 * PowerSeries.X * C * hxcat

end D5.S3.Combinatorics.InversionSeq.InversionSeq152RightCount
