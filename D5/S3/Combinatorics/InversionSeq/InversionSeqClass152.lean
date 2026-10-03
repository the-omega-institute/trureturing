/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeqClass152
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeqClass152
   mirror-E: none(waiver:class-152-equinumerosity)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: First-descent and last-zero bijections prove Class 152 equinumerosity at every length. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Left
import D5.S3.Combinatorics.InversionSeq.InversionSeq152GapWeights
import D5.S3.Combinatorics.InversionSeq.InversionSeq152RightCount
import D5.S3.Combinatorics.InversionSeq.InversionSeq152MarkedSeries
import D5.S3.Combinatorics.InversionSeq.InversionSeq152PenultimateSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeqClass152

open scoped PowerSeries.WithPiTopology BigOperators
open D5.S3.Combinatorics Nonnesting
open D5.S3.Combinatorics.InversionSeq
open InversionSeqOccurs InversionSeq152Left

set_option maxHeartbeats 6400000 in
theorem result : InversionSeqDefs.claim152 := by
  classical
  have hleftcount (size : ℕ) :
    Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 2)
      [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]]} =
    Fintype.card {path : DyckWord // path.semilength = size + 2} +
      ∑ cut : Fin (size + 1),
        ∑ path : {path : DyckWord // path.semilength = cut.val + 1},
          let gaps := (((path.val.toList.splitOn DyckStep.U).map List.length).filter
            (· != 0)).dropLast
          ((gaps.dropLast.map (fun run => (run - 1).choose (size + 1 - cut.val))).sum) +
            (gaps.getLastD 0 - 1 + (size - cut.val)).choose (size + 1 - cut.val) := by
    classical
    let Mono (length : ℕ) := {word : List ℕ // word.length = length ∧
      InversionSeqDefs.IsInversionSeq word ∧ word.Pairwise (· ≤ ·)}
    let Avoid := {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 2)
      [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]]}
    let Suf (cut : Fin (size + 1)) (initialWord : Mono (cut.val + 1))
        (gap : Fin (cut.val + 1)) :=
      {suffix : List ℕ // suffix.length = size + 1 - cut.val ∧
        (∀ value ∈ suffix,
          (initialWord.1.getD (gap.val - 1) 0 < value ∧ value < initialWord.1.getD gap.val 0) ∨
          (initialWord.1.getD gap.val 0 = initialWord.1.getD cut.val 0 ∧
            value = initialWord.1.getD cut.val 0)) ∧
        (suffix.filter (· ≠ initialWord.1.getD cut.val 0)).Pairwise (· < ·) ∧
        initialWord.1.getD (gap.val - 1) 0 < suffix.getD 0 0 ∧
        suffix.getD 0 0 < initialWord.1.getD gap.val 0}
    let Splits := Σ cut : Fin (size + 1), Σ initialWord : Mono (cut.val + 1),
      Σ gap : Fin (cut.val + 1), Suf cut initialWord gap
    have hmono (word : List ℕ) (hsorted : word.Pairwise (· ≤ ·))
        (first second : ℕ) (hfirst : first ≤ second) (hsecond : second < word.length) :
        word.getD first 0 ≤ word.getD second 0 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hsecond]
      exact hsorted.rel_get_of_le (show (⟨first, by omega⟩ : Fin word.length) ≤
        ⟨second, hsecond⟩ from hfirst)
    have hsorted (word : List ℕ) (bound : ℕ) (hbound : bound < word.length)
        (hadjacent : ∀ index < bound, word.getD index 0 ≤ word.getD (index + 1) 0) :
        ∀ first second, first ≤ second → second ≤ bound →
          word.getD first 0 ≤ word.getD second 0 := by
      intro first second hfirst hsecond
      induction second with
      | zero =>
        have hz : first = 0 := by omega
        subst first; exact le_rfl
      | succ second ih =>
        by_cases heq : first = second + 1
        · subst first; exact le_rfl
        · exact (ih (by omega) (by omega)).trans (hadjacent second (by omega))
    have htake (word : List ℕ) (length index : ℕ) (hi : index < length)
        (hw : index < word.length) : (word.take length).getD index 0 = word.getD index 0 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take,
        List.getD_eq_getElem _ _ hw]
    have hdrop (word : List ℕ) (length index : ℕ) (hi : length + index < word.length) :
        (word.drop length).getD index 0 = word.getD (length + index) 0 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_drop,
        List.getD_eq_getElem _ _ hi]
    have hfilter (word : List ℕ) (maximum : ℕ) :
        (word.filter (· ≠ maximum)).Pairwise (· < ·) ↔
          ∀ first second, first < second → second < word.length →
            word.getD first 0 ≠ maximum → word.getD second 0 ≠ maximum →
            word.getD first 0 < word.getD second 0 := by
      rw [List.pairwise_filter, List.pairwise_iff_getElem]
      constructor
      · intro h first second hfs hs hfval hsval
        rw [List.getD_eq_getElem _ _ (by omega)] at hfval ⊢
        rw [List.getD_eq_getElem _ _ hs] at hsval ⊢
        exact h first second (by omega) hs hfs (by simpa using hfval)
          (by simpa using hsval)
      · intro h first second hf hs hfs hfval hsval
        have hf' : word.getD first 0 ≠ maximum := by
          rw [List.getD_eq_getElem _ _ hf]; simpa using hfval
        have hs' : word.getD second 0 ≠ maximum := by
          rw [List.getD_eq_getElem _ _ hs]; simpa using hsval
        simpa only [List.getD_eq_getElem _ _ hf, List.getD_eq_getElem _ _ hs]
          using h first second hfs hs hf' hs'
    have hnondecreasing (word : List ℕ) (hsorted : word.Pairwise (· ≤ ·)) :
        ¬ NonnestingDefs.Occurs [1, 2, 1] word ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1] word ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] word ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] word := by
      have hp010 := occurs_three_iff 1 2 1 word (by omega) (by omega) (by omega)
        (by intro rank hrank hupper; omega)
      have hp100 := occurs_three_iff 2 1 1 word (by omega) (by omega) (by omega)
        (by intro rank hrank hupper; omega)
      have hp102 := occurs_three_iff 2 1 3 word (by omega) (by omega) (by omega)
        (by intro rank hrank hupper; omega)
      have hp210 := occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
        (by intro rank hrank hupper; omega)
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨first, second, third, hfs, hst, ht, hrels⟩ := hp010.mp h
        have hle := hmono word hsorted second third (by omega) ht
        obtain ⟨_, _, _, _, _, _⟩ := hrels
        omega
      · obtain ⟨first, second, third, hfs, hst, ht, hrels⟩ := hp100.mp h
        have hle := hmono word hsorted first second (by omega) (by omega)
        obtain ⟨_, _, _, _, _, _⟩ := hrels
        omega
      · obtain ⟨first, second, third, hfs, hst, ht, hrels⟩ := hp102.mp h
        have hle := hmono word hsorted first second (by omega) (by omega)
        obtain ⟨_, _, _, _, _, _⟩ := hrels
        omega
      · obtain ⟨first, second, third, hfs, hst, ht, hrels⟩ := hp210.mp h
        have hle := hmono word hsorted first second (by omega) (by omega)
        obtain ⟨_, _, _, _, _, _⟩ := hrels
        omega
    let join : Mono (size + 2) ⊕ Splits → Avoid := fun data => by
      cases data with
      | inl word =>
        refine ⟨word.1, word.2.1, word.2.2.1, ?_⟩
        simpa using hnondecreasing word.1 word.2.2.2
      | inr data =>
        obtain ⟨cut, initialWord, gap, suffix⟩ := data
        let word := initialWord.1 ++ suffix.1
        let maximum := initialWord.1.getD cut.val 0
        let upper := initialWord.1.getD gap.val 0
        let lower := initialWord.1.getD (gap.val - 1) 0
        have hplen := initialWord.2.1; have hslen := suffix.2.1
        have hpre (index : ℕ) (hi : index ≤ cut.val) :
            word.getD index 0 = initialWord.1.getD index 0 :=
          List.getD_append _ _ _ _ (by rw [hplen]; omega)
        have hsuf (index : ℕ) : word.getD (cut.val + 1 + index) 0 =
            suffix.1.getD index 0 := by
          dsimp only [word]; rw [List.getD_append_right _ _ _ _ (by rw [hplen]; omega), hplen]
          congr 1
          omega
        have hboundary : word.getD (cut.val + 1) 0 = suffix.1.getD 0 0 := by
          simpa only [Nat.add_zero] using hsuf 0
        have hlength : word.length = size + 2 := by
          simp only [word, List.length_append, hplen, hslen]; have := cut.isLt; omega
        have hu : upper ≤ maximum := hmono initialWord.1 initialWord.2.2.2 _ _
          (by have := gap.isLt; omega) (by rw [hplen]; omega)
        have hall (index : ℕ) (hi : index < suffix.1.length) :
            (lower < suffix.1.getD index 0 ∧ suffix.1.getD index 0 < upper) ∨
            (upper = maximum ∧ suffix.1.getD index 0 = maximum) := by
          exact suffix.2.2.1 _ (by
            rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
        have hmax (index : ℕ) (hi : index < word.length) : word.getD index 0 ≤ maximum := by
          by_cases hp : index ≤ cut.val
          · rw [hpre index hp]
            exact hmono initialWord.1 initialWord.2.2.2 _ _ hp (by rw [hplen]; omega)
          · have heq : index = cut.val + 1 + (index - cut.val - 1) := by omega
            rw [heq, hsuf]
            have hh := hall (index - cut.val - 1) (by
              simp only [word, List.length_append, hplen] at hi; omega)
            rcases hh with hh | hh <;> omega
        have hpref : ∀ first second, first ≤ second → second ≤ cut.val →
            word.getD first 0 ≤ word.getD second 0 := by
          intro first second hfs hs; rw [hpre first (by omega), hpre second hs]
          exact hmono initialWord.1 initialWord.2.2.2 _ _ hfs (by rw [hplen]; omega)
        have hfirst := suffix.2.2.2.2
        have hdescent : word.getD (cut.val + 1) 0 < word.getD cut.val 0 := by
          rw [hpre cut.val le_rfl, hboundary]; exact hfirst.2.trans_le hu
        have habsent : ∀ index, cut.val < index → index < word.length →
            word.getD index 0 < word.getD cut.val 0 →
            ∀ preindex ≤ cut.val, word.getD preindex 0 ≠ word.getD index 0 := by
          intro index hcut hi hlow preindex hp heq
          have heqi : index = cut.val + 1 + (index - cut.val - 1) := by omega
          rw [heqi, hsuf] at heq hlow; rw [hpre preindex hp] at heq
          rw [hpre cut.val le_rfl] at hlow
          have hh := hall (index - cut.val - 1) (by
            simp only [word, List.length_append, hplen] at hi; omega)
          rcases hh with ⟨hl, huval⟩ | hh
          · by_cases hbefore : preindex < gap.val
            · have hle := hmono initialWord.1 initialWord.2.2.2 preindex (gap.val - 1)
                (by omega) (by rw [hplen]; have := gap.isLt; omega)
              change initialWord.1.getD preindex 0 ≤ lower at hle; omega
            · have hle := hmono initialWord.1 initialWord.2.2.2 gap.val preindex
                (by omega) (by rw [hplen]; omega)
              change upper ≤ initialWord.1.getD preindex 0 at hle; omega
          · omega
        have hincreasing : ∀ first second, cut.val < first → first < second →
            second < word.length → word.getD first 0 < word.getD cut.val 0 →
            word.getD second 0 < word.getD cut.val 0 →
            word.getD first 0 < word.getD second 0 := by
          intro first second hcut hfs hs hfval hsval
          have heqf : first = cut.val + 1 + (first - cut.val - 1) := by omega
          have heqs : second = cut.val + 1 + (second - cut.val - 1) := by omega
          rw [hpre cut.val le_rfl, heqf, hsuf] at hfval
          rw [hpre cut.val le_rfl, heqs, hsuf] at hsval; rw [heqf, heqs, hsuf, hsuf]
          exact (hfilter suffix.1 maximum).mp suffix.2.2.2.1 _ _ (by omega)
            (by simp only [word, List.length_append, hplen] at hs; omega)
            (by omega) (by omega)
        have hgap : ∀ preindex ≤ cut.val, word.getD preindex 0 < word.getD cut.val 0 →
            word.getD (cut.val + 1) 0 < word.getD preindex 0 →
            ∀ index, cut.val < index → index < word.length →
              word.getD index 0 < word.getD preindex 0 := by
          intro preindex hp hlow habove index hcut hi
          rw [hpre preindex hp, hpre cut.val le_rfl] at hlow
          rw [hpre preindex hp, hboundary] at habove
          have hafter : gap.val ≤ preindex := by
            by_contra hn
            have hle := hmono initialWord.1 initialWord.2.2.2 preindex (gap.val - 1)
              (by omega) (by rw [hplen]; have := gap.isLt; omega)
            change initialWord.1.getD preindex 0 ≤ lower at hle; omega
          have huval := hmono initialWord.1 initialWord.2.2.2 gap.val preindex hafter
            (by rw [hplen]; omega)
          have heq : index = cut.val + 1 + (index - cut.val - 1) := by omega
          rw [hpre preindex hp, heq, hsuf]
          have hh := hall (index - cut.val - 1) (by
            simp only [word, List.length_append, hplen] at hi; omega)
          rcases hh with hh | hh <;> dsimp [upper, maximum] at * <;> omega
        have hav := (first_descent_structure word cut.val (by
          rw [hlength]; have := cut.isLt
          omega) hpref hdescent).mpr
            ⟨fun index hi => by rw [hpre cut.val le_rfl]; exact hmax index hi,
              habsent, hincreasing, hgap⟩
        refine ⟨word, hlength, ?_, ?_⟩
        · intro index hi
          by_cases hp : index ≤ cut.val
          · rw [hpre index hp]
            exact initialWord.2.2.1 index (by rw [hplen]; omega)
          · have hm := hmax index hi
            have hb := initialWord.2.2.1 cut.val (by rw [hplen]; omega); dsimp only [maximum] at hm
            omega
        · simpa using hav
    have hcertificate (cut : Fin (size + 1)) (initialWord : Mono (cut.val + 1))
        (gap : Fin (cut.val + 1)) (suffix : Suf cut initialWord gap) :
        ∀ index < cut.val, (initialWord.1 ++ suffix.1).getD index 0 ≤
          (initialWord.1 ++ suffix.1).getD (index + 1) 0 := by
      intro index hi
      rw [List.getD_append _ _ _ _ (by rw [initialWord.2.1]; omega),
        List.getD_append _ _ _ _ (by rw [initialWord.2.1]; omega)]
      exact hmono initialWord.1 initialWord.2.2.2 _ _ (by omega) (by rw [initialWord.2.1]; omega)
    have hdescent (cut : Fin (size + 1)) (initialWord : Mono (cut.val + 1))
        (gap : Fin (cut.val + 1)) (suffix : Suf cut initialWord gap) :
        (initialWord.1 ++ suffix.1).getD (cut.val + 1) 0 <
          (initialWord.1 ++ suffix.1).getD cut.val 0 := by
      have hboundary : (initialWord.1 ++ suffix.1).getD (cut.val + 1) 0 =
          suffix.1.getD 0 0 := by
        simpa only [initialWord.2.1] using
          (show (initialWord.1 ++ suffix.1).getD initialWord.1.length 0 =
            suffix.1.getD 0 0 by
              rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self])
      rw [hboundary, List.getD_append initialWord.1 suffix.1 0 cut.val
        (by rw [initialWord.2.1]; omega)]
      exact suffix.2.2.2.2.2.trans_le (hmono initialWord.1 initialWord.2.2.2 _ _
        (by have := gap.isLt; omega) (by rw [initialWord.2.1]; omega))
    have hsurjective : Function.Surjective join := by
      intro word
      by_cases hmonotone : word.1.Pairwise (· ≤ ·)
      · exact ⟨Sum.inl ⟨word.1, word.2.1, word.2.2.1, hmonotone⟩, Subtype.ext rfl⟩
      have hex : ∃ index, index + 1 < word.1.length ∧
          word.1.getD (index + 1) 0 < word.1.getD index 0 := by
        by_contra hn
        apply hmonotone
        apply List.pairwise_iff_getElem.mpr
        intro first second hf hs hfs
        have hb := hsorted word.1 second hs (by
          intro index hi
          have hh : ¬ (index + 1 < word.1.length ∧
              word.1.getD (index + 1) 0 < word.1.getD index 0) :=
            fun h => hn ⟨index, h⟩
          omega) first second (by omega) le_rfl
        rw [List.getD_eq_getElem word.1 0 hf,
          List.getD_eq_getElem word.1 0 hs] at hb
        exact hb
      let cutVal := Nat.find hex
      have hcut : cutVal + 1 < word.1.length ∧
          word.1.getD (cutVal + 1) 0 < word.1.getD cutVal 0 := Nat.find_spec hex
      have hpref : ∀ first second, first ≤ second → second ≤ cutVal →
          word.1.getD first 0 ≤ word.1.getD second 0 := by
        apply hsorted word.1 cutVal (by omega)
        intro index hi; have hh := Nat.find_min hex hi; dsimp only [cutVal] at hi
        have hb : index + 1 < word.1.length := by change _ at hcut; omega
        omega
      have hcutbound : cutVal < size + 1 := by
        have hlen := word.2.1; omega
      let cut : Fin (size + 1) := ⟨cutVal, hcutbound⟩
      let initialWord : Mono (cut.val + 1) := ⟨word.1.take (cutVal + 1), by
        refine ⟨by simp only [List.length_take, cut]; exact Nat.min_eq_left (by omega),
          ?_, ?_⟩
        · intro index hi
          rw [htake _ _ _ (by simp only [List.length_take] at hi; omega)
            (by simp only [List.length_take] at hi; omega)]
          exact word.2.2.1 index (by simp only [List.length_take] at hi; omega)
        · apply List.pairwise_iff_getElem.mpr
          intro first second hf hs hfs; have hh := hpref first second (by omega)
            (by simp only [List.length_take] at hs; omega)
          rw [← htake word.1 (cutVal + 1) first
            (by simp only [List.length_take] at hf; omega)
            (by simp only [List.length_take] at hf; omega),
            ← htake word.1 (cutVal + 1) second
            (by simp only [List.length_take] at hs; omega)
            (by simp only [List.length_take] at hs; omega)] at hh
          rw [List.getD_eq_getElem (word.1.take (cutVal + 1)) 0 hf,
            List.getD_eq_getElem (word.1.take (cutVal + 1)) 0 hs] at hh
          exact hh⟩
      have hpre (index : ℕ) (hi : index ≤ cutVal) :
          initialWord.1.getD index 0 = word.1.getD index 0 :=
        htake _ _ _ (by omega) (by omega)
      let suffix := word.1.drop (cutVal + 1)
      have hsuf (index : ℕ) (hi : index < suffix.length) :
          suffix.getD index 0 = word.1.getD (cutVal + 1 + index) 0 :=
        hdrop _ _ _ (by dsimp [suffix] at hi; simp only [List.length_drop] at hi; omega)
      have hslen : suffix.length = size + 1 - cut.val := by
        simp only [suffix, List.length_drop, word.2.1, cut]; omega
      have hspos : 0 < suffix.length := by rw [hslen]; have := cut.isLt; omega
      have hav : ¬ NonnestingDefs.Occurs [1, 2, 1] word.1 ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1] word.1 ∧
          ¬ NonnestingDefs.Occurs [2, 1, 3] word.1 ∧
          ¬ NonnestingDefs.Occurs [3, 2, 1] word.1 := by simpa using word.2.2.2
      obtain ⟨hmax, habsent, hincreasing, hgap⟩ :=
        (first_descent_structure word.1 cutVal hcut.1 hpref hcut.2).mp hav
      let first := suffix.getD 0 0
      have hfirst : first = word.1.getD (cutVal + 1) 0 := by
        simpa [first] using hsuf 0 hspos
      have hfirstlow : first < initialWord.1.getD cut.val 0 := by
        rw [hpre cutVal le_rfl, hfirst]; exact hcut.2
      change first < initialWord.1.getD cutVal 0 at hfirstlow
      have hfirstabsent : ∀ index ≤ cutVal, initialWord.1.getD index 0 ≠ first := by
        intro index hi; rw [hpre index hi, hfirst]
        exact habsent _ (by omega) hcut.1 hcut.2 index hi
      have hgapEx : ∃ index, index ≤ cutVal ∧ first < initialWord.1.getD index 0 :=
        ⟨cutVal, le_rfl, hfirstlow⟩
      let gapVal := Nat.find hgapEx
      have hg : gapVal ≤ cutVal ∧ first < initialWord.1.getD gapVal 0 :=
        Nat.find_spec hgapEx
      have hgpos : 0 < gapVal := by
        by_contra hn
        have hz : gapVal = 0 := by omega
        have hg' := hg.2; rw [hz, hpre 0 (by omega)] at hg'
        have hb := word.2.2.1 0 (by rw [word.2.1]; omega); omega
      let gap : Fin (cut.val + 1) := ⟨gapVal, by change gapVal < cutVal + 1; omega⟩
      have hlower : initialWord.1.getD (gap.val - 1) 0 < first := by
        have hn := Nat.find_min hgapEx (show gapVal - 1 < gapVal by omega)
        have hne := hfirstabsent (gapVal - 1) (by omega)
        change ¬ (gapVal - 1 ≤ cutVal ∧ first < initialWord.1.getD (gapVal - 1) 0) at hn
        change initialWord.1.getD (gapVal - 1) 0 < first; omega
      have hupper : first < initialWord.1.getD gap.val 0 := hg.2
      let suffixData : Suf cut initialWord gap := ⟨suffix, hslen, by
        refine ⟨?_, ?_, hlower, hupper⟩
        · intro value hv
          obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hv
          have hval : value = word.1.getD (cutVal + 1 + index) 0 := by
            rw [← hsuf index hi, List.getD_eq_getElem suffix 0 hi, heq]
          have hlen : cutVal + 1 + index < word.1.length := by
            dsimp [suffix] at hi; simp only [List.length_drop] at hi; omega
          have hm := hmax _ hlen
          have hm' : value ≤ initialWord.1.getD cutVal 0 := by
            rw [hpre cutVal le_rfl, hval]; exact hm
          have hy : first ≤ value := by
            by_cases hz : index = 0
            · subst index; rw [hval, hfirst]
            · by_cases heqm : value = initialWord.1.getD cutVal 0
              · omega
              · have hh := hincreasing (cutVal + 1) (cutVal + 1 + index)
                  (by omega) (by omega) hlen hcut.2 (by
                    rw [← hpre cutVal le_rfl, ← hval]; omega)
                rw [← hfirst, ← hval] at hh; omega
          have hlow : initialWord.1.getD (gap.val - 1) 0 < value := by omega
          by_cases htop : initialWord.1.getD gap.val 0 = initialWord.1.getD cutVal 0
          · by_cases heqm : value = initialWord.1.getD cutVal 0
            · exact Or.inr ⟨htop, heqm⟩
            · exact Or.inl ⟨hlow, by omega⟩
          · have hgle : gap.val ≤ cutVal := hg.1
            have hu := hmono initialWord.1 initialWord.2.2.2 gap.val cut.val
              (by change gap.val ≤ cutVal; exact hgle) (by rw [initialWord.2.1]; omega)
            change initialWord.1.getD gap.val 0 ≤ initialWord.1.getD cutVal 0 at hu
            change initialWord.1.getD gap.val 0 ≠ initialWord.1.getD cutVal 0 at htop
            have hh := hgap gap.val hgle
              (by rw [← hpre gap.val hgle, ← hpre cutVal le_rfl]; omega)
              (by rw [← hfirst, ← hpre gap.val hgle]; exact hupper)
              _ (by omega) hlen
            rw [← hpre gap.val hgle, ← hval] at hh; exact Or.inl ⟨hlow, hh⟩
        · apply (hfilter suffix (initialWord.1.getD cut.val 0)).mpr
          intro firstIndex secondIndex hfs hs hfval hsval
          have hfl : firstIndex < suffix.length := by omega
          rw [hsuf firstIndex hfl, hsuf secondIndex hs]
          have hmfirst := hmax (cutVal + 1 + firstIndex) (by
            dsimp [suffix] at hfl; simp only [List.length_drop] at hfl; omega)
          have hmsecond := hmax (cutVal + 1 + secondIndex) (by
            dsimp [suffix] at hs; simp only [List.length_drop] at hs; omega)
          rw [hpre cutVal le_rfl, hsuf firstIndex hfl] at hfval
          rw [hpre cutVal le_rfl, hsuf secondIndex hs] at hsval
          exact hincreasing _ _ (by omega) (by omega)
            (by dsimp [suffix] at hs; simp only [List.length_drop] at hs; omega)
            (by omega) (by omega)⟩
      refine ⟨Sum.inr ⟨cut, initialWord, gap, suffixData⟩, ?_⟩
      apply Subtype.ext
      exact List.take_append_drop _ _
    have hinjective : Function.Injective join := by
      intro firstData secondData heq
      cases firstData with
      | inl first =>
        cases secondData with
        | inl second =>
          have hw : first.1 = second.1 := congrArg (fun value : Avoid => value.1) heq
          exact congrArg Sum.inl (Subtype.ext hw)
        | inr second =>
          obtain ⟨cut, initialWord, gap, suffix⟩ := second
          have hw : first.1 = initialWord.1 ++ suffix.1 := congrArg Subtype.val heq
          have hd := hdescent cut initialWord gap suffix; rw [← hw] at hd
          have hm := hmono first.1 first.2.2.2 cut.val (cut.val + 1) (by omega)
            (by rw [first.2.1]; have := cut.isLt; omega)
          omega
      | inr first =>
        obtain ⟨cut, initialWord, gap, suffix⟩ := first
        cases secondData with
        | inl second =>
          have hw : initialWord.1 ++ suffix.1 = second.1 := congrArg Subtype.val heq
          have hd := hdescent cut initialWord gap suffix; rw [hw] at hd
          have hm := hmono second.1 second.2.2.2 cut.val (cut.val + 1) (by omega)
            (by rw [second.2.1]; have := cut.isLt; omega)
          omega
        | inr second =>
          obtain ⟨cut', initialWord', gap', suffix'⟩ := second
          have hw : initialWord.1 ++ suffix.1 = initialWord'.1 ++ suffix'.1 :=
            congrArg Subtype.val heq
          have hc : cut = cut' := by
            apply Fin.ext
            by_contra hn
            rcases lt_or_gt_of_ne hn with hlt | hgt
            · have hd := hdescent cut initialWord gap suffix
              rw [hw] at hd; have hm := hcertificate cut' initialWord' gap' suffix' cut.val hlt
              omega
            · have hd := hdescent cut' initialWord' gap' suffix'
              rw [← hw] at hd; have hm := hcertificate cut initialWord gap suffix cut'.val hgt
              omega
          subst cut'
          have hp : initialWord = initialWord' := by
            apply Subtype.ext
            have hh := congrArg (List.take (cut.val + 1)) hw
            have ht (pre : Mono (cut.val + 1)) (suf : List ℕ) :
                (pre.1 ++ suf).take (cut.val + 1) = pre.1 := by
              simpa only [pre.2.1] using
                (List.take_left (l₁ := pre.1) (l₂ := suf))
            rw [ht initialWord suffix.1, ht initialWord' suffix'.1] at hh; exact hh
          subst initialWord'; have hs : suffix.1 = suffix'.1 := List.append_cancel_left hw
          have hg : gap = gap' := by
            apply Fin.ext
            by_contra hn
            rcases lt_or_gt_of_ne hn with hlt | hgt
            · have hh := hmono initialWord.1 initialWord.2.2.2 gap.val (gap'.val - 1)
                (by omega) (by rw [initialWord.2.1]; have := gap'.isLt; omega)
              have hf := suffix.2.2.2.2.2; have hf' := suffix'.2.2.2.2.1; rw [hs] at hf; omega
            · have hh := hmono initialWord.1 initialWord.2.2.2 gap'.val (gap.val - 1)
                (by omega) (by rw [initialWord.2.1]; have := gap.isLt; omega)
              have hf := suffix.2.2.2.2.1; have hf' := suffix'.2.2.2.2.2; rw [hs] at hf; omega
          subst gap'; have hs' : suffix = suffix' := Subtype.ext hs; subst suffix'; rfl
    let Paths (length : ℕ) := {path : DyckWord // path.semilength = length}
    let dyckEquiv (length : ℕ) : Mono length ≃ Paths length :=
      Classical.choose (InversionSeq152Dyck.monoDyckEquiv length)
    let monoFintype (length : ℕ) : Fintype (Mono length) :=
      Fintype.ofEquiv (Paths length) (dyckEquiv length).symm
    let _ : ∀ length, Fintype (Mono length) := monoFintype
    have hcount (cut : Fin (size + 1)) (initialWord : Mono (cut.val + 1))
        (gap : Fin (cut.val + 1)) :
        Finite (Suf cut initialWord gap) ∧ Nat.card (Suf cut initialWord gap) =
          if initialWord.1.getD gap.val 0 = initialWord.1.getD cut.val 0 then
            (initialWord.1.getD gap.val 0 - initialWord.1.getD (gap.val - 1) 0 - 1 +
              (size - cut.val)).choose (size + 1 - cut.val)
          else (initialWord.1.getD gap.val 0 -
            initialWord.1.getD (gap.val - 1) 0 - 1).choose (size + 1 - cut.val) := by
      let lower := initialWord.1.getD (gap.val - 1) 0
      let upper := initialWord.1.getD gap.val 0
      let maximum := initialWord.1.getD cut.val 0
      let interval := Finset.Ioo lower upper
      have hu : upper ≤ maximum := hmono initialWord.1 initialWord.2.2.2 _ _
        (by have := gap.isLt; omega) (by rw [initialWord.2.1]; omega)
      have hlength : size + 1 - cut.val = (size - cut.val) + 1 := by
        have := cut.isLt; omega
      have hinterval : ∀ value ∈ interval, value < maximum := by
        intro value hv; have hh := Finset.mem_Ioo.mp hv; omega
      obtain ⟨internalEquiv, topEquiv, hinternal, htop⟩ :=
        InversionSeq152GapCount.gap_suffix_enumerators
        interval maximum (size - cut.val) hinterval
      by_cases hlast : upper = maximum
      · rw [if_pos hlast]
        have hprop (word : List ℕ) :
            (word.length = size + 1 - cut.val ∧
              (∀ value ∈ word, (lower < value ∧ value < upper) ∨
                (upper = maximum ∧ value = maximum)) ∧
              (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧
              lower < word.getD 0 0 ∧ word.getD 0 0 < upper) ↔
            (word.length = (size - cut.val) + 1 ∧
              (∀ value ∈ word, value ∈ interval ∨ value = maximum) ∧
              (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧
              word.getD 0 maximum ≠ maximum) := by
          constructor
          · rintro ⟨hlen, hall, hpair, hlo, hup⟩
            have hz : 0 < word.length := by rw [hlen, hlength]; omega
            refine ⟨hlen.trans hlength, ?_, hpair, ?_⟩
            · intro value hv
              rcases hall value hv with hgap | hmax
              · exact Or.inl (Finset.mem_Ioo.mpr hgap)
              · exact Or.inr hmax.2
            · rw [List.getD_eq_getElem word maximum hz]
              rw [List.getD_eq_getElem word 0 hz] at hup; omega
          · rintro ⟨hlen, hall, hpair, hfirst⟩
            have hz : 0 < word.length := by omega
            have hh := hall (word.getD 0 0) (by
              rw [List.getD_eq_getElem word 0 hz]; exact List.getElem_mem hz)
            have heq : word.getD 0 maximum = word.getD 0 0 := by
              rw [List.getD_eq_getElem word maximum hz, List.getD_eq_getElem word 0 hz]
            rw [heq] at hfirst
            have hgap : lower < word.getD 0 0 ∧ word.getD 0 0 < upper := by
              rcases hh with hh | hh
              · exact Finset.mem_Ioo.mp hh
              · exact False.elim (hfirst hh)
            refine ⟨hlen.trans hlength.symm, ?_, hpair, hgap⟩
            intro value hv
            rcases hall value hv with hh | hh
            · exact Or.inl (Finset.mem_Ioo.mp hh)
            · exact Or.inr ⟨hlast, hh⟩
        let equivalence := Equiv.subtypeEquivRight hprop
        obtain ⟨countEquiv⟩ := topEquiv
        refine ⟨Finite.of_equiv (Sym interval ((size - cut.val) + 1))
          (equivalence.trans countEquiv).symm, ?_⟩
        change Nat.card (Suf cut initialWord gap) =
          (upper - lower - 1 + (size - cut.val)).choose (size + 1 - cut.val)
        rw [Nat.card_congr equivalence, htop, Nat.card_Ioo, hlength]
      · rw [if_neg hlast]
        have hprop (word : List ℕ) :
            (word.length = size + 1 - cut.val ∧
              (∀ value ∈ word, (lower < value ∧ value < upper) ∨
                (upper = maximum ∧ value = maximum)) ∧
              (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧
              lower < word.getD 0 0 ∧ word.getD 0 0 < upper) ↔
            (word.length = (size - cut.val) + 1 ∧ word.Pairwise (· < ·) ∧
              ∀ value ∈ word, value ∈ interval) := by
          constructor
          · rintro ⟨hlen, hall, hpair, hlo, hup⟩
            have hmem : ∀ value ∈ word, value ∈ interval := by
              intro value hv
              rcases hall value hv with hh | hh
              · exact Finset.mem_Ioo.mpr hh
              · exact False.elim (hlast hh.1)
            have hfilterEq : word.filter (· ≠ maximum) = word := by
              apply List.filter_eq_self.mpr
              intro value hv; have hh := hinterval value (hmem value hv)
              simp only [decide_eq_true_eq]; omega
            rw [hfilterEq] at hpair; exact ⟨hlen.trans hlength, hpair, hmem⟩
          · rintro ⟨hlen, hpair, hall⟩
            have hz : 0 < word.length := by omega
            have hh := Finset.mem_Ioo.mp (hall (word.getD 0 0) (by
              rw [List.getD_eq_getElem word 0 hz]; exact List.getElem_mem hz))
            refine ⟨hlen.trans hlength.symm, ?_, hpair.filter _, hh⟩
            intro value hv; exact Or.inl (Finset.mem_Ioo.mp (hall value hv))
        let equivalence := Equiv.subtypeEquivRight hprop
        obtain ⟨countEquiv⟩ := internalEquiv
        refine ⟨Finite.of_equiv (interval.powersetCard ((size - cut.val) + 1))
          (equivalence.trans countEquiv).symm, ?_⟩
        change Nat.card (Suf cut initialWord gap) =
          (upper - lower - 1).choose (size + 1 - cut.val)
        rw [Nat.card_congr equivalence, hinternal, Nat.card_Ioo, hlength]
    let _ : ∀ (cut : Fin (size + 1)) (initialWord : Mono (cut.val + 1))
      (gap : Fin (cut.val + 1)), Finite (Suf cut initialWord gap) :=
        fun cut initialWord gap => (hcount cut initialWord gap).1
    have : Finite Splits := inferInstance
    rw [Nat.card_congr (Equiv.ofBijective join ⟨hinjective, hsurjective⟩).symm,
      Nat.card_sum, Nat.card_congr (dyckEquiv (size + 2)), Nat.card_eq_fintype_card,
      Nat.card_sigma]
    congr 1
    apply Finset.sum_congr rfl
    intro cut _; rw [Nat.card_sigma]; rw [← Equiv.sum_comp (dyckEquiv (cut.val + 1)).symm]
    apply Finset.sum_congr rfl
    intro path _; rw [Nat.card_sigma]
    let initialWord := (dyckEquiv (cut.val + 1)).symm path
    let internal := fun run : ℕ => (run - 1).choose (size + 1 - cut.val)
    let top := fun run : ℕ => (run - 1 + (size - cut.val)).choose (size + 1 - cut.val)
    let scores := initialWord.1.zipWith (fun value prior =>
      if value = initialWord.1.getD cut.val 0 then top (value - prior)
      else internal (value - prior)) (0 :: initialWord.1)
    have hlookup : scores = List.ofFn (fun gap : Fin (cut.val + 1) =>
        if initialWord.1.getD gap.val 0 = initialWord.1.getD cut.val 0 then
          top (initialWord.1.getD gap.val 0 - initialWord.1.getD (gap.val - 1) 0)
        else internal (initialWord.1.getD gap.val 0 -
          initialWord.1.getD (gap.val - 1) 0)) := by
      apply List.ext_getElem
      · simp only [scores, List.length_zipWith, List.length_cons, List.length_ofFn,
          initialWord.2.1]
        omega
      · intro index hs ho
        rw [List.getElem_ofFn]; dsimp only [scores]; rw [List.getElem_zipWith]
        have hi : index < initialWord.1.length := by
          simp only [List.length_ofFn] at ho; rw [initialWord.2.1]; exact ho
        rw [List.getD_eq_getElem initialWord.1 0 hi]
        cases index with
        | zero =>
          have hb := initialWord.2.2.1 0 hi; rw [List.getD_eq_getElem initialWord.1 0 hi] at hb
          have hz : initialWord.1[0] = 0 := by omega
          simp only [List.getElem_cons_zero, Nat.zero_sub, hz,
            List.getD_eq_getElem initialWord.1 0 hi]
        | succ index =>
          rw [List.getElem_cons_succ, Nat.add_sub_cancel,
            List.getD_eq_getElem initialWord.1 0 (show index < initialWord.1.length by omega)]
    have hcounts : (∑ gap : Fin (cut.val + 1), Nat.card (Suf cut initialWord gap)) =
        scores.sum := by
      rw [hlookup, List.sum_ofFn]
      apply Finset.sum_congr rfl
      intro gap _; rw [(hcount cut initialWord gap).2]
    rw [hcounts]
    have hlast : initialWord.1.getLastD 0 = initialWord.1.getD cut.val 0 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        ← List.getD_eq_getElem?_getD, initialWord.2.1, Nat.add_sub_cancel]
    have hint0 : internal 0 = 0 := Nat.choose_eq_zero_of_lt (by
      dsimp [internal]; have := cut.isLt; omega)
    have htop0 : top 0 = 0 := Nat.choose_eq_zero_of_lt (by
      dsimp [top]; have := cut.isLt; omega)
    have hh := InversionSeq152GapWeights.gap_weight_isolation
      internal top hint0 htop0 initialWord.1 0
      initialWord.2.2.2 (fun value _ => Nat.zero_le value)
    dsimp only at hh; rw [hlast] at hh
    change scores.sum = _ at hh; rw [hh]
    have hstats := (Classical.choose_spec
      (InversionSeq152Dyck.monoDyckEquiv (cut.val + 1))).2.2.2 initialWord
    have hpath : (Classical.choose (InversionSeq152Dyck.monoDyckEquiv (cut.val + 1)))
        initialWord = path := (dyckEquiv (cut.val + 1)).apply_symm_apply path
    rw [hpath] at hstats; rw [← hstats]
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
  let Couter := PowerSeries.map (Nat.castRingHom (PowerSeries ℚ)) PowerSeries.catalanSeries
  let geometric : PowerSeries ℚ := PowerSeries.mk fun _ => 1
  let qone : PowerSeries ℚ := 1 + PowerSeries.X
  let weight (q : PowerSeries ℚ) (run : ℕ) := if run = 0 then 0 else q ^ (run - 1) - 1
  let runs (path : DyckWord) :=
    ((path.toList.splitOn DyckStep.U).map List.length).filter (· != 0)
  let gaps (path : DyckWord) := (runs path).dropLast
  let second (path : DyckWord) := (runs path).reverse.getD 1 0
  let height (path : DyckWord) :=
    (path.toList.reverse.takeWhile (· == DyckStep.D)).length
  let Paths (size : ℕ) := {path : DyckWord // path.semilength = size}
  let H (q : PowerSeries ℚ) : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
    ∑ path : Paths size, ((gaps path.val).map (weight q)).sum
  let J (q : PowerSeries ℚ) : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
    ∑ path : Paths size, weight q (second path.val)
  let D (q : PowerSeries ℚ) : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
    ∑ path : Paths size, weight q (height path.val)
  let T := H qone + J geometric - J qone
  have hsecond (path : DyckWord) : second path = (gaps path).getLastD 0 := by
    dsimp only [second, gaps]
    generalize runs path = word
    induction word using List.reverseRecOn with
    | nil => rfl
    | append_singleton word value _ =>
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.getD_cons_succ, List.dropLast_concat]
      rw [List.getLastD_eq_getLast?, ← List.head?_reverse]
      cases word.reverse <;> rfl
  have hweightsum (function : ℕ → ℚ) (hzero : function 0 = 0) : ∀ word : List ℕ,
      (word.map function).sum = (word.dropLast.map function).sum +
        function (word.getLastD 0) := by
    intro word
    induction word using List.reverseRecOn with
    | nil => simp [hzero]
    | append_singleton word value _ => simp
  have honecoeff (run degree : ℕ) (hdegree : 0 < degree) :
      PowerSeries.coeff degree (weight qone run) = ((run - 1).choose degree : ℚ) := by
    by_cases hz : run = 0
    · subst run
      simp [weight, Nat.choose_eq_zero_of_lt hdegree]
    · simp only [weight, if_neg hz, map_sub, PowerSeries.coeff_one,
        if_neg (by omega : degree ≠ 0), sub_zero]
      have heq : (((1 + Polynomial.X : Polynomial ℚ) ^ (run - 1)) : PowerSeries ℚ) =
          qone ^ (run - 1) := by simp [qone]
      rw [← heq, ← Polynomial.coe_pow, Polynomial.coeff_coe,
        Polynomial.coeff_one_add_X_pow]
  have hgeocoeff (run degree : ℕ) (hdegree : 0 < degree) :
      PowerSeries.coeff degree (weight geometric run) =
        ((run - 1 + (degree - 1)).choose degree : ℚ) := by
    cases run with
    | zero => simp [weight, Nat.choose_eq_zero_of_lt (show degree - 1 < degree by omega)]
    | succ run =>
      cases run with
      | zero => simp [weight, Nat.choose_eq_zero_of_lt (show degree - 1 < degree by omega)]
      | succ run =>
        simp only [weight, Nat.succ_ne_zero, if_false, Nat.succ_sub_one, map_sub,
          PowerSeries.coeff_one, if_neg (by omega : degree ≠ 0), sub_zero]
        rw [show geometric ^ (run + 1) = PowerSeries.mk
          (fun index => ((run + index).choose run : ℚ)) from
            PowerSeries.mk_one_pow_eq_mk_choose_add ℚ run]
        rw [PowerSeries.coeff_mk]; have heq : run + 1 + (degree - 1) = run + degree := by omega
        rw [heq, Nat.choose_symm_add]
  have hconst (q : PowerSeries ℚ) (hq : PowerSeries.constantCoeff q = 1) (run : ℕ) :
      PowerSeries.coeff 0 (weight q run) = 0 := by
    by_cases hz : run = 0
    · simp [weight, hz]
    · simp [weight, hz, PowerSeries.coeff_zero_eq_constantCoeff, hq]
  have hqone : PowerSeries.constantCoeff qone = 1 := by simp [qone]
  have hgeo : PowerSeries.constantCoeff geometric = 1 := by simp [geometric]
  have hpathcoeff (path : DyckWord) (degree : ℕ) (hdegree : 0 < degree) :
      PowerSeries.coeff degree
        (((gaps path).map (weight qone)).sum +
          weight geometric (second path) - weight qone (second path)) =
      (((gaps path).dropLast.map (fun run => (run - 1).choose degree)).sum : ℚ) +
        (((gaps path).getLastD 0 - 1 + (degree - 1)).choose degree : ℚ) := by
    rw [map_sub, map_add, map_list_sum]; simp only [List.map_map, Function.comp_def]
    simp_rw [honecoeff _ _ hdegree]
    rw [hgeocoeff _ _ hdegree, hsecond]
    have hh := hweightsum (fun run => ((run - 1).choose degree : ℚ)) (by
      simp [Nat.choose_eq_zero_of_lt hdegree]) (gaps path)
    rw [hh]
    ring
  have hpathconst (path : DyckWord) :
      PowerSeries.coeff 0
        (((gaps path).map (weight qone)).sum +
          weight geometric (second path) - weight qone (second path)) = 0 := by
    simp only [map_sub, map_add, map_list_sum, List.map_map, Function.comp_def]
    simp [hconst qone hqone, hconst geometric hgeo]
  have hzero (path : DyckWord) (hsize : path.semilength = 0) : path = 0 := by
    apply DyckWord.toList_eq_nil.mp
    apply List.length_eq_zero_iff.mp
    rw [← DyckWord.two_mul_semilength_eq_length, hsize, mul_zero]
  have hTcoeff (index degree : ℕ) : PowerSeries.coeff degree (PowerSeries.coeff index T) =
      ∑ path : Paths index, PowerSeries.coeff degree
        (((gaps path.val).map (weight qone)).sum +
          weight geometric (second path.val) - weight qone (second path.val)) := by
    simp only [T, H, J, map_sub, map_add, PowerSeries.coeff_mk, map_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hTconst (index : ℕ) : PowerSeries.coeff 0 (PowerSeries.coeff index T) = 0 := by
    rw [hTcoeff]; simp only [hpathconst, Finset.sum_const_zero]
  have hTzero (degree : ℕ) : PowerSeries.coeff degree (PowerSeries.coeff 0 T) = 0 := by
    rw [hTcoeff]
    apply Finset.sum_eq_zero
    intro path _; have hh := hzero path.val path.property
    have hnil : path.val.toList = [] := DyckWord.toList_eq_nil.mpr hh
    simp [gaps, runs, second, weight, hnil]
  have hTouterzero : PowerSeries.constantCoeff T = 0 := by
    ext degree
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_zero] using hTzero degree
  have hactual : C + diagonal T =
      1 + PowerSeries.X + PowerSeries.X ^ 2 * PowerSeries.mk fun size =>
        (Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 2)
          [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]]} : ℚ) := by
    ext degree
    rw [map_add, hdiagonal]
    cases degree with
    | zero => simp [C, hTouterzero, PowerSeries.coeff_X_pow_mul']
    | succ degree =>
      cases degree with
      | zero => simp [C, hTouterzero, hTconst, Finset.sum_range_succ,
          PowerSeries.coeff_X_pow_mul']
      | succ size =>
        simp only [map_add]; rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
        simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one,
          PowerSeries.coeff_X, if_neg (by omega : size + 1 + 1 ≠ 0),
          if_neg (by omega : size + 1 + 1 ≠ 1), zero_add,
          show size + 1 + 1 - 2 = size from by omega]
        rw [hleftcount, Nat.cast_add]
        simp only [C, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff,
          DyckWord.card_dyckWord_semilength_eq_catalan]
        congr 1
        rw [Finset.sum_range_succ]
        simp only [show size + 1 + 1 = size + 2 from by omega, Nat.sub_self,
          hTconst, add_zero]
        rw [show size + 2 = (size + 1) + 1 from rfl, Finset.sum_range_succ']; rw [hTzero, add_zero]
        rw [Fin.sum_univ_eq_sum_range (fun index : ℕ =>
          ∑ path : Paths (index + 1), (
            ((gaps path.val).dropLast.map
              (fun run => (run - 1).choose (size + 1 - index))).sum +
            ((gaps path.val).getLastD 0 - 1 + (size - index)).choose
              (size + 1 - index))) (size + 1)]
        simp only [Nat.cast_sum, Nat.cast_add]
        apply Finset.sum_congr rfl
        intro index hi; simp only [Finset.mem_range] at hi; rw [hTcoeff]
        apply Finset.sum_congr rfl
        intro path _; rw [hpathcoeff _ _ (by omega)]
        simp only [Nat.cast_list_sum, List.map_map, Function.comp_def]
        rw [show size + 1 + 1 - (index + 1) = size + 1 - index from by omega,
          show size + 1 - index - 1 = size - index from by omega]
  have hcast (size : ℕ) : (size : PowerSeries ℚ) = PowerSeries.C (size : ℚ) :=
    (map_natCast PowerSeries.C size).symm
  have hCdiagonal : diagonal Couter = C := by
    ext degree
    rw [hdiagonal]; simp only [Couter, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff, C]
    rw [Finset.sum_eq_single degree]
    · rw [Nat.sub_self]
      change PowerSeries.coeff 0 (catalan degree : PowerSeries ℚ) = _
      rw [hcast, PowerSeries.coeff_zero_C]; rfl
    · intro index hi hne
      simp only [Finset.mem_range] at hi; have hn : degree - index ≠ 0 := by omega
      change PowerSeries.coeff (degree - index) (catalan index : PowerSeries ℚ) = 0
      rw [hcast, PowerSeries.coeff_C_of_ne_zero hn]
    · simp
  have hCX (value : PowerSeries ℚ) : diagonal (PowerSeries.C value) = value := by
    dsimp only [diagonal]; rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_C _ _ value
  have hX : diagonal PowerSeries.X = (PowerSeries.X : PowerSeries ℚ) := by
    dsimp only [diagonal]; rw [PowerSeries.coe_eval₂Hom]; exact PowerSeries.eval₂_X _ _
  have hcat : C * (1 - PowerSeries.X * C) = 1 := by
    have hh := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simp only [map_add, map_mul, map_one, PowerSeries.map_X, map_pow] at hh; dsimp [C]
    linear_combination -hh
  let t := PowerSeries.X * C
  have hxcat : t * (1 - t) = PowerSeries.X := by
    dsimp [t]
    linear_combination PowerSeries.X * hcat
  have hmarked (q : PowerSeries ℚ) :
      (2 - C) * diagonal (H q) = (C - 1) * diagonal (D q) := by
    have hh := InversionSeq152MarkedSeries.marked_interior_descent_enumeration
      (weight q) (by simp [weight])
    change (2 - Couter) * H q = (Couter - 1) * D q at hh; have hd := congrArg diagonal hh
    simpa only [map_mul, map_sub, map_ofNat, map_one, hCdiagonal] using hd
  have hpenultimate (q : PowerSeries ℚ) :
      (1 - PowerSeries.X) * diagonal (J q) = t * diagonal (D q) := by
    have hh := InversionSeq152PenultimateSeries.penultimate_descent_enumeration
      (weight q) (by simp [weight])
    change (1 - PowerSeries.X) * J q = PowerSeries.X * Couter * D q at hh
    have hd := congrArg diagonal hh
    simpa only [map_mul, map_sub, map_one, hX, hCdiagonal, t] using hd
  have hpositive (path : DyckWord) (hne : path ≠ 0) : 0 < height path := by
    have hword := DyckWord.cons_tail_dropLast_concat hne; have hr := congrArg List.reverse hword
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
    dsimp only [height]; rw [← hr]
    simp
  have hD (q : PowerSeries ℚ) (hq : PowerSeries.constantCoeff q = 1) :
      (1 - q * t) * diagonal (D q) = C * t ^ 2 * (q - 1) := by
    let F : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun size =>
      ∑ path : Paths size, q ^ height path.val
    have hqd : PowerSeries.C q * D q =
        F - 1 - PowerSeries.C q * (Couter - 1) := by
      apply PowerSeries.ext
      intro size; rw [PowerSeries.coeff_C_mul]
      cases size with
      | zero =>
        simp only [D, F, PowerSeries.coeff_mk]
        have hp (path : Paths 0) : path.val = 0 := hzero path.val path.property
        have hg : ∀ path : Paths 0, height path.val = 0 := by
          intro path; rw [hp path]; rfl
        simp [hg, weight, Couter, Paths, DyckWord.card_dyckWord_semilength_eq_catalan,
          PowerSeries.coeff_C_mul, map_sub]
      | succ size =>
        have hp (path : Paths (size + 1)) : 0 < height path.val := hpositive path.val (by
          intro hz; have hh := path.property; rw [hz, DyckWord.semilength_zero] at hh
          omega)
        simp only [D, F, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
          PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, sub_zero]
        rw [Finset.mul_sum]; have hw (path : Paths (size + 1)) :
            q * weight q (height path.val) = q ^ height path.val - q := by
          have hh := hp path; dsimp [weight]; rw [if_neg (by omega)]; rw [mul_sub, mul_one]
          have heq : q * q ^ (height path.val - 1) = q ^ height path.val := by
            rw [← pow_succ']
            congr 1
            omega
          rw [heq]
        simp_rw [hw]
        rw [Finset.sum_sub_distrib]
        simp [Couter, Paths, DyckWord.card_dyckWord_semilength_eq_catalan, mul_comm]
    have hheight : (1 - PowerSeries.C q * PowerSeries.X * Couter) * F = 1 :=
      InversionSeq152FinalSeries.final_descent_enumeration q
    have hheightdiag : (1 - q * t) * diagonal F = 1 := by
      have hh := congrArg diagonal hheight
      simpa only [map_mul, map_sub, map_one, hCX, hX, hCdiagonal, t, mul_assoc] using hh
    have hqdiag : q * diagonal (D q) = diagonal F - 1 - q * (C - 1) := by
      have hh := congrArg diagonal hqd
      simpa only [map_mul, map_sub, map_one, hCX, hCdiagonal] using hh
    have hne : q ≠ 0 := by
      intro hz; rw [hz, map_zero] at hq; exact zero_ne_one hq
    apply mul_left_cancel₀ hne
    have hc : C * (1 - t) = 1 := hcat
    linear_combination (1 - q * t) * hqdiag + hheightdiag +
      q * (q * t - t - 1) * hc
  have hgeoinv : (1 - PowerSeries.X) * geometric = 1 := by
    have heq : geometric = PowerSeries.mk (1 : ℕ → ℚ) := by
      ext degree
      simp [geometric]
    rw [heq, mul_comm]; exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  have hdone : (1 - t) * (1 - t ^ 2) * diagonal (D qone) = t ^ 3 := by
    have hh := hD qone hqone; have hc : C * (1 - t) = 1 := hcat; dsimp only [qone] at hh
    linear_combination hh - (t * diagonal (D qone) + C * t ^ 2) * hxcat + t ^ 3 * hc
  have hdtwo : (1 - t) ^ 2 * diagonal (D geometric) = t ^ 3 := by
    have hh := hD geometric hgeo; have hc : C * (1 - t) = 1 := hcat
    linear_combination (1 - PowerSeries.X) * hh +
      (t * diagonal (D geometric) + C * t ^ 2) * hgeoinv -
      (diagonal (D geometric) + C * t ^ 2) * hxcat + t ^ 3 * hc
  have htdiff : diagonal (D geometric) - diagonal (D qone) =
      t * diagonal (D qone) := by
    have hn : (1 - t) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro hz; have hh := congrArg PowerSeries.constantCoeff hz; simp [t] at hh
    apply mul_left_cancel₀ hn
    linear_combination hdtwo - hdone
  have hc : C * (1 - t) = 1 := hcat; have hW : (2 - C) * (1 - PowerSeries.X) * diagonal T =
      (C - 1) * (1 - PowerSeries.X) * diagonal (D qone) +
        (2 - C) * t ^ 2 * diagonal (D qone) := by
    dsimp only [T]; rw [map_sub, map_add]
    linear_combination (1 - PowerSeries.X) * hmarked qone +
      (2 - C) * hpenultimate geometric - (2 - C) * hpenultimate qone +
      (2 - C) * t * htdiff
  have hWnorm : (1 - PowerSeries.X) * (1 - 2 * t) * diagonal T =
      t * (1 - t ^ 2) * diagonal (D qone) := by
    linear_combination (1 - t) * hW +
      ((1 - PowerSeries.X) * diagonal T +
        (1 - PowerSeries.X - t ^ 2) * diagonal (D qone)) * hc +
      t * diagonal (D qone) * hxcat
  have hS : (1 - PowerSeries.X) * (1 - 2 * t) * diagonal T = C * t ^ 4 := by
    linear_combination hWnorm + C * t * hdone -
      t * (1 - t ^ 2) * diagonal (D qone) * hc
  let actualLeft := 1 + PowerSeries.X + PowerSeries.X ^ 2 * PowerSeries.mk fun size =>
    (Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 2)
      [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]]} : ℚ)
  let actualRight := 1 + PowerSeries.X * PowerSeries.mk fun size =>
    (Nat.card {word : List ℕ // word ∈ InversionSeqDefs.avoiders (size + 1)
      [[1, 2, 2], [3, 1, 2], [3, 2, 1]]} : ℚ)
  have hleftEq : 2 * (1 - PowerSeries.X) * (1 - 2 * t) * (actualLeft - 1) =
      PowerSeries.X * (2 - 2 * t) := by
    rw [show actualLeft = C + diagonal T from hactual.symm]
    linear_combination 2 * hS +
      (2 * (1 - 2 * t) * (C - 1) + 2 - 2 * t) * hxcat +
      (2 - 4 * t + 2 * t ^ 2 - 2 * t ^ 3) * hc
  have hrightEq : 2 * (1 - PowerSeries.X) * (1 - 2 * t) * (actualRight - 1) =
      PowerSeries.X * (2 - 2 * t) :=
    InversionSeq152RightCount.right_avoider_enumeration
  have heq : actualLeft = actualRight := by
    have hn : (2 * (1 - PowerSeries.X) * (1 - 2 * t) : PowerSeries ℚ) ≠ 0 := by
      intro hz; have hh := congrArg PowerSeries.constantCoeff hz
      simp only [map_mul, map_sub, map_one, map_ofNat, t,
        PowerSeries.constantCoeff_X, zero_mul, mul_zero, sub_zero] at hh
      norm_num at hh
    have hh := mul_left_cancel₀ hn (hleftEq.trans hrightEq.symm)
    linear_combination hh
  have hshort (size : ℕ) (hsize : size ≤ 1) :
      InversionSeqDefs.avoiders size [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]] =
        InversionSeqDefs.avoiders size [[1, 2, 2], [3, 1, 2], [3, 2, 1]] := by
    ext word
    have hno (pattern : List ℕ) (hpattern : pattern.length = 3)
        (hword : word.length = size) : ¬ NonnestingDefs.Occurs pattern word := by
      rintro ⟨values, _, _, hsub, _⟩
      have hh := hsub.length_le; simp only [List.length_map, hpattern, hword] at hh; omega
    constructor
    · rintro ⟨hlen, hinv, _⟩; refine ⟨hlen, hinv, ?_⟩
      intro pattern hp; apply hno pattern ?_ hlen
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · rintro ⟨hlen, hinv, _⟩; refine ⟨hlen, hinv, ?_⟩
      intro pattern hp; apply hno pattern ?_ hlen
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> rfl
  intro size; cases size with
  | zero => rw [hshort 0 (by omega)]
  | succ size =>
    cases size with
    | zero => rw [hshort 1 (by omega)]
    | succ size =>
      have hh := congrArg (PowerSeries.coeff (size + 2)) heq
      simp only [actualLeft, actualRight, map_add,
        PowerSeries.coeff_one, if_neg (by omega : size + 2 ≠ 0),
        PowerSeries.coeff_X, if_neg (by omega : size + 2 ≠ 1), zero_add,
        PowerSeries.coeff_X_pow_mul', if_pos (by omega : 2 ≤ size + 2),
        Nat.add_sub_cancel, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk] at hh
      exact_mod_cast hh
end D5.S3.Combinatorics.InversionSeq.InversionSeqClass152
