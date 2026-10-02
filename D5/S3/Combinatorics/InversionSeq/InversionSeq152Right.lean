/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Right
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Right
   mirror-E: none(waiver:last-zero-structure)
   anchors: []
   utility: none
   digest: Repeated positive values and last-zero triples characterize the right avoidance class. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Right

open D5.S3.Combinatorics Nonnesting InversionSeqOccurs

theorem avoid011_iff_positive_distinct (word : List ℕ)
    (hseq : InversionSeqDefs.IsInversionSeq word) :
    (¬ NonnestingDefs.Occurs [1, 2, 2] word) ↔
    ∀ first second, first < second → second < word.length →
      0 < word.getD first 0 → word.getD first 0 ≠ word.getD second 0 := by
  have pat011 := occurs_three_iff 1 2 2 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  constructor
  · intro havoid first second horder hlength hpositive heq
    have hzero : word.getD 0 0 = 0 := by
      have := hseq 0 (by omega)
      omega
    have hfirst : 0 < first := by
      by_contra hnot
      have heqindex : first = 0 := by omega
      subst first
      omega
    apply havoid
    apply pat011.mpr
    exact ⟨0, first, second, hfirst, horder, hlength,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro hdistinct hoccurs
    obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
      pat011.mp hoccurs
    have hlt : word.getD first 0 < word.getD second 0 := hab.mp (by omega)
    have heq : word.getD second 0 = word.getD third 0 := hebc.mp rfl
    exact hdistinct second third hst hthird (by omega) heq

theorem right_last_zero_structure (word : List ℕ)
    (hseq : InversionSeqDefs.IsInversionSeq word)
    (lastZero : ℕ) (hlast : lastZero < word.length)
    (hzero : word.getD lastZero 0 = 0)
    (hnonzero : ∀ position, lastZero < position → position < word.length →
      word.getD position 0 ≠ 0) :
    (¬ NonnestingDefs.Occurs [1, 2, 2] word ∧
      ¬ NonnestingDefs.Occurs [3, 1, 2] word ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] word) ↔
    (∀ first second, first < second → second < word.length →
      0 < word.getD first 0 → word.getD first 0 ≠ word.getD second 0) ∧
    (∀ first second, first < second → second ≤ lastZero →
      0 < word.getD first 0 → 0 < word.getD second 0 →
      word.getD first 0 < word.getD second 0) ∧
    (∀ preindex ≤ lastZero, ∀ suffix, lastZero < suffix → suffix < word.length →
      word.getD preindex 0 < word.getD suffix 0) ∧
    (∀ first second third, lastZero < first → first < second → second < third →
      third < word.length →
      ¬ (word.getD second 0 < word.getD first 0 ∧
        word.getD third 0 < word.getD first 0)) := by
  have pat201 := occurs_three_iff 3 1 2 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat210 := occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  constructor
  · rintro ⟨h011, h201, h210⟩
    have hdistinct := (avoid011_iff_positive_distinct word hseq).mp h011
    refine ⟨hdistinct, ?_, ?_, ?_⟩
    · intro first second hfs hsecond hfirstpos hsecondpos
      have hne := hdistinct first second hfs (by omega) hfirstpos
      have hnezero : second ≠ lastZero := by
        intro heq
        subst second
        omega
      by_contra hnot
      apply h210
      apply pat210.mpr
      exact ⟨first, second, lastZero, hfs, by omega, hlast,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
    · intro preindex hpreindex suffix hsuffix hlength
      have hpos : 0 < word.getD suffix 0 := by
        have := hnonzero suffix hsuffix hlength
        omega
      by_cases hprepos : 0 < word.getD preindex 0
      · have hne := hdistinct preindex suffix (by omega) hlength hprepos
        have hprezero : preindex ≠ lastZero := by
          intro heq
          subst preindex
          omega
        by_contra hnot
        apply h201
        apply pat201.mpr
        exact ⟨preindex, lastZero, suffix, by omega, hsuffix, hlength,
          by omega, by omega, by omega, by omega, by omega, by omega⟩
      · omega
    · intro first second third hfirst hfs hst hthird ⟨hsecond, hthirdval⟩
      have hpos : 0 < word.getD second 0 := by
        have := hnonzero second (by omega) (by omega)
        omega
      have hne := hdistinct second third hst hthird hpos
      by_cases horder : word.getD second 0 < word.getD third 0
      · apply h201
        apply pat201.mpr
        exact ⟨first, second, third, hfs, hst, hthird,
          by omega, by omega, by omega, by omega, by omega, by omega⟩
      · apply h210
        apply pat210.mpr
        exact ⟨first, second, third, hfs, hst, hthird,
          by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rintro ⟨hdistinct, hincreasing, hseparated, hsmaller⟩
    have hfirstlargest : ∀ first second third,
        first < second → second < third → third < word.length →
        word.getD second 0 < word.getD first 0 →
        word.getD third 0 < word.getD first 0 →
        word.getD second 0 ≠ word.getD third 0 → False := by
      intro first second third hfs hst hthird hsecond hthirdval hne
      by_cases hfirst : lastZero < first
      · exact hsmaller first second third hfirst hfs hst hthird ⟨hsecond, hthirdval⟩
      · have hthirdpre : third ≤ lastZero := by
          by_contra hnot
          have := hseparated first (by omega) third (by omega) hthird
          omega
        have hfirstpos : 0 < word.getD first 0 := by omega
        have hsecondzero : word.getD second 0 = 0 := by
          by_contra hnot
          have := hincreasing first second hfs (by omega) hfirstpos (by omega)
          omega
        have hthirdzero : word.getD third 0 = 0 := by
          by_contra hnot
          have := hincreasing first third (by omega) hthirdpre hfirstpos (by omega)
          omega
        omega
    refine ⟨(avoid011_iff_positive_distinct word hseq).mpr hdistinct, ?_, ?_⟩
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat201.mp hoccurs
      exact hfirstlargest first second third hfs hst hthird
        (by omega) (by omega) (by omega)
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat210.mp hoccurs
      exact hfirstlargest first second third hfs hst hthird
        (by omega) (by omega) (by omega)

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Right
