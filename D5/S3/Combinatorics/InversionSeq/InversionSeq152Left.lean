/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Left
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Left
   mirror-E: none(waiver:first-descent-structure)
   anchors: []
   utility: none
   digest: Low-value uniqueness and maximum descents give the left class gap decomposition. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Left

open D5.S3.Combinatorics Nonnesting InversionSeqOccurs

theorem low_value_unique (word : List ℕ)
    (h010 : ¬ NonnestingDefs.Occurs [1, 2, 1] word)
    (h100 : ¬ NonnestingDefs.Occurs [2, 1, 1] word)
    (high low : ℕ) (horder : high < low) (hlow : low < word.length)
    (hdrop : word.getD low 0 < word.getD high 0) :
    ∀ other < word.length, word.getD other 0 = word.getD low 0 → other = low := by
  have pat010 := occurs_three_iff 1 2 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat100 := occurs_three_iff 2 1 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  intro other hother heq
  by_contra hne
  have hhigh : other ≠ high := by
    intro hequal
    subst other
    omega
  by_cases hbefore : other < high
  · apply h010
    apply pat010.mpr
    exact ⟨other, high, low, hbefore, horder, hlow, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
  · by_cases hbetween : other < low
    · apply h100
      apply pat100.mpr
      exact ⟨high, other, low, by omega, hbetween, hlow, by omega, by omega,
        by omega, by omega, by omega, by omega⟩
    · apply h100
      apply pat100.mpr
      exact ⟨high, low, other, horder, by omega, hother, by omega, by omega,
        by omega, by omega, by omega, by omega⟩

theorem descent_global_maximum (word : List ℕ)
    (h102 : ¬ NonnestingDefs.Occurs [2, 1, 3] word)
    (h210 : ¬ NonnestingDefs.Occurs [3, 2, 1] word)
    (descent : ℕ) (hdescent : descent + 1 < word.length)
    (hdrop : word.getD (descent + 1) 0 < word.getD descent 0) :
    ∀ position < word.length, word.getD position 0 ≤ word.getD descent 0 := by
  have pat102 := occurs_three_iff 2 1 3 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat210 := occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  intro position hposition
  by_contra hlarge
  have hne : position ≠ descent := by
    intro heq
    subst position
    omega
  have hnext : position ≠ descent + 1 := by
    intro heq
    subst position
    omega
  by_cases hbefore : position < descent
  · apply h210
    apply pat210.mpr
    exact ⟨position, descent, descent + 1, hbefore, by omega, hdescent,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  · apply h102
    apply pat102.mpr
    exact ⟨descent, descent + 1, position, by omega, by omega, hposition,
      by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem first_descent_structure (word : List ℕ) (descent : ℕ)
    (hdescent : descent + 1 < word.length)
    (hprefix : ∀ first second : ℕ, first ≤ second → second ≤ descent →
      word.getD first 0 ≤ word.getD second 0)
    (hdrop : word.getD (descent + 1) 0 < word.getD descent 0) :
    (¬ NonnestingDefs.Occurs [1, 2, 1] word ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1] word ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] word ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] word) ↔
    (∀ position < word.length, word.getD position 0 ≤ word.getD descent 0) ∧
    (∀ suffix, descent < suffix → suffix < word.length →
      word.getD suffix 0 < word.getD descent 0 →
      ∀ preindex ≤ descent, word.getD preindex 0 ≠ word.getD suffix 0) ∧
    (∀ first second, descent < first → first < second → second < word.length →
      word.getD first 0 < word.getD descent 0 →
      word.getD second 0 < word.getD descent 0 →
      word.getD first 0 < word.getD second 0) ∧
    (∀ preindex ≤ descent, word.getD preindex 0 < word.getD descent 0 →
      word.getD (descent + 1) 0 < word.getD preindex 0 →
      ∀ suffix, descent < suffix → suffix < word.length →
        word.getD suffix 0 < word.getD preindex 0) := by
  have pat010 := occurs_three_iff 1 2 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat100 := occurs_three_iff 2 1 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat102 := occurs_three_iff 2 1 3 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  have pat210 := occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
    (by intro rank hrank hmax; omega)
  constructor
  · rintro ⟨h010, h100, h102, h210⟩
    have hmax := descent_global_maximum word h102 h210 descent hdescent hdrop
    have hunique := low_value_unique word h010 h100
    refine ⟨hmax, ?_, ?_, ?_⟩
    · intro suffix hsuffix hlength hlow preindex hprefixindex heq
      have := hunique descent suffix hsuffix hlength hlow preindex (by omega) heq
      omega
    · intro first second hfirst hsecond hlength hfirstlow hsecondlow
      have hne : word.getD first 0 ≠ word.getD second 0 := by
        intro heq
        have := hunique descent second (by omega) hlength hsecondlow first (by omega) heq
        omega
      by_contra hnot
      apply h210
      apply pat210.mpr
      exact ⟨descent, first, second, hfirst, hsecond, hlength,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
    · intro preindex hprefixindex hprefixlow habovey suffix hsuffix hlength
      have hne : word.getD preindex 0 ≠ word.getD suffix 0 := by
        intro heq
        have hlow : word.getD suffix 0 < word.getD descent 0 := by omega
        have := hunique descent suffix hsuffix hlength hlow preindex (by omega) heq
        omega
      by_contra hnot
      apply h102
      apply pat102.mpr
      have hnext : suffix ≠ descent + 1 := by
        intro heq
        subst suffix
        omega
      exact ⟨preindex, descent + 1, suffix, by omega, by omega, hlength,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rintro ⟨hmax, habsent, hincreasing, hgap⟩
    have hlowunique : ∀ first second, first < second → second < word.length →
        word.getD first 0 = word.getD second 0 →
        word.getD first 0 < word.getD descent 0 → second ≤ descent := by
      intro first second hfirst hlength heq hlow
      by_contra hsecond
      by_cases hp : first ≤ descent
      · exact habsent second (by omega) hlength (by omega) first hp heq
      · have := hincreasing first second (by omega) hfirst hlength hlow (by omega)
        omega
    have hymin : ∀ suffix, descent < suffix → suffix < word.length →
        word.getD (descent + 1) 0 ≤ word.getD suffix 0 := by
      intro suffix hsuffix hlength
      by_cases heq : suffix = descent + 1
      · subst suffix; exact le_rfl
      · by_cases hlow : word.getD suffix 0 < word.getD descent 0
        · have := hincreasing (descent + 1) suffix (by omega) (by omega)
            hlength hdrop hlow
          omega
        · have := hmax suffix hlength
          omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat010.mp hoccurs
      have hlt : word.getD first 0 < word.getD second 0 := hab.mp (by omega)
      have heq : word.getD first 0 = word.getD third 0 := heac.mp rfl
      have hlow : word.getD first 0 < word.getD descent 0 := by
        have := hmax second (by omega)
        omega
      have hp := hlowunique first third (by omega) hthird heq hlow
      have := hprefix second third (by omega) hp
      omega
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat100.mp hoccurs
      have hlt : word.getD second 0 < word.getD first 0 := by omega
      have heq : word.getD second 0 = word.getD third 0 := hebc.mp rfl
      have hlow : word.getD second 0 < word.getD descent 0 := by
        have := hmax first (by omega)
        omega
      have hp := hlowunique second third hst hthird heq hlow
      have := hprefix first second (by omega) (by omega)
      omega
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat102.mp hoccurs
      have hfsval : word.getD second 0 < word.getD first 0 := by omega
      have hftval : word.getD first 0 < word.getD third 0 := hac.mp (by omega)
      have hfirstlow : word.getD first 0 < word.getD descent 0 := by
        have := hmax third hthird
        omega
      have hsecondlow : word.getD second 0 < word.getD descent 0 := by omega
      have hsecond : descent < second := by
        by_contra hnot
        have := hprefix first second (by omega) (by omega)
        omega
      by_cases hp : first ≤ descent
      · have hneq := habsent second hsecond (by omega) hsecondlow first hp
        have hy := hymin second hsecond (by omega)
        have hg := hgap first hp hfirstlow (by omega) third (by omega) hthird
        omega
      · have := hincreasing first second (by omega) hfs (by omega)
          hfirstlow hsecondlow
        omega
    · intro hoccurs
      obtain ⟨first, second, third, hfs, hst, hthird, hab, hac, hbc, heab, heac, hebc⟩ :=
        pat210.mp hoccurs
      have hfsval : word.getD second 0 < word.getD first 0 := by omega
      have hstval : word.getD third 0 < word.getD second 0 := by omega
      have hsecond : descent < second := by
        by_contra hnot
        have := hprefix first second (by omega) (by omega)
        omega
      have hsecondlow : word.getD second 0 < word.getD descent 0 := by
        have := hmax first (by omega)
        omega
      have := hincreasing second third hsecond hst hthird hsecondlow (by omega)
      omega

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Left
