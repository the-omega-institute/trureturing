/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207RightStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207RightStructure
   mirror-E: none(waiver:right-descent-endpoint-witnesses)
   anchors: []
   utility: none
   digest: Forbidden triples restrict right descent tops to mutually exclusive endpoints. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Maximum
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Append

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207RightStructure

open D5.S3.Combinatorics.Nonnesting InversionSeqOccurs
open InversionSeq207Append InversionSeq207Maximum

theorem right_descent_classification (word : List ℕ)
    (hword : word ∈ InversionSeqDefs.avoiders word.length
      [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]])
    (maximumIndex : ℕ) (hmaximumIndex : maximumIndex < word.length)
    (hmaximum : ∀ index < word.length,
      word.getD index 0 ≤ word.getD maximumIndex 0) :
    (∀ index < word.length,
      word.getD index 0 ≤ secondLargest word ∨
        word.getD index 0 = word.getD maximumIndex 0) ∧
    (∀ top bottom : ℕ, top < bottom → bottom < word.length →
      word.getD bottom 0 < word.getD top 0 → secondLargest word ≤ word.getD top 0 →
      secondLargest word < word.getD maximumIndex 0 ∧
        (word.getD top 0 = secondLargest word ∨
          word.getD top 0 = word.getD maximumIndex 0)) ∧
    ¬ ((∃ top bottom : ℕ, top < bottom ∧ bottom < word.length ∧
          word.getD top 0 = secondLargest word ∧ word.getD bottom 0 < word.getD top 0) ∧
        (∃ top bottom : ℕ, top < bottom ∧ bottom < word.length ∧
          word.getD top 0 = word.getD maximumIndex 0 ∧
            word.getD bottom 0 < word.getD top 0)) := by
  have hpairs (first second : ℕ) (hfirst : first < second)
      (hsecond : second < word.length) :
      min (word.getD first 0) (word.getD second 0) ≤ secondLargest word := by
    unfold secondLargest
    exact le_trans
      (Finset.le_sup (f := fun index => min (word.getD index 0) (word.getD second 0))
        (Finset.mem_range.mpr hfirst))
      (Finset.le_sup (f := fun later => (Finset.range later).sup fun earlier =>
        min (word.getD earlier 0) (word.getD later 0)) (Finset.mem_range.mpr hsecond))
  have hentries (index : ℕ) (hindex : index < word.length) :
      word.getD index 0 ≤ secondLargest word ∨
        word.getD index 0 = word.getD maximumIndex 0 := by
    by_cases heq : index = maximumIndex
    · subst index
      exact Or.inr rfl
    · have hbound := hmaximum index hindex
      rcases lt_or_gt_of_ne heq with hbefore | hafter
      · have := hpairs index maximumIndex hbefore hmaximumIndex
        rw [min_eq_left hbound] at this
        exact Or.inl this
      · have := hpairs maximumIndex index hafter hindex
        rw [min_eq_right hbound] at this
        exact Or.inl this
  have h101 (first second third : ℕ) (hfirst : first < second)
      (hsecond : second < third) (hthird : third < word.length)
      (heq : word.getD first 0 = word.getD third 0)
      (hlt : word.getD second 0 < word.getD first 0) : False := by
    apply hword.2.2 [2, 1, 2] (by simp)
    apply (occurs_three_iff 2 1 2 word (by omega) (by omega) (by omega) (by omega)).mpr
    exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
  have htwo (first second third : ℕ) (hfirst : first < second)
      (hsecond : second < third) (hthird : third < word.length)
      (hleft : word.getD third 0 < word.getD first 0)
      (hright : word.getD third 0 < word.getD second 0) : False := by
    rcases lt_trichotomy (word.getD first 0) (word.getD second 0) with hlt | heq | hgt
    · apply hword.2.2 [2, 3, 1] (by simp)
      apply (occurs_three_iff 2 3 1 word (by omega) (by omega) (by omega) (by omega)).mpr
      exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
    · apply hword.2.2 [2, 2, 1] (by simp)
      apply (occurs_three_iff 2 2 1 word (by omega) (by omega) (by omega) (by omega)).mpr
      exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
    · apply hword.2.2 [3, 2, 1] (by simp)
      apply (occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega) (by omega)).mpr
      exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
  have hdescendingMaximum (top bottom : ℕ) (htop : top < bottom)
      (hbottom : bottom < word.length)
      (heq : word.getD top 0 = word.getD maximumIndex 0)
      (hlt : word.getD bottom 0 < word.getD top 0) :
      secondLargest word < word.getD maximumIndex 0 := by
    have htoplen : top < word.length := by omega
    have hmaxTop : ∀ index < word.length, word.getD index 0 ≤ word.getD top 0 := by
      intro index hindex
      rw [heq]
      exact hmaximum index hindex
    have hunique (index : ℕ) (hindex : index < word.length)
        (hsame : word.getD index 0 = word.getD top 0) : index = top := by
      by_cases hbefore : index < top
      · have hmaxIndex : ∀ entry < word.length,
            word.getD entry 0 ≤ word.getD index 0 := by
          intro entry hentry
          rw [hsame]
          exact hmaxTop entry hentry
        have hterminal := (maximum_decomposition word
          [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] (Or.inr rfl)
          hword index hmaxIndex).1 top hbefore htoplen hsame.symm bottom
          (by omega) hbottom
        omega
      · by_cases hsameIndex : top = index
        · exact hsameIndex.symm
        · have hterminal := (maximum_decomposition word
            [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] (Or.inr rfl)
            hword top hmaxTop).1 index (by omega) hindex hsame bottom
            htop hbottom
          omega
    have hpositive : 0 < word.getD top 0 := by omega
    have hstrict : secondLargest word ≤ word.getD top 0 - 1 := by
      simp only [secondLargest, Finset.sup_le_iff, Finset.mem_range]
      intro second hsecond first hfirst
      have hfirstlen : first < word.length := by omega
      have hfirstmax := hmaxTop first hfirstlen
      have hsecondmax := hmaxTop second hsecond
      by_contra hmin
      have heqFirst : word.getD first 0 = word.getD top 0 := by omega
      have heqSecond : word.getD second 0 = word.getD top 0 := by omega
      have := hunique first hfirstlen heqFirst
      have := hunique second hsecond heqSecond
      omega
    omega
  refine ⟨hentries, ?_, ?_⟩
  · intro top bottom htop hbottom hdescent hsecond
    have htoplen : top < word.length := by omega
    rcases hentries top htoplen with hlow | hhigh
    · have heq : word.getD top 0 = secondLargest word := by omega
      have hmax := hmaximum top htoplen
      have hne : word.getD top 0 ≠ word.getD maximumIndex 0 := by
        intro heqMax
        have := hdescendingMaximum top bottom htop hbottom heqMax hdescent
        omega
      exact ⟨by omega, Or.inl heq⟩
    · exact ⟨hdescendingMaximum top bottom htop hbottom hhigh hdescent, Or.inr hhigh⟩
  · rintro ⟨⟨lowerTop, lowerBottom, hlower, hlowerlen, hlowerEq, hlowerDescent⟩,
      ⟨upperTop, upperBottom, hupper, hupperlen, hupperEq, hupperDescent⟩⟩
    have hgap := hdescendingMaximum upperTop upperBottom hupper hupperlen
      hupperEq hupperDescent
    have htopDifferent : lowerTop ≠ upperTop := by
      intro heq
      subst upperTop
      omega
    have hafter : lowerBottom < upperTop := by
      by_contra hnot
      by_cases heq : lowerBottom = upperTop
      · subst upperTop
        omega
      · have hupperBefore : upperTop < lowerBottom := by omega
        rcases lt_or_gt_of_ne htopDifferent with hbefore | hafter
        · exact htwo lowerTop upperTop lowerBottom hbefore hupperBefore hlowerlen
            hlowerDescent (by omega)
        · exact htwo upperTop lowerTop lowerBottom hafter hlower hlowerlen
            (by omega) hlowerDescent
    rcases hentries upperBottom hupperlen with hlow | hhigh
    · by_cases hstrict : word.getD upperBottom 0 < secondLargest word
      · exact htwo lowerTop upperTop upperBottom (by omega) hupper hupperlen
          (by omega) hupperDescent
      · have heq : word.getD lowerTop 0 = word.getD upperBottom 0 := by omega
        exact h101 lowerTop lowerBottom upperBottom hlower (by omega) hupperlen
          heq hlowerDescent
    · omega

end D5.S3.Combinatorics.InversionSeq.InversionSeq207RightStructure
