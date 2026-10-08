/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207RightChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207RightChildren
   mirror-E: none(waiver:right-active-child-construction)
   anchors: []
   utility: none
   digest: A maximum pair and terminal descent witnesses determine every right child value. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207RightStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207RightChildren

open D5.S3.Combinatorics.Nonnesting InversionSeqOccurs
open InversionSeq207Append InversionSeq207RightStructure

theorem right_children_exact (word : List ℕ) (value maximumIndex : ℕ)
    (hword : word ∈ InversionSeqDefs.avoiders word.length
      [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]])
    (hvalue : word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
      [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]])
    (hmaximumIndex : maximumIndex < word.length)
    (hmaximum : ∀ index < word.length,
      word.getD index 0 ≤ word.getD maximumIndex 0) :
    secondLargest (word ++ [value]) = min (word.getD maximumIndex 0) value ∧
    (∀ candidate : ℕ,
      (word ++ [value]) ++ [candidate] ∈ InversionSeqDefs.avoiders (word.length + 2)
        [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] ↔
      min (word.getD maximumIndex 0) value ≤ candidate ∧
      candidate ≤ word.length + 1 ∧
      (∀ top bottom : ℕ, top < bottom → bottom < word.length →
        word.getD bottom 0 < word.getD top 0 → word.getD top 0 ≠ candidate) ∧
      (value < word.getD maximumIndex 0 → candidate ≠ word.getD maximumIndex 0)) := by
  have hget (index : ℕ) (hindex : index < word.length) :
      (word ++ [value]).getD index 0 = word.getD index 0 :=
    List.getD_append word [value] 0 index hindex
  have hlast : (word ++ [value]).getD word.length 0 = value := by
    rw [List.getD_append_right word [value] 0 word.length le_rfl]
    simp
  have hactive := (right_append_iff word value hword).mp hvalue
  have hclassification := right_descent_classification word hword
    maximumIndex hmaximumIndex hmaximum
  have hpair (entries : List ℕ) (first second : ℕ)
      (hfirst : first < second) (hsecond : second < entries.length) :
      min (entries.getD first 0) (entries.getD second 0) ≤ secondLargest entries := by
    unfold secondLargest
    exact le_trans
      (Finset.le_sup (f := fun index => min (entries.getD index 0)
        (entries.getD second 0)) (Finset.mem_range.mpr hfirst))
      (Finset.le_sup (f := fun later => (Finset.range later).sup fun earlier =>
        min (entries.getD earlier 0) (entries.getD later 0))
        (Finset.mem_range.mpr hsecond))
  have hsecondMax : secondLargest word ≤ word.getD maximumIndex 0 := by
    simp only [secondLargest, Finset.sup_le_iff, Finset.mem_range]
    intro second hsecond first hfirst
    exact le_trans (min_le_right _ _) (hmaximum second hsecond)
  have hnewSecond : secondLargest (word ++ [value]) =
      min (word.getD maximumIndex 0) value := by
    apply le_antisymm
    · simp only [secondLargest, Finset.sup_le_iff, Finset.mem_range]
      intro second hsecond first hfirst
      have hsecondlen : second < word.length + 1 := by simpa using hsecond
      by_cases hprefix : second < word.length
      · rw [hget first (by omega), hget second hprefix]
        exact le_trans (hpair word first second hfirst hprefix)
          (le_min hsecondMax hactive.1)
      · have heq : second = word.length := by omega
        subst second
        rw [hget first hfirst, hlast]
        exact min_le_min_right value (hmaximum first hfirst)
    · have hattained := hpair (word ++ [value]) maximumIndex word.length
        hmaximumIndex (by simp)
      simpa only [hget maximumIndex hmaximumIndex, hlast] using hattained
  refine ⟨hnewSecond, ?_⟩
  intro candidate
  have hnext := right_append_iff (word ++ [value]) candidate (by simpa using hvalue)
  have hlength : (word ++ [value]).length + 1 = word.length + 2 := by simp
  rw [hlength, hnewSecond] at hnext
  constructor
  · intro hchild
    obtain ⟨hsecond, hbound, hdescent⟩ := hnext.mp hchild
    refine ⟨hsecond, by simpa using hbound, ?_, ?_⟩
    · intro top bottom htop hbottom hdrop heq
      apply hdescent top bottom htop (by simp; omega)
        (by rwa [hget top (by omega), hget bottom hbottom])
      simpa only [hget top (by omega)] using heq
    · intro hlow heq
      apply hchild.2.2 [2, 1, 2] (by simp)
      apply (occurs_three_iff 2 1 2 ((word ++ [value]) ++ [candidate])
        (by omega) (by omega) (by omega) (by omega)).mpr
      refine ⟨maximumIndex, word.length, word.length + 1,
        hmaximumIndex, by omega, by simp, ?_⟩
      have htop : ((word ++ [value]) ++ [candidate]).getD maximumIndex 0 =
          word.getD maximumIndex 0 := by
        rw [List.getD_append _ _ _ _ (by simp; omega), hget maximumIndex hmaximumIndex]
      have hbottom : ((word ++ [value]) ++ [candidate]).getD word.length 0 = value := by
        rw [List.getD_append _ _ _ _ (by simp), hlast]
      have hend : ((word ++ [value]) ++ [candidate]).getD (word.length + 1) 0 =
          candidate := by
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      rw [htop, hbottom, hend]
      omega
  · rintro ⟨hsecond, hbound, holdDescent, hnewDescent⟩
    apply hnext.mpr
    refine ⟨hsecond, by simpa using hbound, ?_⟩
    intro top bottom htop hbottom hdrop heq
    have hbottomlen : bottom < word.length + 1 := by simpa using hbottom
    by_cases hprefix : bottom < word.length
    · rw [hget top (by omega), hget bottom hprefix] at hdrop
      rw [hget top (by omega)] at heq
      exact holdDescent top bottom htop hprefix hdrop heq
    · have heqIndex : bottom = word.length := by omega
      subst bottom
      rw [hget top htop, hlast] at hdrop
      rw [hget top htop] at heq
      have htopMax := hmaximum top htop
      have hlow : value < word.getD maximumIndex 0 := by omega
      rcases hclassification.1 top htop with hsmall | hmax
      · omega
      · exact hnewDescent hlow (heq.symm.trans hmax)

end D5.S3.Combinatorics.InversionSeq.InversionSeq207RightChildren
