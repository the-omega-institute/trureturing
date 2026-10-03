/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveClassify
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveClassify
   mirror-E: none(waiver:row-four-primitive-classification)
   anchors: []
   utility: none
   digest: Classifies primitive row-four words by their initial value. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoConstruct
import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveClassify

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge
open D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoTail

theorem primitive_classification (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 3 ≤ n) (hprim : primitive w n) :
    (∃ v : increasingWords (n - 1), w = n :: n :: v.1) ∨
    (∃ v : increasingWords n, primitive v.1 n ∧ w = v.1) ∨
    (∃ v : increasingWords (n - 2), primitive v.1 (n - 2) ∧
      w = [2, 1, 3, 2, 1] ++ (shift 2 v.1).tail) := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have hlen : w.length = 2 * n := by
    simpa [Nat.mul_comm] using hw.1.length_eq
  cases hwhead : w with
  | nil => simp [hwhead] at hlen; omega
  | cons k r =>
    have hk : 1 ≤ k ∧ k ≤ n := by
      have hxbase := hw.1.mem_iff.mp (by rw [hwhead]; simp : k ∈ w)
      obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
      have heq : k = i := by simpa using hxi
      subst k
      rw [List.mem_range'_1] at hi
      omega
    have hhead : w.head? = some k := by simp [hwhead]
    rcases eq_or_lt_of_le hk.1 with hk1 | hk1
    · subst k
      right
      left
      have hfirst1 : (w).idxOf 1 = 0 := by simp [hwhead]
      have horder : ∀ a b, 1 ≤ a → a < b → b ≤ n →
          (w).idxOf a < (w).idxOf b := by
        intro a b ha hab hb
        by_cases ha1 : a = 1
        · subst a
          rw [hfirst1]
          have hcountb : w.count b = 2 := by
            apply doubled_count n b w hw.1
            rw [List.mem_range'_1]
            omega
          have hposb := (count_two_positions b w hcountb).2.1
          have hne : (w).idxOf b ≠ 0 := by
            intro heq
            rw [heq, hwhead] at hposb
            simp at hposb
            omega
          omega
        · exact (primitive_later_order w n 1 hw hprim (Or.inl rfl) hhead)
            a b (by omega) hab hb
      exact ⟨⟨w, hw, horder⟩, hprim, by simp [hwhead]⟩
    by_cases hk2 : k = 2
    · subst k
      right
      right
      let z := (w.filter (fun x => decide (2 < x))).map (fun x => x - 2)
      obtain ⟨hz, horder, hzprim, hword⟩ :=
        primitive_two_tail w n hw hn hhead hprim
      refine ⟨⟨z, hz, horder⟩, hzprim, ?_⟩
      exact hwhead.symm.trans hword
    · left
      have hkge : 3 ≤ k := by omega
      have hkn : k = n := by
        by_contra hne
        have hklt : k < n := by omega
        exact hprim k hk.1 hklt (large_first_cut w n k hw ⟨hkge, hklt⟩ hhead)
      subst k
      obtain ⟨v, hvword⟩ := large_first_double w n n hw
        ⟨by omega, le_refl _⟩ hhead
      have hv := large_first_tail n v hn (hvword ▸ hw)
      exact ⟨⟨v, hv.1, hv.2⟩, hwhead.symm.trans hvword⟩

#print axioms primitive_classification

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveClassify
