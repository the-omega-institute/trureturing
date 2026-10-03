/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoPrefix
   mirror-E: none(waiver:row-four-two-first-prefix)
   anchors: []
   utility: none
   digest: Forces the 21321 prefix of primitive two-first row-four words. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoPrefix

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwo

theorem primitive_two_positions (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 3 ≤ n) (hhead : w.head? = some 2)
    (hprimitive : primitive w n) :
    (w).idxOf 1 = 1 ∧ (w).idxOf 3 = 2 ∧
      secondPos 2 w = 3 ∧ secondPos 1 w = 4 := by
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
  have count_two_position_iff (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) (i : ℕ) :
      w[i]? = some a ↔ i = (w).idxOf a ∨ i = secondPos a w := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    rw [hfirst, hsecond]
    constructor
    · intro hi
      by_cases h0 : i < u.length
      · have hmem : a ∈ u := by
          have : u[i]? = some a := by simpa [List.getElem?_append, h0] using hi
          exact List.mem_of_getElem? this
        exact (hu hmem).elim
      by_cases h1 : i = u.length
      · exact Or.inl h1
      by_cases h2 : i < u.length + 1 + v.length
      · have hmem : a ∈ v := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hlt : i - u.length - 1 < v.length := by omega
          have hiv : v[i - u.length - 1]? = some a := by
            simpa [List.getElem?_append, hlt] using hi''
          exact List.mem_of_getElem? hiv
        exact (hv hmem).elim
      by_cases h3 : i = u.length + 1 + v.length
      · exact Or.inr h3
      · have hmem : a ∈ z := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hle : ¬ i - u.length - 1 < v.length := by omega
          have hi''' : (a :: z)[i - u.length - 1 - v.length]? = some a := by
            simpa [List.getElem?_append, hle] using hi''
          have heq' : i - u.length - 1 - v.length =
              (i - u.length - 1 - v.length - 1) + 1 := by omega
          rw [heq'] at hi'''
          have hiz : z[i - u.length - 1 - v.length - 1]? = some a := by
            simpa using hi'''
          exact List.mem_of_getElem? hiz
        exact (hz hmem).elim
    · rintro (rfl | rfl)
      · simp at *
      · have h := (count_two_positions a _ hw).2.2
        rw [hsecond] at h
        exact h
  have hlater := primitive_later_order w n 2 hw hprimitive (Or.inr rfl) hhead
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase := hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : x ∈ w :=
    List.mem_of_getElem? (count_two_positions x w (hcount x hx)).2.1
  have hsame := (nonnesting_iff_equal_orders w
    (fun x hx => hcount x (hbound x hx))).mp ⟨hw.2.1, hw.2.2.1⟩
  have hlen : w.length = 2 * n := by
    simpa [Nat.mul_comm] using hw.1.length_eq
  have hf2 : (w).idxOf 2 = 0 := by
    cases w with
    | nil => simp at hhead
    | cons x xs =>
      have hx : x = 2 := by simpa using hhead
      subst x
      simp []
  have hf1 : (w).idxOf 2 < (w).idxOf 1 := by
    have hneq : (w).idxOf 2 ≠ (w).idxOf 1 := by
      intro heq
      exact (by decide : (2 : ℕ) ≠ 1)
        ((List.idxOf_inj (hmem 2 ⟨by omega, by omega⟩)).mp heq)
    omega
  have hf3 : (w).idxOf 1 < (w).idxOf 3 :=
    (first_block_structure w n 2 hw ⟨by omega, by omega⟩ hf2).2
      1 3 (by omega) (by omega) (by omega) (by omega)
  have hs2s1 : secondPos 2 w < secondPos 1 w :=
    hsame 2 (hmem 2 ⟨by omega, by omega⟩)
      1 (hmem 1 ⟨by omega, by omega⟩) hf1
  have hs1s3 : secondPos 1 w < secondPos 3 w :=
    hsame 1 (hmem 1 ⟨by omega, by omega⟩)
      3 (hmem 3 ⟨by omega, by omega⟩) hf3
  have hf3s2 : (w).idxOf 3 < secondPos 2 w :=
    primitive_two_crossing w n hw hn hhead hlater hprimitive
  have hhigh (x : ℕ) (hx : 4 ≤ x ∧ x ≤ n) :
      secondPos 1 w < (w).idxOf x := by
    have hf3x := hlater 3 x (by omega) (by omega) hx.2
    have h1231 : ¬ NonnestingDefs.Occurs [1, 2, 3, 1] w :=
      hw.2.2.2 _ (by simp)
    have h1312 : ¬ NonnestingDefs.Occurs [1, 3, 1, 2] w :=
      hw.2.2.2 _ (by simp)
    exact (separated_three_orders w 1 3 x
      (hcount 1 ⟨by omega, by omega⟩)
      (hcount 3 ⟨by omega, by omega⟩)
      (hcount x ⟨by omega, hx.2⟩)
      (by omega) (by omega) hsame h1231 h1312).1 hf3 hf3x
  have hposition (p : ℕ) (hp : p ≤ 4) :
      ∃ x : ℕ, w[p]? = some x ∧
        (p = (w).idxOf x ∨ p = secondPos x w) ∧
        1 ≤ x ∧ x ≤ n := by
    have hplt : p < w.length := by omega
    let x := w[p]
    have hpx : w[p]? = some x := List.getElem?_eq_getElem hplt
    have hxb : 1 ≤ x ∧ x ≤ n := hbound x (List.mem_of_getElem? hpx)
    have hcase := (count_two_position_iff x w (hcount x hxb) p).mp hpx
    exact ⟨x, hpx, hcase, hxb⟩
  obtain ⟨x1, hx1, hcase1, hbound1⟩ := hposition 1 (by omega)
  have hx1val : x1 = 1 := by
    by_contra hneq
    by_cases h2 : x1 = 2
    · subst x1
      rcases hcase1 with h | h <;> omega
    by_cases h3 : x1 = 3
    · subst x1
      have hfs := (count_two_positions 3 w
        (hcount 3 ⟨by omega, by omega⟩)).1
      rcases hcase1 with h | h <;> omega
    have hx4 : 4 ≤ x1 := by omega
    have hfx := hlater 3 x1 (by omega) (by omega) hbound1.2
    have hfs := (count_two_positions x1 w (hcount x1 hbound1)).1
    rcases hcase1 with h | h <;> omega
  have hf1pos : (w).idxOf 1 = 1 := by
    subst x1
    have hfs := (count_two_positions 1 w
      (hcount 1 ⟨by omega, by omega⟩)).1
    rcases hcase1 with h | h
    · exact h.symm
    · omega
  obtain ⟨x2, hx2, hcase2, hbound2⟩ := hposition 2 (by omega)
  have hx2val : x2 = 3 := by
    by_contra hneq
    by_cases h1 : x2 = 1
    · subst x2
      rcases hcase2 with h | h <;> omega
    by_cases h2 : x2 = 2
    · subst x2
      rcases hcase2 with h | h <;> omega
    have hx4 : 4 ≤ x2 := by omega
    have hfx := hlater 3 x2 (by omega) (by omega) hbound2.2
    have hfs := (count_two_positions x2 w (hcount x2 hbound2)).1
    rcases hcase2 with h | h <;> omega
  have hf3pos : (w).idxOf 3 = 2 := by
    subst x2
    have hfs := (count_two_positions 3 w
      (hcount 3 ⟨by omega, by omega⟩)).1
    rcases hcase2 with h | h
    · exact h.symm
    · omega
  obtain ⟨x3, hx3, hcase3, hbound3⟩ := hposition 3 (by omega)
  have hx3val : x3 = 2 := by
    by_contra hneq
    by_cases h1 : x3 = 1
    · subst x3
      rcases hcase3 with h | h <;> omega
    by_cases h3 : x3 = 3
    · subst x3
      have hfs := (count_two_positions 3 w
        (hcount 3 ⟨by omega, by omega⟩)).1
      rcases hcase3 with h | h <;> omega
    have hx4 : 4 ≤ x3 := by omega
    have hfx := hhigh x3 ⟨hx4, hbound3.2⟩
    have hfs := (count_two_positions x3 w (hcount x3 hbound3)).1
    rcases hcase3 with h | h <;> omega
  have hs2pos : secondPos 2 w = 3 := by
    subst x3
    rcases hcase3 with h | h
    · omega
    · exact h.symm
  obtain ⟨x4, hx4, hcase4, hbound4⟩ := hposition 4 (by omega)
  have hx4val : x4 = 1 := by
    by_contra hneq
    by_cases h2 : x4 = 2
    · subst x4
      rcases hcase4 with h | h <;> omega
    by_cases h3 : x4 = 3
    · subst x4
      rcases hcase4 with h | h <;> omega
    have hxge : 4 ≤ x4 := by omega
    have hfx := hhigh x4 ⟨hxge, hbound4.2⟩
    have hfs := (count_two_positions x4 w (hcount x4 hbound4)).1
    rcases hcase4 with h | h <;> omega
  have hs1pos : secondPos 1 w = 4 := by
    subst x4
    rcases hcase4 with h | h
    · omega
    · exact h.symm
  exact ⟨hf1pos, hf3pos, hs2pos, hs1pos⟩

#print axioms primitive_two_positions

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoPrefix
