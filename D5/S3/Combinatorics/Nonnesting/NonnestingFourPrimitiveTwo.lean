/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwo
   mirror-E: none(waiver:row-four-two-first-block)
   anchors: []
   utility: none
   digest: Characterizes the first value cut of a word beginning with two. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwo

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks

theorem primitive_two_crossing (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 3 ≤ n) (hhead : w.head? = some 2)
    (hlater : ∀ a b, 2 ≤ a → a < b → b ≤ n →
      (w).idxOf a < (w).idxOf b)
    (hprimitive : primitive w n) :
    (w).idxOf 3 < secondPos 2 w := by
  have two_first_cut_iff (w : List ℕ) (n : ℕ)
      (hw : w ∈ NonnestingDefs.avoiders n
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hn : 3 ≤ n) (hhead : w.head? = some 2)
      (hlater : ∀ a b, 2 ≤ a → a < b → b ≤ n →
        (w).idxOf a < (w).idxOf b) :
      valueCut w 2 ↔ secondPos 1 w < (w).idxOf 3 := by
    have valueCut_separates_positions (w : List ℕ) (k x y : ℕ)
        (hcut : valueCut w k) (hcount : w.count x = 2)
        (hx : x ≤ k) (hy : k < y) :
        secondPos x w < (w).idxOf y := by
      obtain ⟨u, v, heq, _, hu, hv⟩ := hcut
      have hxNot : x ∉ v := by
        intro h
        have := hv x h
        omega
      have hyNot : y ∉ u := by
        intro h
        have := (hu y h).2
        omega
      have hcountU : u.count x = 2 := by
        rw [heq, List.count_append] at hcount
        have hvzero : v.count x = 0 := List.count_eq_zero_of_not_mem hxNot
        omega
      obtain ⟨a, b, c, ha, hb, _, hueq⟩ :=
        count_two_decomposition x u hcountU
      have hs : secondPos x w = a.length + 1 + b.length := by
        rw [heq, hueq]
        have hdrop : a.drop (a.length + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr
          omega
        simp [secondPos, List.idxOf_append, ha, hb,
          List.drop_append, hdrop, List.append_assoc]
      have hf : (w).idxOf y = u.length + v.idxOf y := by
        rw [heq]
        exact List.idxOf_append_of_notMem hyNot
      rw [hs, hf, hueq]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
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
    have hsame := (nonnesting_iff_equal_orders w
      (fun x hx => hcount x (hbound x hx))).mp ⟨hw.2.1, hw.2.2.1⟩
    have hfirst2 : (w).idxOf 2 = 0 := by
      cases w with
      | nil => simp at hhead
      | cons x xs =>
        have hx : x = 2 := by simpa using hhead
        subst x
        simp []
    have hfirst1 : (w).idxOf 2 < (w).idxOf 1 := by
      have hneq : (w).idxOf 1 ≠ (w).idxOf 2 := by
        intro heq
        have hmem : 1 ∈ w :=
          List.mem_of_getElem? (count_two_positions 1 w
            (hcount 1 ⟨by omega, by omega⟩)).2.1
        exact (by decide : (1 : ℕ) ≠ 2)
          ((List.idxOf_inj hmem).mp heq)
      omega
    have hsecond2 : secondPos 2 w < secondPos 1 w :=
      hsame 2 (List.mem_of_getElem? (count_two_positions 2 w
        (hcount 2 ⟨by omega, by omega⟩)).2.1)
        1 (List.mem_of_getElem? (count_two_positions 1 w
          (hcount 1 ⟨by omega, by omega⟩)).2.1) hfirst1
    constructor
    · intro hcut
      exact valueCut_separates_positions w 2 1 3 hcut
        (hcount 1 ⟨by omega, by omega⟩) (by omega) (by omega)
    · intro hsep
      apply valueCut_of_separated_indices n 2 w hw.1 (by omega)
      intro i j a b hia hjb ha hb
      have hama : a = 1 ∨ a = 2 := by
        have hamem : a ∈ w := List.mem_of_getElem? hia
        have := hbound a hamem
        omega
      have hbge : 3 ≤ b := by omega
      have hble : b ≤ n := (hbound b (List.mem_of_getElem? hjb)).2
      have hsb : secondPos a w < (w).idxOf b := by
        have hsa : secondPos a w ≤ secondPos 1 w := by
          rcases hama with rfl | rfl
          · exact le_refl _
          · exact le_of_lt hsecond2
        have hfb : (w).idxOf 3 ≤ (w).idxOf b := by
          rcases eq_or_lt_of_le hbge with rfl | hlt
          · exact le_refl _
          · exact le_of_lt (hlater 3 b (by omega) hlt hble)
        omega
      have hai := (count_two_position_iff a w
        (hcount a (hbound a (List.mem_of_getElem? hia))) i).mp hia
      have hbj := (count_two_position_iff b w
        (hcount b (hbound b (List.mem_of_getElem? hjb))) j).mp hjb
      have hpa := (count_two_positions a w
        (hcount a (hbound a (List.mem_of_getElem? hia)))).1
      have hpb := (count_two_positions b w
        (hcount b (hbound b (List.mem_of_getElem? hjb)))).1
      rcases hai with rfl | rfl <;> rcases hbj with rfl | rfl <;> omega
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
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have p1 := count_two_positions 1 w (hcount 1 ⟨by omega, by omega⟩)
  have p2 := count_two_positions 2 w (hcount 2 ⟨by omega, by omega⟩)
  have p3 := count_two_positions 3 w (hcount 3 ⟨by omega, by omega⟩)
  have hnotCut : ¬ valueCut w 2 := hprimitive 2 (by omega) (by omega)
  have hnotSep : ¬ secondPos 1 w < (w).idxOf 3 := by
    intro hsep
    exact hnotCut ((two_first_cut_iff w n hw hn hhead hlater).mpr hsep)
  have hne13 : secondPos 1 w ≠ (w).idxOf 3 := by
    intro heq
    have hvalues : (1 : ℕ) = 3 := by
      have h := p1.2.2.symm.trans
        ((congrArg (fun i => w[i]?) heq).trans p3.2.1)
      exact Option.some.inj h
    omega
  have hf3s1 : (w).idxOf 3 < secondPos 1 w := by omega
  have hf2 : (w).idxOf 2 = 0 := by
    cases w with
    | nil => simp at hhead
    | cons x xs =>
      have hx : x = 2 := by simpa using hhead
      subst x
      simp []
  have hne23 : secondPos 2 w ≠ (w).idxOf 3 := by
    intro heq
    have hvalues : (2 : ℕ) = 3 := by
      have h := p2.2.2.symm.trans
        ((congrArg (fun i => w[i]?) heq).trans p3.2.1)
      exact Option.some.inj h
    omega
  by_contra hnot
  have hs2f3 : secondPos 2 w < (w).idxOf 3 := by omega
  have hsub : List.Sublist [2, 2, 3, 1] w := by
    let p : Fin 4 → ℕ := fun j =>
      if j.val = 0 then (w).idxOf 2 else if j.val = 1 then secondPos 2 w else
      if j.val = 2 then (w).idxOf 3 else secondPos 1 w
    have hp : ∀ j : Fin 4, p j < w.length := by
      intro j
      fin_cases j <;> simp [p] <;>
        first | exact (List.getElem?_eq_some_iff.mp p2.2.1).1
              | exact (List.getElem?_eq_some_iff.mp p2.2.2).1
              | exact (List.getElem?_eq_some_iff.mp p3.2.1).1
              | exact (List.getElem?_eq_some_iff.mp p1.2.2).1
    let f : Fin 4 ↪o Fin w.length :=
      OrderEmbedding.ofMapLEIff (fun j => ⟨p j, hp j⟩) (by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [p] <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f, ?_⟩
    intro j
    fin_cases j <;> simp [f, p]
    · simpa using (List.getElem?_eq_some_iff.mp p2.2.2).2.symm
    · simpa using (List.getElem?_eq_some_iff.mp p1.2.2).2.symm
  have hocc : NonnestingDefs.Occurs [2, 2, 3, 1] w := by
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨id, ?_, ?_, by simpa using hsub, by simp⟩
    · intro i hi hlt
      simp [NonnestingDefs.letters] at hlt
      simp
    · intro i hi hle
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
        simp [NonnestingDefs.letters] at hle
        omega
      rcases hi' with rfl | rfl | rfl
      · exact List.mem_of_getElem? p1.2.1
      · exact List.mem_of_getElem? p2.2.1
      · exact List.mem_of_getElem? p3.2.1
  exact hw.2.2.2 _ (by simp) hocc

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwo

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwo.primitive_two_crossing
