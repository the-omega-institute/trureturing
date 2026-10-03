/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing
   mirror-E: none(waiver:row-four-binary-adjacency)
   anchors: []
   utility: none
   digest: Adjacent first and second occurrences encode increasing-order avoiders. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

theorem increasing_adjacent (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
      (w).idxOf a < (w).idxOf b) (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
    secondPos i w + 1 = (w).idxOf (i + 1) ∨
      (w).idxOf (i + 1) + 1 = secondPos i w := by
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
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun j => [j, j]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hxbase
    have hxj' : x = j := by simpa using hxj
    subst x
    rw [List.mem_range'_1] at hj
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : x ∈ w :=
    List.mem_of_getElem? (count_two_positions x w (hcount x hx)).2.1
  have hcountAll : ∀ x ∈ w, w.count x = 2 := by
    intro x hx
    exact hcount x (hbound x hx)
  have hsame := (nonnesting_iff_equal_orders w hcountAll).mp ⟨hw.2.1, hw.2.2.1⟩
  have h1231 : ¬ NonnestingDefs.Occurs [1, 2, 3, 1] w :=
    hw.2.2.2 _ (by simp)
  have h1312 : ¬ NonnestingDefs.Occurs [1, 3, 1, 2] w :=
    hw.2.2.2 _ (by simp)
  have hfmono (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n) :
      (w).idxOf a ≤ (w).idxOf b := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (hfirst a b ha hlt hb)
  have hsmono (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n) :
      secondPos a w ≤ secondPos b w := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · have hfab := hfirst a b ha hlt hb
      exact le_of_lt (hsame a (hmem a ⟨ha, by omega⟩)
        b (hmem b ⟨by omega, hb⟩) hfab)
  have hskip (j : ℕ) (hj : 1 ≤ j ∧ j + 2 ≤ n) :
      secondPos j w < (w).idxOf (j + 2) := by
    have hthree := separated_three_orders w j (j + 1) (j + 2)
      (hcount j ⟨hj.1, by omega⟩)
      (hcount (j + 1) ⟨by omega, by omega⟩)
      (hcount (j + 2) ⟨by omega, hj.2⟩)
      (by omega) (by omega) hsame h1231 h1312
    exact hthree.1 (hfirst j (j + 1) hj.1 (by omega) (by omega))
      (hfirst (j + 1) (j + 2) (by omega) (by omega) hj.2)
  have hiBound : 1 ≤ i ∧ i ≤ n := ⟨hi.1, by omega⟩
  have hi1Bound : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
  have pi := count_two_positions i w (hcount i hiBound)
  have pi1 := count_two_positions (i + 1) w (hcount (i + 1) hi1Bound)
  have hne : secondPos i w ≠ (w).idxOf (i + 1) := by
    intro heq
    have hval : some i = some (i + 1) := by
      calc
        some i = w[secondPos i w]? := pi.2.2.symm
        _ = w[(w).idxOf (i + 1)]? := congrArg (fun j => w[j]?) heq
        _ = some (i + 1) := pi1.2.1
    simp at hval
  have hgap (p lo hi : ℕ) (hlo : lo < p) (hhi : p < hi)
      (hboundp : hi < w.length) :
      ∃ x : ℕ, w[p]? = some x ∧ 1 ≤ x ∧ x ≤ n := by
    have hp : p < w.length := by omega
    refine ⟨w[p], ?_, ?_⟩
    · exact List.getElem?_eq_getElem hp
    · exact hbound w[p] (List.getElem_mem hp)
  rcases lt_or_gt_of_ne hne with his | hsi
  · by_contra hnot
    have hwide : secondPos i w + 1 < (w).idxOf (i + 1) := by omega
    obtain ⟨x, hpx, hxbound⟩ := hgap (secondPos i w + 1)
      (secondPos i w) ((w).idxOf (i + 1)) (by omega)
      hwide (List.getElem?_eq_some_iff.mp pi1.2.1).1
    have hpos := (count_two_position_iff x w (hcount x hxbound)
      (secondPos i w + 1)).mp hpx
    rcases hpos with hfirstx | hsecondx
    · by_cases hxi : x ≤ i
      · have hle := hfmono x i hxbound.1 hxi hiBound.2
        omega
      · have hle := hfmono (i + 1) x (by omega) (by omega) hxbound.2
        omega
    · by_cases hxi : x ≤ i
      · have hle := hsmono x i hxbound.1 hxi hiBound.2
        omega
      · have hle := hsmono (i + 1) x (by omega) (by omega) hxbound.2
        omega
  · by_contra hnot
    have hwide : (w).idxOf (i + 1) + 1 < secondPos i w := by omega
    obtain ⟨x, hpx, hxbound⟩ := hgap ((w).idxOf (i + 1) + 1)
      ((w).idxOf (i + 1)) (secondPos i w) (by omega)
      hwide (List.getElem?_eq_some_iff.mp pi.2.2).1
    have hpos := (count_two_position_iff x w (hcount x hxbound)
      ((w).idxOf (i + 1) + 1)).mp hpx
    rcases hpos with hfirstx | hsecondx
    · by_cases hxi : x ≤ i + 1
      · have hle := hfmono x (i + 1) hxbound.1 hxi hi1Bound.2
        omega
      · have hsk := hskip i ⟨hi.1, by omega⟩
        have hle := hfmono (i + 2) x (by omega) (by omega) hxbound.2
        omega
    · by_cases hxi : x < i
      · have hsk := hskip (i - 1) ⟨by omega, by omega⟩
        have hle := hsmono x (i - 1) hxbound.1 (by omega) (by omega)
        have heq : i - 1 + 2 = i + 1 := by omega
        rw [heq] at hsk
        omega
      · have hle := hsmono i x hi.1 (by omega) hxbound.2
        omega

theorem increasing_prefix (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 2 ≤ n)
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
      (w).idxOf a < (w).idxOf b) :
    (∃ t, w = 1 :: 1 :: 2 :: t) ∨ (∃ t, w = 1 :: 2 :: 1 :: t) := by
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
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun j => [j, j]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hxbase
    have hxj' : x = j := by simpa using hxj
    subst x
    rw [List.mem_range'_1] at hj
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hp1 := count_two_positions 1 w (hcount 1 ⟨by omega, by omega⟩)
  have hp2 := count_two_positions 2 w (hcount 2 ⟨by omega, hn⟩)
  have hpair := increasing_adjacent w n hw hfirst 1 ⟨by omega, by omega⟩
  cases w with
  | nil =>
    have hlen := hw.1.length_eq
    simp at hlen
    omega
  | cons z zs =>
    have hz : z = 1 := by
      have hzb := hbound z (by simp)
      by_contra hnot
      have hfz : ((z :: zs)).idxOf z = 0 := by simp []
      have hlt := hfirst 1 z (by omega) (by omega) hzb.2
      omega
    subst z
    cases zs with
    | nil =>
      have hlen := hw.1.length_eq
      simp at hlen
      omega
    | cons z t =>
      have hzb := hbound z (by simp)
      have hz12 : z = 1 ∨ z = 2 := by
        by_contra hnot
        have hzgt : 2 < z := by omega
        have hfz : ((1 :: z :: t)).idxOf z = 1 := by
          simp [show 1 ≠ z by omega]
        have hf2 : ((1 :: z :: t)).idxOf 2 ≠ 0 := by
          intro he
          have hv := hp2.2.1
          rw [he] at hv
          simp at hv
        have hlt := hfirst 2 z (by omega) hzgt hzb.2
        omega
      rcases hz12 with hz1 | hz2
      · subst z
        have hs1 : secondPos 1 (1 :: 1 :: t) = 1 := by
          simp [secondPos]
        have hf2 : ((1 :: 1 :: t)).idxOf 2 = 2 := by
          have hf2ge : 2 ≤ ((1 :: 1 :: t)).idxOf 2 := by
            simp []
          rw [hs1] at hpair
          change 2 = ((1 :: 1 :: t)).idxOf 2 ∨
            ((1 :: 1 :: t)).idxOf 2 + 1 = 1 at hpair
          omega
        have hv : (1 :: 1 :: t)[2]? = some 2 := by
          simpa [hf2] using hp2.2.1
        cases t with
        | nil => simp at hv
        | cons a s =>
          have ha : a = 2 := by simpa using hv
          subst a
          exact Or.inl ⟨s, rfl⟩
      · subst z
        have hf2 : ((1 :: 2 :: t)).idxOf 2 = 1 := by simp []
        have hs1 : secondPos 1 (1 :: 2 :: t) = 2 := by
          have hf1 : ((1 :: 2 :: t)).idxOf 1 = 0 := by simp []
          have hs1pos := hp1.1
          rw [hf1] at hs1pos
          rw [hf2] at hpair
          norm_num at hpair
          rcases hpair with hpair | hpair <;> omega
        have hv : (1 :: 2 :: t)[2]? = some 1 := by
          simpa [hs1] using hp1.2.2
        cases t with
        | nil => simp at hv
        | cons a s =>
          have ha : a = 1 := by simpa using hv
          subst a
          exact Or.inr ⟨s, rfl⟩

theorem increasing_cut_iff (w : List ℕ) (n i : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
      (w).idxOf a < (w).idxOf b) (hi : 1 ≤ i ∧ i < n) :
    valueCut w i ↔ secondPos i w < (w).idxOf (i + 1) := by
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
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun j => [j, j]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hxbase
    have heq : x = j := by simpa using hxj
    subst x
    rw [List.mem_range'_1] at hj
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hcountAll : ∀ x ∈ w, w.count x = 2 := by
    intro x hx
    exact hcount x (hbound x hx)
  have hsame := (nonnesting_iff_equal_orders w hcountAll).mp ⟨hw.2.1, hw.2.2.1⟩
  constructor
  · intro hcut
    exact valueCut_separates_positions w i i (i + 1) hcut
      (hcount i ⟨hi.1, by omega⟩) (by omega) (by omega)
  · intro hsep
    apply valueCut_of_separated_indices n i w hw.1 (by omega)
    intro p q x y hpx hqy hxi hiy
    have hx : x ∈ w := List.mem_of_getElem? hpx
    have hy : y ∈ w := List.mem_of_getElem? hqy
    have hxb := hbound x hx
    have hyb := hbound y hy
    have hxfi : (w).idxOf x ≤ (w).idxOf i := by
      rcases eq_or_lt_of_le hxi with heq | hlt
      · subst x; exact le_refl _
      · exact le_of_lt (hfirst x i hxb.1 hlt (by omega))
    have hxsi : secondPos x w ≤ secondPos i w := by
      rcases eq_or_lt_of_le hxi with heq | hlt
      · subst x; exact le_refl _
      · exact le_of_lt (hsame x hx i
          (List.mem_of_getElem? (count_two_positions i w
            (hcount i ⟨hi.1, by omega⟩)).2.1)
          (hfirst x i hxb.1 hlt (by omega)))
    have hiyf : (w).idxOf (i + 1) ≤ (w).idxOf y := by
      rcases eq_or_lt_of_le (show i + 1 ≤ y by omega) with heq | hlt
      · subst y; exact le_refl _
      · exact le_of_lt (hfirst (i + 1) y (by omega) hlt hyb.2)
    have hpositions : secondPos x w < (w).idxOf y := by omega
    have hxp := (count_two_position_iff x w (hcount x hxb) p).mp hpx
    have hyq := (count_two_position_iff y w (hcount y hyb) q).mp hqy
    have hpx' := (count_two_positions x w (hcount x hxb)).1
    have hqy' := (count_two_positions y w (hcount y hyb)).1
    rcases hxp with rfl | rfl <;> rcases hyq with rfl | rfl <;> omega

end D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing.increasing_adjacent
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing.increasing_prefix
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing.increasing_cut_iff
