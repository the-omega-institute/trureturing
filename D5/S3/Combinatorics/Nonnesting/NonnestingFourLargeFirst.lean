/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourLargeFirst
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourLargeFirst
   mirror-E: none(waiver:row-four-large-first-letter)
   anchors: []
   utility: none
   digest: A first value of at least three must occur twice at the start. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree
open D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

theorem large_first_double (w : List ℕ) (n k : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hk : 3 ≤ k ∧ k ≤ n) (hhead : w.head? = some k) :
    ∃ t : List ℕ, w = k :: k :: t := by
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
  have hrange (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : x ∈ List.range' 1 n := by
    rw [List.mem_range'_1]
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 :=
    doubled_count n x w hw.1 (hrange x hx)
  have hcountAll : ∀ x ∈ w, w.count x = 2 := by
    intro x hx
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have hxi' : x = i := by simpa using hxi
    subst x
    exact doubled_count n i w hw.1 hi
  have hsame := (nonnesting_iff_equal_orders w hcountAll).mp ⟨hw.2.1, hw.2.2.1⟩
  have h1231 : ¬ NonnestingDefs.Occurs [1, 2, 3, 1] w := by
    exact hw.2.2.2 _ (by simp)
  have h1312 : ¬ NonnestingDefs.Occurs [1, 3, 1, 2] w := by
    exact hw.2.2.2 _ (by simp)
  have hk' : 1 ≤ k ∧ k ≤ n := ⟨by omega, hk.2⟩
  have h1 : 1 ≤ (1 : ℕ) ∧ 1 ≤ n := ⟨by omega, by omega⟩
  have h2 : 1 ≤ (2 : ℕ) ∧ 2 ≤ n := ⟨by omega, by omega⟩
  have hb := first_block_structure w n k hw hk'
  cases w with
  | nil => simp at hhead
  | cons y ws =>
    have hy : y = k := by simpa using hhead
    subst y
    cases ws with
    | nil =>
      have hlen := hw.1.length_eq
      simp at hlen
      omega
    | cons x t =>
      by_cases hxk : x = k
      · subst x
        exact ⟨t, rfl⟩
      have hfirstk : ((k :: x :: t)).idxOf k = 0 := by simp []
      have hblock := hb hfirstk
      have hf12 : ((k :: x :: t)).idxOf 1 < ((k :: x :: t)).idxOf 2 :=
        hblock.1 1 2 (by omega) (by omega) (by omega)
      have hfk1 : ((k :: x :: t)).idxOf k < ((k :: x :: t)).idxOf 1 := by
        have hnot : ((k :: x :: t)).idxOf 1 ≠ 0 := by
          intro heq
          have hval := (count_two_positions 1 (k :: x :: t) (hcount 1 h1)).2.1
          rw [heq] at hval
          simp at hval
          omega
        omega
      have hsk1 : secondPos k (k :: x :: t) < ((k :: x :: t)).idxOf 1 :=
        (separated_three_orders (k :: x :: t) 1 2 k
          (hcount 1 h1) (hcount 2 h2) (hcount k hk')
          (by omega) (by omega) hsame h1231 h1312).2.2 hfk1 hf12
      have hposk := (count_two_positions k (k :: x :: t) (hcount k hk')).1
      have hfx : ((k :: x :: t)).idxOf x = 1 := by
        simp [Ne.symm hxk]
      have hxb : 1 ≤ x ∧ x ≤ n := by
        have hxmem : x ∈ (k :: x :: t) := by simp
        have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
          hw.1.mem_iff.mp hxmem
        obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
        have hxi' : x = i := by simpa using hxi
        subst x
        rw [List.mem_range'_1] at hi
        omega
      have hf1le : ((k :: x :: t)).idxOf 1 ≤ 1 := by
        rcases lt_or_gt_of_ne hxk with hxk' | hxk'
        · by_cases hx1 : x = 1
          · subst x
            omega
          · have horder := hblock.1 1 x (by omega) (by omega) hxk'
            omega
        · have horder := hblock.2 1 x (by omega) (by omega) hxk' hxb.2
          omega
      omega

theorem large_first_cut (w : List ℕ) (n k : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hk : 3 ≤ k ∧ k < n) (hhead : w.head? = some k) : valueCut w k := by
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
  obtain ⟨t, heq⟩ := large_first_double w n k hw ⟨hk.1, by omega⟩ hhead
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have hxi' : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have h2231 : ¬ NonnestingDefs.Occurs [2, 2, 3, 1] w :=
    hw.2.2.2 _ (by simp)
  have hsep : ∀ x y : ℕ, x ∈ w → y ∈ w → x ≤ k → k < y →
      secondPos x w < (w).idxOf y := by
    intro x y hx hy hxk hky
    have hxb := hbound x hx
    have hyb := hbound y hy
    have px := count_two_positions x w (hcount x hxb)
    have py := count_two_positions y w (hcount y hyb)
    have hfy : (w).idxOf y < w.length :=
      (List.getElem?_eq_some_iff.mp py.2.1).1
    have hsx : secondPos x w < w.length :=
      (List.getElem?_eq_some_iff.mp px.2.2).1
    have hfy2 : 2 ≤ (w).idxOf y := by
      rw [heq]
      have hne : k ≠ y := by omega
      simp [List.idxOf_cons_ne _ hne]
    by_cases hxkeq : x = k
    · subst x
      have hsk : secondPos k w = 1 := by
        rw [heq]
        simp [secondPos]
      omega
    have hxsneq : secondPos x w ≠ (w).idxOf y := by
      intro he
      have hxy' : some x = some y := by
        calc
          some x = w[secondPos x w]? := px.2.2.symm
          _ = w[(w).idxOf y]? := congrArg (fun i => w[i]?) he
          _ = some y := py.2.1
      have hxy : x = y := by simpa using hxy'
      omega
    by_contra hnot
    have hfysx : (w).idxOf y < secondPos x w := by omega
    have hsub : List.Sublist [k, k, y, x] w := by
      let p : Fin 4 → ℕ := fun j =>
        if j.val = 0 then 0 else if j.val = 1 then 1 else
        if j.val = 2 then (w).idxOf y else secondPos x w
      have hp : ∀ j : Fin 4, p j < w.length := by
        intro j
        fin_cases j <;> simp [p] <;> omega
      let f : Fin 4 ↪o Fin w.length :=
        OrderEmbedding.ofMapLEIff (fun j => ⟨p j, hp j⟩) (by
          intro i j
          fin_cases i <;> fin_cases j <;> simp [p] <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨f, ?_⟩
      intro j
      fin_cases j <;> simp [f, p, heq]
      · simpa [heq] using (List.getElem?_eq_some_iff.mp px.2.2).2.symm
    let q : ℕ → ℕ := fun i => if i = 1 then x else if i = 2 then k else y
    have hocc : NonnestingDefs.Occurs [2, 2, 3, 1] w := by
      unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
      refine ⟨q, ?_, ?_, ?_, by simp⟩
      · intro i hi hlt
        have hi' : i = 1 ∨ i = 2 := by
          simp [NonnestingDefs.letters] at hlt
          omega
        rcases hi' with rfl | rfl
        · simpa [q] using (lt_of_le_of_ne hxk hxkeq)
        · simpa [q] using hky
      · intro i hi hle
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
          simp [NonnestingDefs.letters] at hle
          omega
        rcases hi' with rfl | rfl | rfl
        · simpa [q] using hx
        · have hkMem : k ∈ w := by rw [heq]; simp
          simpa [q] using hkMem
        · simpa [q] using hy
      · simpa [q] using hsub
    exact h2231 hocc
  apply valueCut_of_separated_indices n k w hw.1 (by omega)
  intro i j x y hix hjy hxk hky
  have hx : x ∈ w := List.mem_of_getElem? hix
  have hy : y ∈ w := List.mem_of_getElem? hjy
  have hxy := hsep x y hx hy hxk hky
  have hxi := (count_two_position_iff x w (hcount x (hbound x hx)) i).mp hix
  have hyj := (count_two_position_iff y w (hcount y (hbound y hy)) j).mp hjy
  have hpx := (count_two_positions x w (hcount x (hbound x hx))).1
  have hpy := (count_two_positions y w (hcount y (hbound y hy))).1
  rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl <;> omega

end D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst.large_first_double
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourLargeFirst.large_first_cut
