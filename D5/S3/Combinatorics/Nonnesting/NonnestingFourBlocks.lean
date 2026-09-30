/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourBlocks
   mirror-E: none(waiver:row-four-first-block)
   anchors: []
   utility: none
   digest: The first letter controls the first-occurrence order of all other values. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree

theorem first_block_structure (w : List ℕ) (n k : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hk : 1 ≤ k ∧ k ≤ n) (hfirst : (w).idxOf k = 0) :
    (∀ a b, 1 ≤ a → a < b → b < k → (w).idxOf a < (w).idxOf b) ∧
      (∀ a c, 1 ≤ a → a < k → k < c → c ≤ n →
        (w).idxOf a < (w).idxOf c) := by
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
  have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : x ∈ w := by
    exact List.mem_of_getElem? (count_two_positions x w (hcount x hx)).2.1
  have hcountAll : ∀ x ∈ w, w.count x = 2 := by
    intro x hx
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have hxi' : x = i := by simpa using hxi
    subst x
    exact doubled_count n i w hw.1 hi
  have hsame := (nonnesting_iff_equal_orders w hcountAll).mp ⟨hw.2.1, hw.2.2.1⟩
  have hne (x y : ℕ) (hx : 1 ≤ x ∧ x ≤ n) (hy : 1 ≤ y ∧ y ≤ n)
      (hxy : x ≠ y) : (w).idxOf x ≠ (w).idxOf y := by
    intro hpos
    have px := (count_two_positions x w (hcount x hx)).2.1
    have py := (count_two_positions y w (hcount y hy)).2.1
    have hvalues : some x = some y := by
      calc
        some x = w[(w).idxOf x]? := px.symm
        _ = w[(w).idxOf y]? := congrArg (fun i => w[i]?) hpos
        _ = some y := py
    exact hxy (by simpa using hvalues)
  have h2231 : ¬ NonnestingDefs.Occurs [2, 2, 3, 1] w := by
    exact hw.2.2.2 _ (by simp)
  have h3221 : ¬ NonnestingDefs.Occurs [3, 2, 2, 1] w := by
    exact hw.2.2.2 _ (by simp)
  constructor
  · intro a b ha hab hbk
    have hak : 1 ≤ a ∧ a ≤ n := ⟨ha, by omega⟩
    have hbk' : 1 ≤ b ∧ b ≤ n := ⟨by omega, by omega⟩
    have hkk : 1 ≤ k ∧ k ≤ n := hk
    have hfkb : (w).idxOf k < (w).idxOf b := by
      have hneq := hne k b hkk hbk' (by omega)
      omega
    have hfab : (w).idxOf a ≠ (w).idxOf b :=
      hne a b hak hbk' (by omega)
    by_contra hnot
    have hfba : (w).idxOf b < (w).idxOf a := by omega
    have hbad := (forbidden_last_first w a b k
      (hcount a hak) (hcount b hbk') (hcount k hkk)
      hab hbk (fun p hp q hq hlt => hsame p hp q hq hlt) h2231 h3221).2
    exact hbad ⟨hfkb, hfba⟩
  · intro a c ha hak hkc hcn
    have ha' : 1 ≤ a ∧ a ≤ n := ⟨ha, by omega⟩
    have hc' : 1 ≤ c ∧ c ≤ n := ⟨by omega, hcn⟩
    have hfkc : (w).idxOf k < (w).idxOf c := by
      have hneq := hne k c hk hc' (by omega)
      omega
    have hfac : (w).idxOf a ≠ (w).idxOf c :=
      hne a c ha' hc' (by omega)
    by_contra hnot
    have hfca : (w).idxOf c < (w).idxOf a := by omega
    have hbad := (forbidden_last_first w a k c
      (hcount a ha') (hcount k hk) (hcount c hc')
      hak hkc (fun p hp q hq hlt => hsame p hp q hq hlt) h2231 h3221).1
    exact hbad ⟨hfkc, hfca⟩

end D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks.first_block_structure
