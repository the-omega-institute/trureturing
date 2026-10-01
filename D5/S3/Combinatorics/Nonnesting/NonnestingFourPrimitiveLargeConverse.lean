/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLargeConverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLargeConverse
   mirror-E: none(waiver:row-four-maximum-prefix-construction)
   anchors: []
   utility: none
   digest: Constructs row-four avoiders by prefixing an increasing tail with nn. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLargeConverse

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitivePrefix

theorem large_prefix_construct (n : ℕ) (hn : 2 ≤ n) (v : increasingWords (n - 1)) :
    (n :: n :: v.1) ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
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
  have no_bba_sublist_of_same_orders (w : List ℕ) (a b : ℕ)
      (ha : w.count a = 2) (hb : w.count b = 2)
      (hfirst : (w).idxOf a < (w).idxOf b)
      (hsecond : secondPos a w < secondPos b w) :
      ¬ List.Sublist [b, b, a] w := by
    intro hsub
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    have h0 : w[(f 0).val]? = some b := by
      rw [List.getElem?_eq_getElem (f 0).isLt]
      simpa using (hf (0 : Fin 3)).symm
    have h1 : w[(f 1).val]? = some b := by
      rw [List.getElem?_eq_getElem (f 1).isLt]
      simpa using (hf (1 : Fin 3)).symm
    have h2 : w[(f 2).val]? = some a := by
      rw [List.getElem?_eq_getElem (f 2).isLt]
      simpa using (hf (2 : Fin 3)).symm
    have h01 : (f 0).val < (f 1).val :=
      f.strictMono (show (0 : Fin 3) < 1 by decide)
    have h12 : (f 1).val < (f 2).val :=
      f.strictMono (show (1 : Fin 3) < 2 by decide)
    have hb0 := (count_two_position_iff b w hb _).mp h0
    have hb1 := (count_two_position_iff b w hb _).mp h1
    have ha2 := (count_two_position_iff a w ha _).mp h2
    have hbb := (count_two_positions b w hb).1
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases ha2 with ha2 | ha2 <;> omega
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hbase : ((List.range' 1 n).flatMap fun i => [i, i]) =
      ((List.range' 1 (n - 1)).flatMap fun i => [i, i]) ++ [n, n] := by
    have hnn : n - 1 + 1 = n := by omega
    have hrange : List.range' 1 n = List.range' 1 (n - 1) ++ [n] := by
      calc
        List.range' 1 n = List.range' 1 (n - 1 + 1) := by rw [hnn]
        _ = List.range' 1 (n - 1) ++ [1 + (n - 1)] :=
          List.range'_1_concat
        _ = List.range' 1 (n - 1) ++ [n] := by
          rw [show 1 + (n - 1) = n by omega]
    rw [hrange, List.flatMap_append]
    simp
  have hperm : (n :: n :: v.1).Perm
      ((List.range' 1 n).flatMap fun i => [i, i]) := by
    apply List.perm_iff_count.mpr
    intro x
    rw [hbase]
    have hc := v.2.1.1.count_eq x
    simp only [List.count_cons, List.count_append]
    simp only [List.count_nil]
    omega
  have hbound (x : ℕ) (hx : x ∈ v.1) : 1 ≤ x ∧ x ≤ n - 1 := by
    have hxbase := v.2.1.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hcount (x : ℕ) (hx : x ∈ v.1) : v.1.count x = 2 := by
    apply doubled_count (n - 1) x v.1 v.2.1.1
    rw [List.mem_range'_1]
    have hb := hbound x hx
    omega
  have hsame := (nonnesting_iff_equal_orders v.1 hcount).mp
    ⟨v.2.1.2.1, v.2.1.2.2.1⟩
  have hnobba (a b : ℕ) (hab : a < b) : ¬ List.Sublist [b, b, a] v.1 := by
    intro hsub
    have ha : a ∈ v.1 := hsub.subset (by simp)
    have hb : b ∈ v.1 := hsub.subset (by simp)
    have hfa := v.2.2 a b (hbound a ha).1 hab (hbound b hb).2
    have hsa := hsame a ha b hb hfa
    exact no_bba_sublist_of_same_orders v.1 a b (hcount a ha)
      (hcount b hb) hfa hsa hsub
  refine ⟨hperm, ?_, ?_, ?_⟩
  · intro hocc
    have htail := prefix_nesting_reduces n v.1 [1, 2, 2, 1]
      v.2.1.1 (Or.inl rfl) hocc
    exact v.2.1.2.1 htail
  · intro hocc
    have htail := prefix_nesting_reduces n v.1 [2, 1, 1, 2]
      v.2.1.1 (Or.inr rfl) hocc
    exact v.2.1.2.2.1 htail
  · intro σ hσ hocc
    rcases prefix_pattern_reduces n v.1 σ v.2.1.1 hσ hocc with htail | hcross
    · exact v.2.1.2.2.2 σ hσ htail
    · obtain ⟨a, b, hab, hsub⟩ := hcross
      exact hnobba a b hab hsub

#print axioms large_prefix_construct

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLargeConverse
