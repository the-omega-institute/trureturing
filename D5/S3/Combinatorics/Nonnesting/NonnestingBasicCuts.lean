/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicCuts
   mirror-E: none(waiver:ordered-value-cut)
   anchors: []
   utility: none
   digest: Converts separation of indexed occurrences into a doubled-word value cut. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts

open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

theorem filter_partition_of_separated (w : List ℕ) (k : ℕ)
    (horder : ∀ i j x y : ℕ, w[i]? = some x → w[j]? = some y →
      x ≤ k → k < y → i < j) :
    w = w.filter (fun x => decide (x ≤ k)) ++
      w.filter (fun x => decide (k < x)) := by
  induction w with
  | nil => simp
  | cons z zs ih =>
    by_cases hz : z ≤ k
    · have htail : ∀ i j x y : ℕ, zs[i]? = some x → zs[j]? = some y →
          x ≤ k → k < y → i < j := by
        intro i j x y hix hjy hx hy
        have hix' : (z :: zs)[i + 1]? = some x := by simpa using hix
        have hjy' : (z :: zs)[j + 1]? = some y := by simpa using hjy
        have h := horder (i + 1) (j + 1) x y hix' hjy' hx hy
        omega
      have hpart := ih htail
      calc
        z :: zs = z :: (zs.filter (fun x => decide (x ≤ k)) ++
            zs.filter (fun x => decide (k < x))) := congrArg (z :: ·) hpart
        _ = (z :: zs).filter (fun x => decide (x ≤ k)) ++
            (z :: zs).filter (fun x => decide (k < x)) := by simp [hz]
    · have hhigh : k < z := by omega
      have htail : ∀ x ∈ zs, k < x := by
        intro x hx
        by_contra hnot
        have hlow : x ≤ k := by omega
        have hidx : zs[zs.idxOf x]? = some x := List.getElem?_idxOf hx
        have hidx' : (z :: zs)[zs.idxOf x + 1]? = some x := by simpa using hidx
        have hzero : (z :: zs)[0]? = some z := by simp
        have h := horder (zs.idxOf x + 1) 0 x z hidx' hzero hlow hhigh
        omega
      have hlowFilter : zs.filter (fun x => decide (x ≤ k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp [Nat.not_le.mpr (htail x hx)]
      have hhighFilter : zs.filter (fun x => decide (k < x)) = zs := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp [htail x hx]
      simp [hz, hhigh, hlowFilter, hhighFilter]

theorem valueCut_of_separated_indices (n k : ℕ) (w : List ℕ)
    (hw : w.Perm ((List.range' 1 n).flatMap fun i => [i, i]))
    (hk : k ≤ n)
    (horder : ∀ i j x y : ℕ, w[i]? = some x → w[j]? = some y →
      x ≤ k → k < y → i < j) : valueCut w k := by
  let u := w.filter (fun x => decide (x ≤ k))
  let v := w.filter (fun x => decide (k < x))
  have heq : w = u ++ v := filter_partition_of_separated w k horder
  have hrange : List.range' 1 n =
      List.range' 1 k ++ List.range' (k + 1) (n - k) := by
    have h := List.range'_append_1 (s := 1) (m := k) (n := n - k)
    simpa [Nat.add_sub_of_le hk, Nat.add_comm] using h.symm
  let low : List ℕ := (List.range' 1 k).flatMap fun i => [i, i]
  let high : List ℕ := (List.range' (k + 1) (n - k)).flatMap fun i => [i, i]
  have hbase : ((List.range' 1 n).flatMap fun i => [i, i]) = low ++ high := by
    simp [hrange, low, high, List.flatMap_append]
  have hlowRange : ∀ x ∈ low, x ≤ k := by
    intro x hx
    obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hx
    have hxi : x = i := by simpa using hii
    subst x
    have hir : 1 ≤ i ∧ i < 1 + k := by simpa using hi
    omega
  have hhighRange : ∀ x ∈ high, k < x := by
    intro x hx
    obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hx
    have hxi : x = i := by simpa using hii
    subst x
    have hir : k + 1 ≤ i ∧ i < k + 1 + (n - k) := by simpa using hi
    omega
  have huPerm : u.Perm low := by
    have hf := hw.filter (fun x => decide (x ≤ k))
    rw [hbase, List.filter_append] at hf
    have hlowFilter : low.filter (fun x => decide (x ≤ k)) = low := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hlowRange x hx]
    have hhighFilter : high.filter (fun x => decide (x ≤ k)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp [Nat.not_le.mpr (hhighRange x hx)]
    simpa [u, hlowFilter, hhighFilter] using hf
  have hlowLength : low.length = 2 * k := by
    simp [low, List.length_flatMap, Nat.mul_comm]
  have hulength : u.length = 2 * k := huPerm.length_eq.trans hlowLength
  refine ⟨u, v, heq, hulength, ?_, ?_⟩
  · intro x hx
    have hx' := List.mem_filter.mp hx
    have hxbase := hw.mem_iff.mp hx'.1
    obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hxbase
    have hxi : x = i := by simpa using hii
    subst x
    have hir : 1 ≤ i ∧ i < 1 + n := by simpa using hi
    exact ⟨hir.1, by simpa [u] using hx'.2⟩
  · intro x hx
    exact by simpa [v] using (List.mem_filter.mp hx).2

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts.filter_partition_of_separated
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts.valueCut_of_separated_indices
