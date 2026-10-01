/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveInc
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveInc
   mirror-E: none(waiver:row-four-primitive-increasing)
   anchors: []
   utility: none
   digest: Tracks occurrence positions and cuts through crossing insertion. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveInc

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing

theorem crossing_positions (r : List ℕ) (n j : ℕ)
    (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hj : 1 ≤ j ∧ j ≤ n) :
    let v := 1 :: r
    let w := 1 :: 2 :: 1 :: shift 1 r
    (w).idxOf (j + 1) =
      (if (v).idxOf j = 0 then 1 else (v).idxOf j + 2) ∧
      secondPos (j + 1) w = secondPos j v + 2 := by
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
  let v := 1 :: r
  let w := 1 :: 2 :: 1 :: shift 1 r
  have hpermW := (crossing_insert r n hv).1
  have hrangeV : j ∈ List.range' 1 n := by
    rw [List.mem_range'_1]
    omega
  have hrangeW : j + 1 ∈ List.range' 1 (n + 1) := by
    rw [List.mem_range'_1]
    omega
  have hcountV : v.count j = 2 := doubled_count n j v hv.1 hrangeV
  have hcountW : w.count (j + 1) = 2 :=
    doubled_count (n + 1) (j + 1) w hpermW hrangeW
  have pv := count_two_positions j v hcountV
  have pw := count_two_positions (j + 1) w hcountW
  let F : ℕ → ℕ := fun p => if p = 0 then 1 else p + 2
  have hmap (p a : ℕ) (hval : v[p]? = some a) :
      w[F p]? = some (a + 1) := by
    cases p with
    | zero =>
      have ha : a = 1 := by simpa [v] using hval.symm
      subst a
      simp [w, F]
    | succ p =>
      have hrval : r[p]? = some a := by simpa [v] using hval
      have hwval : w[p + 3]? = some (a + 1) := by
        simp [w, shift, hrval]
      simpa [F, Nat.add_assoc] using hwval
  have hq := hmap ((v).idxOf j) j pv.2.1
  have hp := hmap (secondPos j v) j pv.2.2
  have hFlt : F ((v).idxOf j) < F (secondPos j v) := by
    by_cases hzero : (v).idxOf j = 0
    · have hpne : secondPos j v ≠ 0 := by omega
      simp [F, hzero, hpne]
    · have hpne : secondPos j v ≠ 0 := by omega
      simp [F, hzero, hpne]
      omega
  have hqCase := (count_two_position_iff (j + 1) w hcountW (F ((v).idxOf j))).mp hq
  have hpCase := (count_two_position_iff (j + 1) w hcountW (F (secondPos j v))).mp hp
  have hfirstF : (w).idxOf (j + 1) = F ((v).idxOf j) := by
    rcases hqCase with h | h
    · exact h.symm
    · rcases hpCase with hp' | hp'
      · omega
      · omega
  have hsecondF : secondPos (j + 1) w = F (secondPos j v) := by
    rcases hpCase with h | h
    · rw [hfirstF] at h
      omega
    · exact h.symm
  constructor
  · exact hfirstF
  · have hpne : secondPos j v ≠ 0 := by omega
    simpa [F, hpne] using hsecondF

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveInc

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveInc.crossing_positions
