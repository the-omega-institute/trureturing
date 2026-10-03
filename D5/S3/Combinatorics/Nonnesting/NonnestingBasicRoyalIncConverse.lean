/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncConverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncConverse
   mirror-E: none(waiver:royal-increasing-block-converse)
   anchors: []
   utility: none
   digest: Shows increasing skew blocks avoid both low-row first-order triples. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse

open NonnestingBasicRoyalIncBlocks

theorem incBlocks_avoids (n : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
    ¬ NonnestingDefs.Occurs [1, 3, 2] (incBlocks n ks) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] (incBlocks n ks) := by
  classical
  have bounded : ∀ (m : ℕ) (xs : List ℕ),
      (∀ x ∈ xs, 0 < x) → xs.sum ≤ m →
      ∀ a ∈ incBlocks m xs, a ≤ m := by
    intro m xs
    induction xs generalizing m with
    | nil =>
      intro _ _ a ha; simp [incBlocks] at ha
    | cons r xs ih =>
      intro hp hs a ha
      have hr : r ≤ m := by
        simp only [List.sum_cons] at hs; omega
      have hpos' : ∀ x ∈ xs, 0 < x := by
        intro x hx; exact hp x (by simp [hx])
      have hsum' : xs.sum ≤ m - r := by
        simp only [List.sum_cons] at hs; omega
      change a ∈ List.range' (m - r + 1) r ++ incBlocks (m - r) xs at ha
      rcases List.mem_append.mp ha with hpre | htail
      · have hval := List.mem_range'_1.mp hpre
        omega
      · have hval := ih (m - r) hpos' hsum' a htail
        omega
  have outer : ∀ (m : ℕ) (xs : List ℕ),
      (∀ x ∈ xs, 0 < x) → xs.sum ≤ m →
      ∀ i j k (hi : i < (incBlocks m xs).length)
        (hj : j < (incBlocks m xs).length)
        (hk : k < (incBlocks m xs).length),
        i < j → j < k → (incBlocks m xs)[i] < (incBlocks m xs)[k] →
        (incBlocks m xs)[i] < (incBlocks m xs)[j] ∧
          (incBlocks m xs)[j] < (incBlocks m xs)[k] := by
    intro m xs
    induction xs generalizing m with
    | nil =>
      intro _ _ i j k hi; simp [incBlocks] at hi
    | cons r xs ih =>
      intro hp hs i j k hi hj hk hij hjk hik; let q := incBlocks (m - r) xs
      have hr : r ≤ m := by
        simp only [List.sum_cons] at hs; omega
      have hrpos : 0 < r := hp r (by simp)
      have hpos' : ∀ x ∈ xs, 0 < x := by
        intro x hx; exact hp x (by simp [hx])
      have hsum' : xs.sum ≤ m - r := by
        simp only [List.sum_cons] at hs; omega
      have hlen : (incBlocks m (r :: xs)).length = r + q.length := by
        simp [incBlocks, q]
      by_cases hki : k < r
      · have hii : i < r := by omega
        have hji : j < r := by omega
        have hvalI : (incBlocks m (r :: xs))[i] = m - r + 1 + i := by
          simp [incBlocks, hii]
        have hvalJ : (incBlocks m (r :: xs))[j] = m - r + 1 + j := by
          simp [incBlocks, hji]
        have hvalK : (incBlocks m (r :: xs))[k] = m - r + 1 + k := by
          simp [incBlocks, hki]
        rw [hvalI, hvalJ, hvalK]; omega
      · by_cases hii : i < r
        · have hiq : k - r < q.length := by
            rw [hlen] at hk; omega
          have hleft : m - r + 1 ≤ (incBlocks m (r :: xs))[i] := by
            simp [incBlocks, hii]
          have hvalK : (incBlocks m (r :: xs))[k] = q[k - r] := by
            simp [incBlocks, List.getElem_append, q, show ¬ k < r by omega]
          have hright : (incBlocks m (r :: xs))[k] ≤ m - r := by
            have hv : q[k - r] ∈ q := List.getElem_mem hiq
            have hb := bounded (m - r) xs hpos' hsum' q[k - r] hv; rw [hvalK]; exact hb
          omega
        · have hiq : i - r < q.length := by
            rw [hlen] at hi; omega
          have hjq : j - r < q.length := by
            rw [hlen] at hj; omega
          have hkq : k - r < q.length := by
            rw [hlen] at hk; omega
          have hshift : i - r < j - r ∧ j - r < k - r := by omega
          have heqI : (incBlocks m (r :: xs))[i] = q[i - r] := by
            simp [incBlocks, List.getElem_append, q, show ¬ i < r by omega]
          have heqJ : (incBlocks m (r :: xs))[j] = q[j - r] := by
            simp [incBlocks, List.getElem_append, q, show ¬ j < r by omega]
          have heqK : (incBlocks m (r :: xs))[k] = q[k - r] := by
            simp [incBlocks, List.getElem_append, q, show ¬ k < r by omega]
          rw [heqI, heqK] at hik
          obtain ⟨hl, hr⟩ := ih (m - r) hpos' hsum'
            (i - r) (j - r) (k - r) hiq hjq hkq hshift.1 hshift.2 hik
          simpa only [heqI, heqJ, heqK] using And.intro hl hr
  have hbet := outer n ks hpos (by omega)
  constructor
  · intro hocc
    obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
    change List.Sublist [x 1, x 3, x 2] (incBlocks n ks) at hsub
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
    have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
    have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
    have hvalI : (incBlocks n ks)[i] = x 1 := by
      simpa [i] using (hf (0 : Fin 3)).symm
    have hvalJ : (incBlocks n ks)[j] = x 3 := by
      simpa [j] using (hf (1 : Fin 3)).symm
    have hvalK : (incBlocks n ks)[k] = x 2 := by
      simpa [k] using (hf (2 : Fin 3)).symm
    have houter := hbet i j k (f 0).isLt (f 1).isLt (f 2).isLt hij hjk
      (by rw [hvalI, hvalK]; exact hxlt 1 (by omega) (by decide))
    rw [hvalJ, hvalK] at houter
    have h23 : x 2 < x 3 := by simpa using hxlt 2 (by omega) (by decide)
    omega
  · intro hocc
    obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
    change List.Sublist [x 2, x 1, x 3] (incBlocks n ks) at hsub
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
    have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
    have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
    have hvalI : (incBlocks n ks)[i] = x 2 := by
      simpa [i] using (hf (0 : Fin 3)).symm
    have hvalJ : (incBlocks n ks)[j] = x 1 := by
      simpa [j] using (hf (1 : Fin 3)).symm
    have hvalK : (incBlocks n ks)[k] = x 3 := by
      simpa [k] using (hf (2 : Fin 3)).symm
    have houter := hbet i j k (f 0).isLt (f 1).isLt (f 2).isLt hij hjk
      (by
        rw [hvalI, hvalK]
        simpa using hxlt 2 (by omega) (by decide))
    rw [hvalI, hvalJ] at houter
    have h12 : x 1 < x 2 := by simpa using hxlt 1 (by omega) (by decide)
    omega
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse.incBlocks_avoids
