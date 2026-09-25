/- GID: D5/S3/Combinatorics/Geometry/PathBlockGamma/SourceBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/PathBlockGamma/SourceBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite differences invert the literal prefix-maximum source transformation. -/

import D5.S3.Combinatorics.Geometry.PathBlockGamma.SourceEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.PathBlockGamma

open scoped BigOperators
open Classical
noncomputable section

/-- Prefix maxima and finite differences give the exact all-parameter source bijection. -/
def sourceBoundedEquiv {a m q : ℕ} (ha : 0 < a) (hm : 1 < m) :
    SourcePoint a m q ≃ BoundedMonotone a m q where
  toFun := sourceToBounded ha hm
  invFun := boundedToSource ha hm
  left_inv x := by
    have prefix_last (i : Fin m) : prefixSum x i (lastLevel ha) = blockSum x i := by
      simp only [prefixSum, Fin.partialSum, lastLevel, blockSum]
      change (List.take (a - 1 + 1) (List.ofFn (x.coord i))).sum = ∑ k, x.coord i k
      rw [show (a - 1 + 1) = a by omega, List.take_of_length_le (by simp), List.sum_ofFn]
    have even_neighbors (i : Fin m) (hi : ¬ oddBlock i) : (neighborSet m i).Nonempty := by
      have himod := Nat.mod_lt i.val (by omega : 0 < 2)
      have hidiv := Nat.div_add_mod i.val 2
      let j : Fin m := ⟨i.val - 1, by omega⟩
      refine ⟨j, ?_⟩
      simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change (i.val - 1) % 2 = 0
        omega
      · right
        change i.val - 1 + 1 = i.val
        omega
    have source_neighbor_max (i : Fin m) (hi : ¬ oddBlock i) :
        mapNeighborMax ha (sourceToBounded ha hm x) i = neighborMax x i := by
      have hne := even_neighbors i hi
      simp only [mapNeighborMax, neighborMax, dif_pos hne]
      apply Finset.sup'_congr hne rfl
      intro j hj
      have hjodd := (Finset.mem_filter.mp hj).2.1
      change sourceFunction x ⟨j, lastLevel ha⟩ = blockSum x j
      rw [sourceFunction, if_pos hjodd, prefix_last]
    apply SourcePoint.ext
    funext i k
    change mapCoordinate ha (sourceToBounded ha hm x) i k = x.coord i k
    by_cases hk : k.val = 0
    · have hk0 : k = ⟨0, ha⟩ := Fin.ext hk
      subst k
      by_cases hi : oddBlock i
      · change (if oddBlock i then sourceFunction x ⟨i, ⟨0, ha⟩⟩
            else sourceFunction x ⟨i, ⟨0, ha⟩⟩ -
              mapNeighborMax ha (sourceToBounded ha hm x) i) = x.coord i ⟨0, ha⟩
        rw [if_pos hi, sourceFunction, if_pos hi]
        rw [prefixSum, Fin.partialSum_succ]
        simp [Fin.partialSum]
      · change (if oddBlock i then sourceFunction x ⟨i, ⟨0, ha⟩⟩
            else sourceFunction x ⟨i, ⟨0, ha⟩⟩ -
              mapNeighborMax ha (sourceToBounded ha hm x) i) = x.coord i ⟨0, ha⟩
        rw [if_neg hi, sourceFunction, if_neg hi, source_neighbor_max i hi]
        rw [prefixSum, Fin.partialSum_succ]
        simp [Fin.partialSum]
    · have hindex : (previousLevel k hk).succ = k.castSucc := by
        apply Fin.ext
        simp [previousLevel]
        omega
      have hprefix :
          prefixSum x i k = prefixSum x i (previousLevel k hk) + x.coord i k := by
        rw [prefixSum, Fin.partialSum_succ, ← hindex]
        rfl
      rw [mapCoordinate, dif_neg hk]
      by_cases hi : oddBlock i
      · change (if oddBlock i then prefixSum x i k
            else neighborMax x i + prefixSum x i k) -
            (if oddBlock i then prefixSum x i (previousLevel k hk)
            else neighborMax x i + prefixSum x i (previousLevel k hk)) = x.coord i k
        rw [if_pos hi, if_pos hi, hprefix]
        omega
      · change (if oddBlock i then prefixSum x i k
            else neighborMax x i + prefixSum x i k) -
            (if oddBlock i then prefixSum x i (previousLevel k hk)
            else neighborMax x i + prefixSum x i (previousLevel k hk)) = x.coord i k
        rw [if_neg hi, if_neg hi, hprefix]
        omega
  right_inv f := by
    have prefix_last (g : Fin m → Fin a → ℕ) (i : Fin m) :
        Fin.partialSum (g i) (lastLevel ha).succ = ∑ k, g i k := by
      rw [Fin.partialSum]
      have htake : (lastLevel ha).succ.val = a := by
        change a - 1 + 1 = a
        omega
      rw [htake, List.take_of_length_le (by simp), List.sum_ofFn]
    have block_sum (i : Fin m) :
        blockSum (boundedToSource ha hm f) i =
          if oddBlock i then f.1 ⟨i, lastLevel ha⟩
          else f.1 ⟨i, lastLevel ha⟩ - mapNeighborMax ha f i := by
      rw [blockSum]
      change (∑ k, mapCoordinate ha f i k) = _
      rw [← prefix_last (mapCoordinate ha f) i]
      exact mapCoordinate_prefix ha f i (lastLevel ha)
    have even_neighbors (i : Fin m) (hi : ¬ oddBlock i) : (neighborSet m i).Nonempty := by
      have himod := Nat.mod_lt i.val (by omega : 0 < 2)
      have hidiv := Nat.div_add_mod i.val 2
      let j : Fin m := ⟨i.val - 1, by omega⟩
      refine ⟨j, ?_⟩
      simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change (i.val - 1) % 2 = 0
        omega
      · right
        change i.val - 1 + 1 = i.val
        omega
    have reconstructed_neighbor_max (i : Fin m) (hi : ¬ oddBlock i) :
        neighborMax (boundedToSource ha hm f) i = mapNeighborMax ha f i := by
      have hne := even_neighbors i hi
      simp only [neighborMax, mapNeighborMax, dif_pos hne]
      apply Finset.sup'_congr hne rfl
      intro j hj
      have hjodd := (Finset.mem_filter.mp hj).2.1
      rw [block_sum, if_pos hjodd]
      simp [lastLevel]
    apply Subtype.ext
    funext v
    rcases v with ⟨i, k⟩
    change sourceFunction (boundedToSource ha hm f) ⟨i, k⟩ = f.1 ⟨i, k⟩
    by_cases hv : oddBlock i
    · rw [sourceFunction, if_pos hv]
      change Fin.partialSum (mapCoordinate ha f i) k.succ = f.1 ⟨i, k⟩
      rw [mapCoordinate_prefix ha f i k, if_pos hv]
    · rw [sourceFunction, if_neg hv, reconstructed_neighbor_max i hv]
      change mapNeighborMax ha f i +
          Fin.partialSum (mapCoordinate ha f i) k.succ = f.1 ⟨i, k⟩
      rw [mapCoordinate_prefix ha f i k, if_neg hv]
      have hbase : mapNeighborMax ha f i ≤ f.1 ⟨i, k⟩ := by
        have hne := even_neighbors i hv
        simp only [mapNeighborMax, dif_pos hne]
        apply Finset.sup'_le hne
        intro j hj
        apply f.2.2
        right
        have hj' := (Finset.mem_filter.mp hj).2
        refine ⟨hj'.1, hv, ?_⟩
        rcases hj'.2 with h | h
        · exact Or.inr h
        · exact Or.inl h
      omega

/-- The same source bijection with the explicit positive complement `sigma = q + 1 - Y`. -/
def sourcePositiveEquiv {a m q : ℕ} (ha : 0 < a) (hm : 1 < m) :
    SourcePoint a m q ≃ PositiveAntitone a m q := by
  let complement : BoundedMonotone a m q ≃ PositiveAntitone a m q :=
    { toFun := fun f => ⟨fun v => q + 1 - f.1 v, by
        constructor
        · intro v
          constructor
          · have hv := f.2.1 v
            exact Nat.le_sub_of_add_le (by omega)
          · exact Nat.sub_le _ _
        · intro x y hxy
          exact Nat.sub_le_sub_left (f.2.2 hxy) _⟩
      invFun := fun s => ⟨fun v => q + 1 - s.1 v, by
        constructor
        · intro v
          have hv := s.2.1 v
          exact Nat.sub_le_iff_le_add.mpr (by omega)
        · intro x y hxy
          exact Nat.sub_le_sub_left (s.2.2 hxy) _⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext v
        simp only
        have hv := f.2.1 v
        omega
      right_inv := by
        intro s
        apply Subtype.ext
        funext v
        simp only
        have hv := s.2.1 v
        omega }
  exact (sourceBoundedEquiv ha hm).trans complement

end
end D5.S3.Combinatorics.Geometry.PathBlockGamma
