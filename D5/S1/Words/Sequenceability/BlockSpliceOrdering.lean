/- GID: D5/S1/Words/Sequenceability/BlockSpliceOrdering
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/BlockSpliceOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Occurrence-indexed block surgery with exact complementary labels and all prefixes. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Defs

/-! Cut an old edge after replacing an initial block by its chord.
The cut is specified by its old index, even when its value equals the new chord.
The vertex path is the concatenation of the blocks `(t+1,...,N-1)`, `(0)`,
and `(k,...,t)`. Empty end blocks require no exceptional convention. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.BlockSpliceOrdering

private def vertexIndex (N k t j : ℕ) : ℕ :=
  if j < N - t - 1 then t + 1 + j
  else if j = N - t - 1 then 0 else k + (j - (N - t - 1) - 1)

private def labelIndex (N k t j : ℕ) : ℕ :=
  if j < N - t - 1 then t + 1 + j
  else if j = N - t - 1 then t else k + (j - (N - t - 1) - 1)

private theorem vertex_bound {N k t j : ℕ} (hk : 2 ≤ k) (hkt : k ≤ t)
    (ht : t < N) (hj : j ≤ N - k) : vertexIndex N k t j < N := by
  unfold vertexIndex
  split_ifs <;> omega

private theorem vertex_injective {N k t : ℕ} (hk : 2 ≤ k) (hkt : k ≤ t)
    (ht : t < N) {i j : ℕ} (hi : i ≤ N - k) (hj : j ≤ N - k)
    (h : vertexIndex N k t i = vertexIndex N k t j) : i = j := by
  unfold vertexIndex at h
  split_ifs at h <;> omega

private theorem vertex_inventory {N k t y : ℕ} (hk : 2 ≤ k) (hkt : k ≤ t)
    (ht : t < N) :
    (∃ j ≤ N - k, vertexIndex N k t j = y) ↔ y = 0 ∨ (k ≤ y ∧ y < N) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    unfold vertexIndex
    split_ifs <;> omega
  · rintro (rfl | ⟨hy, hyN⟩)
    · refine ⟨N - t - 1, by omega, ?_⟩
      simp [vertexIndex]
    · by_cases hyt : t < y
      · refine ⟨y - t - 1, by omega, ?_⟩
        have h : y - t - 1 < N - t - 1 := by omega
        simp only [vertexIndex, ite_eq_left h]
        omega
      · refine ⟨N - t - 1 + 1 + (y - k), by omega, ?_⟩
        unfold vertexIndex
        split_ifs <;> omega

private theorem label_bound {N k t j : ℕ} (hkt : k ≤ t) (ht : t < N)
    (hj : j < N - k) : k ≤ labelIndex N k t j ∧ labelIndex N k t j < N := by
  unfold labelIndex
  split_ifs <;> omega

private theorem label_injective {N k t : ℕ} (hkt : k ≤ t) (ht : t < N)
    {i j : ℕ} (hi : i < N - k) (hj : j < N - k)
    (h : labelIndex N k t i = labelIndex N k t j) : i = j := by
  unfold labelIndex at h
  split_ifs at h <;> omega

private theorem label_inventory {N k t y : ℕ} (hkt : k ≤ t) (ht : t < N) :
    (∃ j < N - k, labelIndex N k t j = y) ↔ k ≤ y ∧ y < N := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact label_bound hkt ht hj
  · rintro ⟨hy, hyN⟩
    by_cases hyt : t < y
    · refine ⟨y - t - 1, by omega, ?_⟩
      have h : y - t - 1 < N - t - 1 := by omega
      simp only [labelIndex, ite_eq_left h]
      omega
    · by_cases hye : y = t
      · refine ⟨N - t - 1, by omega, ?_⟩
        simp [labelIndex, hye]
      · refine ⟨N - t - 1 + 1 + (y - k), by omega, ?_⟩
        unfold labelIndex
        split_ifs <;> omega

private theorem label_permutation {N k t : ℕ} (hkt : k ≤ t) (ht : t < N) :
    ((List.range (N - k)).map (labelIndex N k t)).Perm (List.range' k (N - k)) := by
  apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s := k) (n := N - k))).2
  · intro y
    simp only [List.mem_map, List.mem_range, List.mem_range'_1]
    have h := label_inventory (y := y) hkt ht
    constructor
    · rintro ⟨j, hj, he⟩
      have := h.mp ⟨j, hj, he⟩
      omega
    · intro hy
      obtain ⟨j, hj, he⟩ := h.mpr (by omega)
      exact ⟨j, hj, he⟩
  · apply List.nodup_range.map_on
    intro i hi j hj he
    exact label_injective hkt ht (List.mem_range.mp hi) (List.mem_range.mp hj) he

private theorem vertex_permutation {N k t : ℕ} (hk : 2 ≤ k) (hkt : k ≤ t)
    (ht : t < N) :
    ((List.range (N - k + 1)).map (vertexIndex N k t)).Perm
      (0 :: List.range' k (N - k)) := by
  have hnd : (0 :: List.range' k (N - k)).Nodup := by
    simp only [List.nodup_cons, List.mem_range'_1]
    exact ⟨by omega, List.nodup_range' (s := k) (n := N - k)⟩
  apply (List.perm_ext_iff_of_nodup ?_ hnd).2
  · intro y
    simp only [List.mem_map, List.mem_range, List.mem_cons, List.mem_range'_1]
    have h := vertex_inventory (y := y) hk hkt ht
    constructor
    · rintro ⟨j, hj, he⟩
      have := h.mp ⟨j, by omega, he⟩
      omega
    · intro hy
      obtain ⟨j, hj, he⟩ := h.mpr (by omega)
      exact ⟨j, by omega, he⟩
  · apply List.nodup_range.map_on
    intro i hi j hj he
    exact vertex_injective hk hkt ht (by have := List.mem_range.mp hi; omega)
      (by have := List.mem_range.mp hj; omega) he

variable {G : Type*} [AddCommGroup G]

private theorem splice_difference (z c : ℕ → G) {N k t : ℕ}
    (ht : t < N)
    (hcycle : ∀ i < N, c i = z ((i + 1) % N) - z i)
    (hchord : z k - z 0 = c t) {i : ℕ} (hi : i < N - k) :
    z (vertexIndex N k t (i + 1)) - z (vertexIndex N k t i) =
      c (labelIndex N k t i) := by
  let a := N - t - 1
  have ha : a = N - t - 1 := rfl
  by_cases hia : i < a
  · have hli : labelIndex N k t i = t + 1 + i := by simp [labelIndex, ← ha, hia]
    have hpi : vertexIndex N k t i = t + 1 + i := by simp [vertexIndex, ← ha, hia]
    rw [hli, hpi, hcycle _ (by dsimp [a] at hia; omega)]
    congr 1
    by_cases hnext : i + 1 < a
    · have hm : t + 1 + i + 1 < N := by dsimp [a] at hnext; omega
      simp only [Nat.mod_eq_of_lt hm]
      simp [vertexIndex, ← ha, hnext, Nat.add_assoc]
    · have he : i + 1 = a := by omega
      have hn : t + 1 + i + 1 = N := by dsimp [a] at he; omega
      simp [vertexIndex, ← ha, he, hn]
  · by_cases he : i = a
    · have hnext : ¬ i + 1 < a := by omega
      have hne : i + 1 ≠ a := by omega
      simpa [vertexIndex, labelIndex, ← ha, he, hnext, hne, show ¬ a + 1 < a by omega] using hchord
    · have hnext : ¬ i + 1 < a := by omega
      have hne : i + 1 ≠ a := by omega
      have hstep : k + (i + 1 - a - 1) = k + (i - a - 1) + 1 := by omega
      have hb : k + (i - a - 1) + 1 < N := by dsimp [a] at *; omega
      simp only [vertexIndex, labelIndex, ← ha, ite_eq_right hia, ite_eq_right he,
        ite_eq_right hnext, ite_eq_right hne, hstep]
      rw [hcycle _ (by omega), Nat.mod_eq_of_lt hb]

private theorem prefix_telescope (P : ℕ → G) (L j : ℕ) (hj : j ≤ L) :
    (((List.range L).map (fun i => P (i + 1) - P i)).take j).sum = P j - P 0 := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hj]
  exact List.sum_range_sub j P

/-- The old occurrence `t` is cut and the new chord is retained. The resulting
word has precisely the labels with indices in `[k,N)`, each once, and has no
collision among any bounded prefixes, including empty and full prefixes.
Its full sum is the negative of the label of the cut old edge. -/
theorem block_splice_ordering (z c : ℕ → G) (N k t : ℕ)
    (hk : 2 ≤ k) (hkt : k ≤ t) (ht : t < N)
    (hz : Set.InjOn z (Set.Iio N)) (hc : Set.InjOn c (Set.Iio N))
    (hcycle : ∀ i < N, c i = z ((i + 1) % N) - z i)
    (hchord : z k - z 0 = c t) :
    ∃ (P : ℕ → G) (w : List G),
      ((List.range (N - k + 1)).map P).Perm ((0 :: List.range' k (N - k)).map z) ∧
      ((List.range (N - k + 1)).map P).Nodup ∧
      w = (List.range (N - k)).map (fun i => P (i + 1) - P i) ∧
      (∀ j ≤ N - k, (w.take j).sum = P j - P 0) ∧
      w.Perm ((List.range' k (N - k)).map c) ∧ w.Nodup ∧ w.length = N - k ∧
      Function.Injective (fun j : Fin (w.length + 1) => (w.take j.val).sum) ∧
      (∀ i j : ℕ, i < j → j ≤ w.length → ((w.drop i).take (j - i)).sum ≠ 0) ∧
      w.sum = -c t ∧ w.sum ≠ 0 := by
  let P : ℕ → G := fun j => z (vertexIndex N k t j)
  let w := (List.range (N - k)).map (fun i => P (i + 1) - P i)
  have hpath : ((List.range (N - k + 1)).map P).Perm
      ((0 :: List.range' k (N - k)).map z) := by
    simpa only [P, List.map_map, Function.comp_def] using
      (vertex_permutation hk hkt ht).map z
  have hpathnd : ((List.range (N - k + 1)).map P).Nodup := by
    apply hpath.nodup_iff.mpr
    have hnd : (0 :: List.range' k (N - k)).Nodup := by
      simp only [List.nodup_cons, List.mem_range'_1]
      exact ⟨by omega, List.nodup_range' (s := k) (n := N - k)⟩
    apply hnd.map_on
    intro i hi j hj he
    have hib : i < N := by
      simp only [List.mem_cons, List.mem_range'_1] at hi
      omega
    have hjb : j < N := by
      simp only [List.mem_cons, List.mem_range'_1] at hj
      omega
    exact hz hib hjb he
  have hwlen : w.length = N - k := by simp [w]
  have hdiff : w = ((List.range (N - k)).map (labelIndex N k t)).map c := by
    simp only [w, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact splice_difference z c ht hcycle hchord (List.mem_range.mp hi)
  have hwperm : w.Perm ((List.range' k (N - k)).map c) := by
    rw [hdiff]
    exact (label_permutation hkt ht).map c
  have hwnd : w.Nodup := hwperm.nodup_iff.mpr (by
    apply (List.nodup_range' (s := k) (n := N - k)).map_on
    intro i hi j hj he
    apply hc (show i < N from by have := List.mem_range'_1.mp hi; omega)
      (show j < N from by have := List.mem_range'_1.mp hj; omega) he)
  have hPinj : ∀ i ≤ N - k, ∀ j ≤ N - k, P i = P j → i = j := by
    intro i hi j hj he
    apply vertex_injective hk hkt ht hi hj
    exact hz (vertex_bound hk hkt ht hi) (vertex_bound hk hkt ht hj) he
  have hpref : ∀ j ≤ N - k, (w.take j).sum = P j - P 0 := by
    intro j hj
    exact prefix_telescope P (N - k) j hj
  have hinj : Function.Injective (fun j : Fin (w.length + 1) => (w.take j.val).sum) := by
    intro i j he
    apply Fin.ext
    change (w.take i.val).sum = (w.take j.val).sum at he
    rw [hpref i.val (by omega), hpref j.val (by omega)] at he
    exact hPinj i.val (by omega) j.val (by omega) (sub_left_inj.mp he)
  have hint : ∀ i j : ℕ, i < j → j ≤ w.length →
      ((w.drop i).take (j - i)).sum ≠ 0 := by
    intro i j hij hj he
    have hs := List.sum_take_add_sum_drop (w.take j) i
    rw [List.take_take, Nat.min_eq_left (by omega : i ≤ j), List.drop_take,
      he, add_zero] at hs
    have := hinj (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) hs
    have := congrArg Fin.val this
    exact (Nat.ne_of_lt hij) this
  have hlast : vertexIndex N k t (N - k) = t := by
    unfold vertexIndex
    split_ifs <;> omega
  have hfirst : vertexIndex N k t 0 = (t + 1) % N := by
    by_cases he : t + 1 = N
    · simp [vertexIndex, he, show N - t - 1 = 0 by omega]
    · have ha : 0 < N - t - 1 := by omega
      simp [vertexIndex, ha, Nat.mod_eq_of_lt (show t + 1 < N by omega)]
  have hsum : w.sum = -c t := by
    have hs := hpref (N - k) (le_refl _)
    rw [List.take_of_length_le (by omega)] at hs
    rw [hs, hcycle t ht]
    simp only [P, hlast, hfirst, neg_sub]
  refine ⟨P, w, hpath, hpathnd, rfl, hpref, hwperm, hwnd, hwlen, hinj, hint, hsum, ?_⟩
  simpa using hint 0 w.length (by omega) (le_refl _)

end D5.S1.Words.Sequenceability.BlockSpliceOrdering
