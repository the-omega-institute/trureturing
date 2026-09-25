/- GID: D5/S3/Combinatorics/Geometry/PathBlockGamma/SourceEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/PathBlockGamma/SourceEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Prefix sums and adjacent odd-block maxima identify source points with bounded order maps. -/

import D5.S3.Combinatorics.Geometry.PathBlockGamma.LiteralPoset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.PathBlockGamma

open scoped BigOperators
open Classical
noncomputable section

@[ext] structure SourcePoint (a m q : ℕ) where
  coord : Fin m → Fin a → ℕ
  adjacent_le : ∀ i : Fin (m - 1),
    (∑ k, coord ⟨i.val, by omega⟩ k) +
      ∑ k, coord ⟨i.val + 1, by omega⟩ k ≤ q

def blockSum {a m q : ℕ} (x : SourcePoint a m q) (i : Fin m) : ℕ :=
  ∑ k, x.coord i k

def prefixSum {a m q : ℕ} (x : SourcePoint a m q) (i : Fin m) (k : Fin a) : ℕ :=
  Fin.partialSum (x.coord i) k.succ

def neighborSet (m : ℕ) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => oddBlock j ∧ adjacentBlocks i j

def neighborMax {a m q : ℕ} (x : SourcePoint a m q) (i : Fin m) : ℕ :=
  if hi : (neighborSet m i).Nonempty then
    (neighborSet m i).sup' hi (blockSum x)
  else 0

def sourceFunction {a m q : ℕ} (x : SourcePoint a m q) : Vertex a m → ℕ := fun v =>
  if oddBlock v.block then prefixSum x v.block v.level
  else neighborMax x v.block + prefixSum x v.block v.level

def BoundedMonotone (a m q : ℕ) : Type :=
  {f : Vertex a m → ℕ // (∀ v, f v ≤ q) ∧ Monotone f}

def PositiveAntitone (a m q : ℕ) : Type :=
  {s : Vertex a m → ℕ //
    (∀ v, 1 ≤ s v ∧ s v ≤ q + 1) ∧ Antitone s}

def previousLevel {a : ℕ} (k : Fin a) (hk : k.val ≠ 0) : Fin a :=
  ⟨k.val - 1, by omega⟩

def lastLevel {a : ℕ} (ha : 0 < a) : Fin a := ⟨a - 1, by omega⟩

def mapNeighborMax {a m q : ℕ} (ha : 0 < a) (f : BoundedMonotone a m q)
    (i : Fin m) : ℕ :=
  if hi : (neighborSet m i).Nonempty then
    (neighborSet m i).sup' hi fun j => f.1 ⟨j, ⟨a - 1, by omega⟩⟩
  else 0

def mapCoordinate {a m q : ℕ} (ha : 0 < a) (f : BoundedMonotone a m q)
    (i : Fin m) (k : Fin a) : ℕ :=
  if hk : k.val = 0 then
    if oddBlock i then f.1 ⟨i, k⟩ else f.1 ⟨i, k⟩ - mapNeighborMax ha f i
  else f.1 ⟨i, k⟩ - f.1 ⟨i, previousLevel k hk⟩

def sourceToBounded {a m q : ℕ} (ha : 0 < a) (hm : 1 < m)
    (x : SourcePoint a m q) : BoundedMonotone a m q := by
  have prefix_mono (i : Fin m) {k l : Fin a} (hkl : k ≤ l) :
      prefixSum x i k ≤ prefixSum x i l := by
    have hp : (List.ofFn (x.coord i)).take k.succ.val <+:
        (List.ofFn (x.coord i)).take l.succ.val := by
      rw [List.prefix_take_iff]
      constructor
      · exact List.take_prefix _ _
      · simp
        omega
    exact hp.sublist.sum_le_sum (by simp [prefixSum, Fin.partialSum])
  have prefix_le_total (i : Fin m) (k : Fin a) : prefixSum x i k ≤ blockSum x i := by
    have hp := List.take_sublist k.succ.val (List.ofFn (x.coord i))
    simpa [prefixSum, Fin.partialSum, blockSum, List.sum_ofFn] using
      hp.sum_le_sum (by simp)
  have adjacent_sum {i j : Fin m} (hij : adjacentBlocks i j) :
      blockSum x i + blockSum x j ≤ q := by
    rcases hij with hij | hij
    · let t : Fin (m - 1) := ⟨i.val, by omega⟩
      have hnext : (⟨i.val + 1, by omega⟩ : Fin m) = j := Fin.ext hij
      simpa [blockSum, t, hnext] using x.adjacent_le t
    · let t : Fin (m - 1) := ⟨j.val, by omega⟩
      have ht := x.adjacent_le t
      have hnext : (⟨j.val + 1, by omega⟩ : Fin m) = i := Fin.ext hij
      simpa [blockSum, t, hnext, Nat.add_comm] using ht
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
  have block_neighbor (i : Fin m) : ∃ j : Fin m, adjacentBlocks i j := by
    by_cases hright : i.val + 1 < m
    · exact ⟨⟨i.val + 1, hright⟩, Or.inl rfl⟩
    · have hi : 0 < i.val := by omega
      let j : Fin m := ⟨i.val - 1, by omega⟩
      refine ⟨j, Or.inr ?_⟩
      change i.val - 1 + 1 = i.val
      omega
  refine ⟨sourceFunction x, ?_, ?_⟩
  · intro v
    by_cases hv : oddBlock v.block
    · change (if oddBlock v.block then prefixSum x v.block v.level
        else neighborMax x v.block + prefixSum x v.block v.level) ≤ q
      rw [if_pos hv]
      obtain ⟨j, hj⟩ := block_neighbor v.block
      exact (prefix_le_total v.block v.level).trans
        ((Nat.le_add_right _ _).trans (adjacent_sum hj))
    · have hne := even_neighbors v.block hv
      obtain ⟨j, hjmem, hjmax⟩ :=
        Finset.exists_mem_eq_sup' hne (blockSum x)
      have hpair := adjacent_sum (i := v.block) (j := j) (by
        simpa [neighborSet] using (Finset.mem_filter.mp hjmem).2.2)
      have hp := prefix_le_total v.block v.level
      simp [sourceFunction, hv, neighborMax, hne, ← hjmax]
      omega
  · intro u v huv
    rcases huv with hsame | hcross
    · by_cases hu : oddBlock u.block
      · change (if oddBlock u.block then prefixSum x u.block u.level
          else neighborMax x u.block + prefixSum x u.block u.level) ≤
          if oddBlock v.block then prefixSum x v.block v.level
          else neighborMax x v.block + prefixSum x v.block v.level
        rw [if_pos hu, if_pos (hsame.1 ▸ hu)]
        rw [hsame.1]
        exact prefix_mono v.block hsame.2
      · change (if oddBlock u.block then prefixSum x u.block u.level
          else neighborMax x u.block + prefixSum x u.block u.level) ≤
          if oddBlock v.block then prefixSum x v.block v.level
          else neighborMax x v.block + prefixSum x v.block v.level
        rw [if_neg hu, if_neg (by simpa [hsame.1] using hu)]
        rw [hsame.1]
        exact Nat.add_le_add_left (prefix_mono v.block hsame.2) _
    · have hv : ¬ oddBlock v.block := hcross.2.1
      have hne := even_neighbors v.block hv
      have humem : u.block ∈ neighborSet m v.block := by
        simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hcross.1, ?_⟩
        rcases hcross.2.2 with h | h
        · exact Or.inr h
        · exact Or.inl h
      have hprefix := prefix_le_total u.block u.level
      have hmax : blockSum x u.block ≤ neighborMax x v.block := by
        simp only [neighborMax, dif_pos hne]
        exact Finset.le_sup' _ humem
      change (if oddBlock u.block then prefixSum x u.block u.level
        else neighborMax x u.block + prefixSum x u.block u.level) ≤
        if oddBlock v.block then prefixSum x v.block v.level
        else neighborMax x v.block + prefixSum x v.block v.level
      rw [if_pos hcross.1, if_neg hv]
      exact hprefix.trans (hmax.trans (Nat.le_add_right _ _))

theorem mapCoordinate_prefix {a m q : ℕ} (ha : 0 < a) (f : BoundedMonotone a m q)
    (i : Fin m) (k : Fin a) :
    Fin.partialSum (mapCoordinate ha f i) k.succ =
      if oddBlock i then f.1 ⟨i, k⟩ else f.1 ⟨i, k⟩ - mapNeighborMax ha f i := by
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
  have base_le (i : Fin m) (hi : ¬ oddBlock i) (k : Fin a) :
      mapNeighborMax ha f i ≤ f.1 ⟨i, k⟩ := by
    have hne := even_neighbors i hi
    simp only [mapNeighborMax, dif_pos hne]
    apply Finset.sup'_le hne
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    apply f.2.2
    right
    refine ⟨hj'.1, hi, ?_⟩
    rcases hj'.2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  induction k using Fin.induction with
  | zero =>
      rw [Fin.partialSum_succ]
      simp [Fin.partialSum, mapCoordinate]
  | succ k ih =>
      rw [Fin.partialSum_succ]
      have hprev :
          Fin.partialSum (mapCoordinate ha f i) (Fin.castSucc k).succ =
            if oddBlock i then f.1 ⟨i, k.castSucc⟩
            else f.1 ⟨i, k.castSucc⟩ - mapNeighborMax ha f i := ih
      have hindex : (k.succ.castSucc : Fin (n + 2)) = (k.castSucc.succ : Fin (n + 2)) :=
        Fin.ext rfl
      rw [hindex, hprev]
      have hmono : f.1 ⟨i, k.castSucc⟩ ≤ f.1 ⟨i, k.succ⟩ := by
        apply f.2.2
        left
        refine ⟨rfl, ?_⟩
        exact Fin.le_iff_val_le_val.mpr (by simp)
      have hpred : previousLevel k.succ (by simp) = k.castSucc := by
        apply Fin.ext
        simp [previousLevel]
      by_cases hi : oddBlock i
      · rw [if_pos hi, if_pos hi]
        rw [show mapCoordinate ha f i k.succ =
            f.1 ⟨i, k.succ⟩ - f.1 ⟨i, k.castSucc⟩ by
          simp [mapCoordinate, hpred]]
        exact Nat.add_sub_of_le hmono
      · have hbase := base_le i hi k.castSucc
        rw [if_neg hi, if_neg hi]
        rw [show mapCoordinate ha f i k.succ =
            f.1 ⟨i, k.succ⟩ - f.1 ⟨i, k.castSucc⟩ by
          simp [mapCoordinate, hpred]]
        omega

def boundedToSource {a m q : ℕ} (ha : 0 < a) (hm : 1 < m)
    (f : BoundedMonotone a m q) : SourcePoint a m q := by
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
  have base_le (i : Fin m) (hi : ¬ oddBlock i) (k : Fin a) :
      mapNeighborMax ha f i ≤ f.1 ⟨i, k⟩ := by
    have hne := even_neighbors i hi
    simp only [mapNeighborMax, dif_pos hne]
    apply Finset.sup'_le hne
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    apply f.2.2
    right
    refine ⟨hj'.1, hi, ?_⟩
    rcases hj'.2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  have total_eq_prefix (i : Fin m) :
      (∑ k, mapCoordinate ha f i k) =
        Fin.partialSum (mapCoordinate ha f i) (lastLevel ha).succ := by
    rw [Fin.partialSum]
    have htake : (lastLevel ha).succ.val = a := by
      change a - 1 + 1 = a
      omega
    rw [htake, List.take_of_length_le (by simp), List.sum_ofFn]
  refine ⟨mapCoordinate ha f, ?_⟩
  intro t
  let left : Fin m := ⟨t.val, by omega⟩
  let right : Fin m := ⟨t.val + 1, by omega⟩
  rw [total_eq_prefix left, total_eq_prefix right,
    mapCoordinate_prefix ha f left (lastLevel ha),
    mapCoordinate_prefix ha f right (lastLevel ha)]
  by_cases hl : oddBlock left
  · have hr : ¬ oddBlock right := by
      simp only [oddBlock, left, right] at hl ⊢
      omega
    rw [if_pos hl, if_neg hr]
    have hne := even_neighbors right hr
    have hmem : left ∈ neighborSet m right := by
      simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hl, Or.inr rfl⟩
    have hbase : f.1 ⟨left, lastLevel ha⟩ ≤ mapNeighborMax ha f right := by
      simp only [mapNeighborMax, dif_pos hne]
      exact Finset.le_sup' (fun j => f.1 ⟨j, lastLevel ha⟩) hmem
    have hbaseEven := base_le right hr (lastLevel ha)
    have hq := f.2.1 ⟨right, lastLevel ha⟩
    omega
  · have hr : oddBlock right := by
      simp only [oddBlock, left, right] at hl ⊢
      have hmod := Nat.mod_lt t.val (by omega : 0 < 2)
      omega
    rw [if_neg hl, if_pos hr]
    have hne := even_neighbors left hl
    have hmem : right ∈ neighborSet m left := by
      simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr, Or.inl rfl⟩
    have hbase : f.1 ⟨right, lastLevel ha⟩ ≤ mapNeighborMax ha f left := by
      simp only [mapNeighborMax, dif_pos hne]
      exact Finset.le_sup' (fun j => f.1 ⟨j, lastLevel ha⟩) hmem
    have hbaseEven := base_le left hl (lastLevel ha)
    have hq := f.2.1 ⟨left, lastLevel ha⟩
    omega

end
end D5.S3.Combinatorics.Geometry.PathBlockGamma
