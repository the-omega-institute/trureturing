/- GID: D5/S3/Combinatorics/Kozlov/ProperModel
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:literal-equal-shift-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.SetFamily.Shadow]
   utility: none
   digest: Proper downsets and their literal equal-shift f-vector sums. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Finset
open scoped BigOperators FinsetFamily

namespace D5.S3.Combinatorics.Kozlov

abbrev Family (n : ℕ) := Finset (Finset (Fin n))
abbrev FVector (n : ℕ) := Fin (n + 1) → ℕ

structure IsComplex {n : ℕ} (D : Family n) : Prop where
  down : ∀ ⦃s t : Finset (Fin n)⦄, s ∈ D → t ⊆ s → t ∈ D
  empty_mem : ∅ ∈ D
  singleton_mem : ∀ i : Fin n, {i} ∈ D

def fEntry {n : ℕ} (D : Family n) (k : ℕ) : ℕ :=
  #(D.filter fun s => #s = k)

def fVector {n : ℕ} (D : Family n) : FVector n := fun j => fEntry D j

def SnF (n : ℕ) : Set (FVector n) := fVector '' {D | IsComplex D}

/-- Tuples use indexed sums, so a vector may occur several times. -/
def sumTuple {n r : ℕ} (s : Fin r → FVector n) : FVector n := fun j => ∑ i, s i j

def properSumset (n r : ℕ) : Set (FVector n) :=
  sumTuple '' {s : Fin r → FVector n | ∀ i, s i ∈ SnF n}

def extend {n : ℕ} (f : FVector n) (k : ℕ) : ℕ :=
  if hk : k < n + 1 then f ⟨k, hk⟩ else 0

theorem extend_sumTuple {n r : ℕ} (s : Fin r → FVector n) (k : ℕ) :
    extend (sumTuple s) k = ∑ i, extend (s i) k := by
  by_cases hk : k < n + 1 <;> simp [extend, sumTuple, hk]

/-- Largest occupied cardinality, with the void-family sentinel. -/
def top {n : ℕ} (s : FVector n) : ℤ :=
  if h : (univ.filter fun j : Fin (n + 1) => 0 < s j).Nonempty
  then ((univ.filter fun j : Fin (n + 1) => 0 < s j).max' h).val
  else -1

/-- First cardinality with a missing face, with the full-simplex sentinel. -/
def indeg {n : ℕ} (s : FVector n) : ℕ :=
  if h : (univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).Nonempty
  then ((univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).min' h).val
  else n + 1

def Chained {n r : ℕ} (s : Fin r → FVector n) : Prop :=
  ∀ ⦃i j : Fin r⦄, i.val + 1 = j.val → top (s i) < (indeg (s j) : ℤ)

theorem top_le {n : ℕ} (s : FVector n) : top s ≤ (n : ℤ) := by
  unfold top
  split
  · rename_i h
    have := ((univ.filter fun j : Fin (n + 1) => 0 < s j).max' h).isLt
    omega
  · omega

theorem top_lt_of_vanish {n k : ℕ} {s : FVector n}
    (h : ∀ j : Fin (n + 1), k ≤ j.val → s j = 0) : top s < (k : ℤ) := by
  unfold top
  split
  · rename_i hs
    let j := (univ.filter fun j : Fin (n + 1) => 0 < s j).max' hs
    have hj := (mem_filter.mp (max'_mem _ hs)).2
    change 0 < s j at hj
    change (j.val : ℤ) < k
    by_contra hn
    have := h j (by omega)
    omega
  · omega

theorem indeg_eq_sentinel_or_missing {n : ℕ} (s : FVector n) :
    indeg s = n + 1 ∨ ∃ k : Fin (n + 1), k.val = indeg s ∧ s k < n.choose k.val := by
  unfold indeg
  split
  · rename_i h
    exact Or.inr ⟨_, rfl, (mem_filter.mp (min'_mem _ h)).2⟩
  · exact Or.inl rfl

def layer (n k : ℕ) : Family n := powersetCard k univ

@[simp] theorem mem_layer {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ layer n k ↔ #s = k := by
  simp [layer]

@[simp] theorem card_layer (n k : ℕ) : #(layer n k) = n.choose k := by
  simp [layer, card_powersetCard]

def missing {n : ℕ} (D : Family n) (k : ℕ) : Family n :=
  layer n k \ D

theorem fEntry_add_card_missing {n : ℕ} (D : Family n) (k : ℕ) :
    fEntry D k + #(missing D k) = n.choose k := by
  have hf : D.filter (fun s => #s = k) = layer n k ∩ D := by
    ext s
    simp [and_comm]
  rw [fEntry, hf, missing, add_comm, card_sdiff_add_card_inter, card_layer]

theorem missing_upShadow_subset {n k : ℕ} {D : Family n} (hD : IsComplex D) :
    ∂⁺ (missing D k) ⊆ missing D (k + 1) := by
  intro t ht
  obtain ⟨s, hs, hst, hc⟩ := mem_upShadow_iff_exists_mem_card_add_one.mp ht
  obtain ⟨hsk, hsD⟩ := mem_sdiff.mp hs
  exact mem_sdiff.mpr ⟨by simpa [mem_layer.mp hsk] using hc,
    fun htD => hsD (hD.down htD hst)⟩

theorem missing_zero {n : ℕ} {D : Family n} (hD : IsComplex D) : missing D 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsk, hsD⟩ := mem_sdiff.mp hs
  rw [card_eq_zero.mp (mem_layer.mp hsk)] at hsD
  exact hsD hD.empty_mem

theorem missing_one {n : ℕ} {D : Family n} (hD : IsComplex D) : missing D 1 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsk, hsD⟩ := mem_sdiff.mp hs
  obtain ⟨i, rfl⟩ := card_eq_one.mp (mem_layer.mp hsk)
  exact hsD (hD.singleton_mem i)

/-- Delete the prescribed missing faces from the family of all subsets. -/
def fromMissing {n : ℕ} (M : ℕ → Family n) : Family n :=
  univ.filter fun s => s ∉ M #s

private theorem upward_of_upShadow {n : ℕ} {M : ℕ → Family n}
    (hM : ∀ k, ∂⁺ (M k) ⊆ M (k + 1)) {s t : Finset (Fin n)}
    (hst : s ⊆ t) (hs : s ∈ M #s) : t ∈ M #t := by
  have hiter (k d : ℕ) : (upShadow^[d]) (M k) ⊆ M (k + d) := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Function.iterate_succ_apply']
      exact (upShadow_monotone ih).trans (hM (k + d))
  have hc : #s + (#t - #s) = #t := Nat.add_sub_of_le (card_le_card hst)
  have ht := hiter #s (#t - #s) (mem_upShadow_iff_exists_mem_card_add.mpr ⟨s, hs, hst, hc⟩)
  rwa [hc] at ht

theorem fromMissing_isComplex {n : ℕ} {M : ℕ → Family n}
    (hM : ∀ k, ∂⁺ (M k) ⊆ M (k + 1)) (h0 : M 0 = ∅) (h1 : M 1 = ∅) :
    IsComplex (fromMissing M) where
  down := by
    intro t s ht hst
    simp only [fromMissing, mem_filter, mem_univ, true_and] at ht ⊢
    exact fun hs => ht (upward_of_upShadow hM hst hs)
  empty_mem := by simp [fromMissing, h0]
  singleton_mem i := by simp [fromMissing, h1]

theorem missing_fromMissing {n : ℕ} {M : ℕ → Family n}
    {k : ℕ} (hM : M k ⊆ layer n k) : missing (fromMissing M) k = M k := by
  classical
  ext s
  simp only [missing, mem_sdiff, fromMissing, mem_filter, mem_univ, true_and, not_not]
  constructor
  · rintro ⟨hs, hm⟩
    rwa [← mem_layer.mp hs]
  · intro hs
    have hk := hM hs
    exact ⟨hk, by rwa [mem_layer.mp hk]⟩

end D5.S3.Combinatorics.Kozlov
