/- GID: D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Original signed coordinate labels and their coefficient-one zero subsets. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-! The signed basis is kept in the original additive group throughout. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum

open scoped BigOperators
open Finset

noncomputable section

abbrev V (r : ℕ) := Fin r → ZMod 3

def basis {r : ℕ} (i : Fin r) : V r := Pi.single i 1

def label {r : ℕ} (x : Fin r × Bool) : V r :=
  if x.2 then basis x.1 else -basis x.1

private theorem label_apply {r : ℕ} (i j : Fin r) (b : Bool) :
    label (i, b) j = if j = i then (if b then 1 else -1) else 0 := by
  cases b <;> by_cases h : j = i <;> simp [label, basis, Pi.single_apply, h]

private theorem sign_ne_zero (b : Bool) : (if b then 1 else -1 : ZMod 3) ≠ 0 := by
  cases b <;> norm_num

theorem label_injective (r : ℕ) : Function.Injective (@label r) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    by_contra hn
    have hh := congrFun h i
    exact sign_ne_zero b (by simpa [label_apply, hn] using hh)
  subst j
  have hbc : b = c := by
    have hh := congrFun h i
    cases b <;> cases c
    · rfl
    · exact False.elim ((by decide : (-1 : ZMod 3) ≠ 1) (by simpa [label_apply] using hh))
    · exact False.elim ((by decide : (-1 : ZMod 3) ≠ 1) (by simpa [label_apply] using hh.symm))
    · rfl
  cases hbc
  rfl

def alphabet (r : ℕ) : Finset (V r) := univ.image label

def pairs {r : ℕ} (I : Finset (Fin r)) : Finset (V r) :=
  (I ×ˢ (univ : Finset Bool)).image label

theorem mem_pairs {r : ℕ} (I : Finset (Fin r)) (x : Fin r × Bool) :
    label x ∈ pairs I ↔ x.1 ∈ I := by
  simp only [pairs, mem_image, mem_product, mem_univ, and_true]
  constructor
  · rintro ⟨y, hy, h⟩
    simpa [label_injective r h] using hy
  · exact fun h => ⟨x, h, rfl⟩

theorem pairs_univ (r : ℕ) : pairs (univ : Finset (Fin r)) = alphabet r := by
  rw [pairs, univ_product_univ]
  rfl

theorem pairs_card {r : ℕ} (I : Finset (Fin r)) : (pairs I).card = 2 * I.card := by
  rw [pairs, card_image_of_injective _ (label_injective r), card_product]
  simp [mul_comm]

theorem alphabet_card (r : ℕ) : (alphabet r).card = 2 * r := by
  rw [← pairs_univ, pairs_card]
  simp

theorem zero_not_mem_alphabet (r : ℕ) : (0 : V r) ∉ alphabet r := by
  rintro h
  obtain ⟨⟨i,b⟩, _, h⟩ := mem_image.mp h
  have hh := congrFun h i
  exact sign_ne_zero b (by simpa [label_apply] using hh)

private theorem subset_image {r : ℕ} (S : Finset (V r)) (hS : S ⊆ alphabet r) :
    (univ.filter (fun x : Fin r × Bool => label x ∈ S)).image label = S := by
  ext a
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    obtain ⟨x, _, rfl⟩ := mem_image.mp (hS ha)
    exact ⟨x, ha, rfl⟩

theorem sum_coordinate {r : ℕ} (S : Finset (V r)) (hS : S ⊆ alphabet r) (i : Fin r) :
    (∑ x ∈ S, x) i =
      (if basis i ∈ S then 1 else 0) - (if -basis i ∈ S then 1 else 0) := by
  rw [Finset.sum_apply]
  calc
    ∑ x ∈ S, x i = ∑ x ∈ univ.filter (fun x : Fin r × Bool => label x ∈ S), label x i := by
      have he := Finset.sum_image
        (s := univ.filter (fun x : Fin r × Bool => label x ∈ S))
        (f := fun a : V r => a i) (g := label)
        (fun x _ y _ h => label_injective r h)
      rw [subset_image S hS] at he
      exact he
    _ = _ := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simp only [label_apply]
      have hz (j : Fin r) (b : Bool) :
          (if label (j,b) ∈ S then (if i = j then (if b then 1 else -1 : ZMod 3) else 0) else 0) =
          if i = j then (if label (j,b) ∈ S then (if b then 1 else -1) else 0) else 0 := by
        by_cases h : i = j <;> simp [h]
      simp_rw [hz]
      rw [Finset.sum_comm]
      by_cases hn : -basis i ∈ S <;> simp [label, sub_eq_add_neg, hn]

theorem sum_eq_zero_iff {r : ℕ} (S : Finset (V r)) (hS : S ⊆ alphabet r) :
    (∑ x ∈ S, x) = 0 ↔ ∀ i : Fin r, basis i ∈ S ↔ -basis i ∈ S := by
  constructor
  · intro h i
    have hh := congrFun h i
    rw [sum_coordinate S hS] at hh
    by_cases hp : basis i ∈ S <;> by_cases hn : -basis i ∈ S <;>
      simp_all
  · intro h
    ext i
    rw [sum_coordinate S hS]
    simp only [Pi.zero_apply]
    simp only [h i, sub_self]

theorem zero_subset_spectrum {r : ℕ} (S : Finset (V r)) (hS : S ⊆ alphabet r) :
    (∑ x ∈ S, x) = 0 ↔ ∃! I : Finset (Fin r), S = pairs I := by
  constructor
  · intro hz
    let I : Finset (Fin r) := univ.filter (fun i => basis i ∈ S)
    have hI : S = pairs I := by
      ext a
      by_cases ha : a ∈ alphabet r
      · obtain ⟨⟨i,b⟩, _, rfl⟩ := mem_image.mp ha
        rw [mem_pairs]
        cases b <;> simp only [label, Bool.false_eq_true, ↓reduceIte, I,
          mem_filter, mem_univ, true_and]
        exact (sum_eq_zero_iff S hS).mp hz i |>.symm
      · have hn : a ∉ pairs I := by
          intro h
          exact ha (by
            rw [← pairs_univ]
            obtain ⟨x,hx,rfl⟩ := mem_image.mp h
            exact mem_image.mpr ⟨x, by simp, rfl⟩)
        simp [notMem_subset hS ha, hn]
    refine ⟨I, hI, ?_⟩
    intro J hJ
    ext i
    have hh : label (i,true) ∈ pairs J ↔ label (i,true) ∈ pairs I := by
      rw [hJ.symm.trans hI]
    simpa only [mem_pairs] using hh
  · rintro ⟨I, rfl, _⟩
    apply (sum_eq_zero_iff _ hS).mpr
    intro i
    simpa [label] using (mem_pairs I (i,true)).trans (mem_pairs I (i,false)).symm

/-- Every nonempty proper contiguous interval has nonzero original-group sum. -/
def Good {G : Type*} [AddCommGroup G] (w : List G) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
    ((w.drop i).take (j-i)).sum ≠ 0

/-- The interval convention expressed by an actual decomposition of the original word. -/
theorem good_iff_decomposition {G : Type*} [AddCommGroup G] (w : List G) :
    Good w ↔ ∀ l u v : List G, w = l ++ u ++ v → u ≠ [] →
      (l ≠ [] ∨ v ≠ []) → u.sum ≠ 0 := by
  constructor
  · intro h l u v he hu hp
    subst w
    have hlen : 0 < u.length := List.length_pos_iff.mpr hu
    have hi : l.length < l.length + u.length := by omega
    have hj : l.length + u.length ≤ (l ++ u ++ v).length := by simp
    have hproper : l.length ≠ 0 ∨ l.length + u.length ≠ (l ++ u ++ v).length := by
      rcases hp with hp | hp
      · exact Or.inl (Nat.ne_of_gt (List.length_pos_iff.mpr hp))
      · right
        have hv : 0 < v.length := List.length_pos_iff.mpr hp
        simp only [List.length_append]
        omega
    have hh := h l.length (l.length + u.length) hi hj hproper
    simpa only [List.append_assoc, List.drop_left, Nat.add_sub_cancel_left,
      List.take_left] using hh
  · intro h i j hij hj hp
    have hi : i ≤ w.length := by omega
    have htake : j-i ≤ (w.drop i).length := by simp only [List.length_drop]; omega
    have hu : (w.drop i).take (j-i) ≠ [] := by
      apply List.length_pos_iff.mp
      rw [List.length_take, Nat.min_eq_left htake]
      omega
    have hproper : w.take i ≠ [] ∨ ((w.drop i).drop (j-i)) ≠ [] := by
      by_contra hn
      simp only [not_or, not_not] at hn
      have h1 := congrArg List.length hn.1
      have h2 := congrArg List.length hn.2
      simp only [List.length_take, List.length_drop, List.length_nil] at h1 h2
      have : i = 0 := by omega
      subst i
      rcases hp with hp | hp <;> omega
    apply h (w.take i) ((w.drop i).take (j-i)) ((w.drop i).drop (j-i))
      _ hu hproper
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

end
end D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
