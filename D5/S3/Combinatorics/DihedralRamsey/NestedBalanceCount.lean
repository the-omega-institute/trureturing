/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedBalanceCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedBalanceCount
   mirror-E: none(waiver:full-matching-colour-count)
   anchors: []
   utility: none
   digest: Reflection incidence sums count twice the edges in the endpoint-sum class. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedBalanceDegree
import D5.S3.Combinatorics.DihedralRamsey.NestedCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedBalanceCount

open Finset
open scoped BigOperators

/-- Each edge of an odd reflection contributes its two endpoints to the colour sum. -/
theorem reflection_class_indicator_sum {a : ℕ} (ha : 0 < a) (hae : a % 2 = 0)
    (G : SimpleGraph (Fin a)) [DecidableRel G.Adj] (c : Fin a) (hc : c.val % 2 = 1) :
    (∑ i : Fin a, if G.Adj i (c - i) then 1 else 0) =
      2 * (univ.filter fun e : Fin a × Fin a =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card := by
  classical
  letI : NeZero a := ⟨by omega⟩
  let f : Fin a → Fin a := fun i => c - i
  have hf : Function.Involutive f := by
    intro i
    dsimp [f]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hsum : ∀ i : Fin a, i + f i = c := by intro i; dsimp [f]; simp
  have hne : ∀ i : Fin a, f i ≠ i := by
    intro i hi
    have he := hsum i
    rw [hi] at he
    have hev := congrArg Fin.val he
    simp only [Fin.val_add] at hev
    have hh := congrArg (fun x : ℕ => x % 2) hev
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hae)] at hh
    omega
  let A : Finset (Fin a) := univ.filter fun i => i < f i ∧ G.Adj i (f i)
  let B : Finset (Fin a) := univ.filter fun i => f i < i ∧ G.Adj i (f i)
  let R : Finset (Fin a) := univ.filter fun i => G.Adj i (f i)
  have hAB : R = A ∪ B := by
    ext i
    simp only [R, A, B, mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro hi
      rcases lt_or_gt_of_ne (hne i).symm with h | h
      · exact Or.inl ⟨h, hi⟩
      · exact Or.inr ⟨h, hi⟩
    · rintro (⟨_, hi⟩ | ⟨_, hi⟩) <;> exact hi
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro i hi hj
    exact lt_asymm (mem_filter.mp hi).2.1 (mem_filter.mp hj).2.1
  have himage : A.image f = B := by
    ext i
    simp only [mem_image, A, B, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, ⟨hj, he⟩, rfl⟩
      exact ⟨by rw [hf j]; exact hj, by rw [hf j]; exact he.symm⟩
    · rintro ⟨hi, he⟩
      exact ⟨f i, ⟨by rw [hf i]; exact hi,
        by rw [hf i]; exact he.symm⟩, hf i⟩
  have hcard : R.card = 2 * A.card := by
    rw [hAB, card_union_of_disjoint hdisj, ← himage, card_image_of_injective _ hf.injective]
    omega
  let P : Finset (Fin a × Fin a) := univ.filter fun e =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val
  have hP : A.image (fun i => (i, f i)) = P := by
    ext e
    simp only [mem_image, A, P, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨hi, he⟩, rfl⟩
      exact ⟨hi, he, congrArg Fin.val (hsum i)⟩
    · rintro ⟨hi, he, hs⟩
      have hsum' : e.1 + e.2 = c := Fin.ext hs
      have hpartner : f e.1 = e.2 := by
        dsimp [f]
        rw [← hsum']
        simp
      refine ⟨e.1, ?_, ?_⟩
      · rw [hpartner]
        exact ⟨hi, he⟩
      · simp only [hpartner]
  have hPcard : P.card = A.card := by
    rw [← hP, card_image_of_injective]
    intro i j hij
    exact congrArg Prod.fst hij
  rw [sum_boole]
  change R.card = 2 * P.card
  rw [hcard, hPcard]

/-- A full odd rank reflection on an even vertex set contains half as many edges. -/
theorem full_reflection_class_card {k : ℕ} (hk : 0 < k)
    (c : Fin (2 * k)) (hc : c.val % 2 = 1) :
    (univ.filter fun e : Fin (2 * k) × Fin (2 * k) =>
      e.1 < e.2 ∧ (e.1.val + e.2.val) % (2 * k) = c.val).card = k := by
  classical
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hne : ∀ i : Fin (2 * k), i ≠ c - i := by
    intro i hi
    have he : i + i = c := by
      calc i + i = i + (c - i) := congrArg (fun x => i + x) hi
           _ = c := by simp
    have hev := congrArg Fin.val he
    simp only [Fin.val_add] at hev
    have hh := congrArg (fun x : ℕ => x % 2) hev
    rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 * k from dvd_mul_right 2 k)] at hh
    omega
  have hh := reflection_class_indicator_sum (by omega : 0 < 2 * k) (by omega)
    (⊤ : SimpleGraph (Fin (2 * k))) c hc
  have hsum : (∑ i : Fin (2 * k),
      if (⊤ : SimpleGraph (Fin (2 * k))).Adj i (c - i) then 1 else 0) = 2 * k := by
    have he : ∀ i : Fin (2 * k),
        (if (⊤ : SimpleGraph (Fin (2 * k))).Adj i (c - i) then 1 else 0) = 1 := by
      intro i
      simp [hne i]
    simp only [he, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [hsum] at hh
  simp only [SimpleGraph.top_adj] at hh
  have hp : (univ.filter fun e : Fin (2 * k) × Fin (2 * k) =>
      e.1 < e.2 ∧ e.1 ≠ e.2 ∧ (e.1.val + e.2.val) % (2 * k) = c.val) =
      univ.filter fun e : Fin (2 * k) × Fin (2 * k) =>
        e.1 < e.2 ∧ (e.1.val + e.2.val) % (2 * k) = c.val := by
    ext e
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ne_of_lt h.1, h.2⟩⟩
  rw [hp] at hh
  omega

end D5.S3.Combinatorics.DihedralRamsey.NestedBalanceCount
