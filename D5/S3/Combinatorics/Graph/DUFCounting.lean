/- GID: D5/S3/Combinatorics/Graph/DUFCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Exact fiber counts and two incidence counts bound codegree-four triple families. -/

import D5.S3.Combinatorics.Graph.DUFWedges
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFCounting

open Finset DUFStructure DUFWedges
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of all ground pairs with the specified codegree. -/
def h (H : Finset (Finset V)) (i : ℕ) : ℕ :=
  (pairs.filter fun p => (neighbors H p).card = i).card

/-- The number of all ground pairs with the specified common-link size. -/
def q (H : Finset (Finset V)) (i : ℕ) : ℕ :=
  (pairs.filter fun p => (common H p).card = i).card

/-- The number of exact four-neighborhood fibers of size one or two. -/
def a (H : Finset (Finset V)) : ℕ :=
  ((univ.powersetCard 4).filter fun S => (fiber H S).card = 1 ∨ (fiber H S).card = 2).card

/-- The number of four-edge exact four-neighborhood fibers. -/
def b (H : Finset (Finset V)) : ℕ :=
  ((univ.powersetCard 4).filter fun S => (fiber H S).card = 4).card

/-- Counting actual fiber wedges gives the exact correction and its uniform bound. -/
theorem fiber_counts (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H) :
    q H 4 + a H = h H 4 + 2 * b H ∧ 4 * b H ≤ h H 4 ∧ 2 * q H 4 ≤ 3 * h H 4 := by
  have hh : h H 4 = ∑ S ∈ univ.powersetCard 4, (fiber H S).card := by
    symm
    have he := sum_card_fiberwise_eq_card_filter (pairs : Finset (Finset V))
      (univ.powersetCard 4) (neighbors H)
    simpa only [fiber, h, mem_powersetCard, subset_univ, true_and] using he
  have hq : q H 4 = ∑ S ∈ univ.powersetCard 4, ((fiber H S).card).choose 2 :=
    (wedge_bijection H hd hc).2
  have he : ∀ S ∈ (univ : Finset V).powersetCard 4,
      ((fiber H S).card).choose 2 +
          (if (fiber H S).card = 1 ∨ (fiber H S).card = 2 then 1 else 0) =
        (fiber H S).card + 2 * (if (fiber H S).card = 4 then 1 else 0) := by
    intro S hS
    have hb := (fiber_structure H hd hc S (mem_powersetCard.mp hS).2).1
    interval_cases hk : (fiber H S).card <;> norm_num [Nat.choose]
  have hb : ∀ S ∈ (univ : Finset V).powersetCard 4,
      4 * (if (fiber H S).card = 4 then 1 else 0) ≤ (fiber H S).card := by
    intro S _
    split_ifs with hs <;> omega
  have he' := sum_congr rfl he
  have hb' := sum_le_sum hb
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at he'
  rw [← mul_sum] at hb'
  have ha : a H = ∑ S ∈ univ.powersetCard 4,
      if (fiber H S).card = 1 ∨ (fiber H S).card = 2 then 1 else 0 := card_filter _ _
  have hb0 : b H = ∑ S ∈ univ.powersetCard 4,
      if (fiber H S).card = 4 then 1 else 0 := card_filter _ _
  rw [← hh, ← hq, ← ha, ← hb0] at he'
  rw [← hh, ← hb0] at hb'
  exact ⟨he', hb', by omega⟩

/-- The pair-triple incidence and the directed pair-pair incidence have two counts each. -/
theorem incidence_counts (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3) :
    (∑ p ∈ (pairs : Finset (Finset V)), (neighbors H p).card) = 3 * H.card ∧
    (∑ p ∈ (pairs : Finset (Finset V)), ((neighbors H p).card).choose 2) =
      ∑ q ∈ (pairs : Finset (Finset V)), (common H q).card := by
  have hN (p : Finset V) (hp : p ∈ pairs) :
      (neighbors H p).card = (H.filter fun e => p ⊆ e).card := by
    have hp2 := (mem_powersetCard.mp hp).2
    apply card_bij (fun x _ => insert x p)
    · intro x hx
      obtain ⟨hx, hH⟩ := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨hH, subset_insert x p⟩
    · intro x hx y hy he
      exact (insert_inj (mem_filter.mp hx).2.1).mp he
    · intro e he
      obtain ⟨heH, hpe⟩ := mem_filter.mp he
      have hd : (e \ p).card = 1 := by rw [card_sdiff_of_subset hpe, hu e heH, hp2]
      obtain ⟨x, hx⟩ := card_eq_one.mp hd
      have hxp : x ∉ p := (mem_sdiff.mp (hx.symm ▸ mem_singleton_self x)).2
      have heq : insert x p = e := by
        have he' := sdiff_union_of_subset hpe
        rw [hx, singleton_union] at he'
        exact he'
      exact ⟨x, mem_filter.mpr ⟨mem_univ _, hxp, heq.symm ▸ heH⟩, heq⟩
  have hP (e : Finset V) : (pairs.filter fun p => p ⊆ e) = e.powersetCard 2 := by
    ext p
    simp only [pairs, mem_filter, mem_powersetCard, subset_univ, true_and]
    tauto
  constructor
  · calc
      (∑ p ∈ pairs, (neighbors H p).card) = ∑ p ∈ pairs, (H.filter fun e => p ⊆ e).card :=
        sum_congr rfl hN
      _ = ∑ e ∈ H, (pairs.filter fun p => p ⊆ e).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := pairs) (t := H) (fun p e : Finset V => p ⊆ e)
      _ = ∑ e ∈ H, 3 := by
        apply sum_congr rfl
        intro e he
        rw [hP, card_powersetCard, hu e he]; decide
      _ = 3 * H.card := by simp [Nat.mul_comm]
  · calc
      (∑ p ∈ pairs, ((neighbors H p).card).choose 2) =
          ∑ p ∈ pairs, (pairs.filter fun q => q ⊆ neighbors H p).card := by
        apply sum_congr rfl
        intro p _
        rw [hP, card_powersetCard]
      _ = ∑ q ∈ pairs, (common H q).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := pairs) (t := pairs) (fun p q => q ⊆ neighbors H p)

/-- The codegree-four bound, together with the exact identity in terms of four-edge fibers. -/
theorem counting_bound (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
    (hd : DUF H) (hc : CapFour H) :
    21 * H.card + 10 * h H 0 + 3 * h H 1 + h H 3 ≤ 22 * (Fintype.card V).choose 2 ∧
    6 * H.card + a H + q H 2 + 2 * q H 1 + 3 * q H 0 + h H 1 + 3 * h H 0 =
      6 * (Fintype.card V).choose 2 + 2 * b H := by
  have hist (f : Finset V → ℕ) (hf : ∀ p ∈ pairs, f p ≤ 4) (g : ℕ → ℕ) :
      (∑ p ∈ pairs, g (f p)) =
        ∑ i ∈ range 5, (pairs.filter fun p => f p = i).card * g i := by
    have hm : ∀ p ∈ pairs, f p ∈ range 5 := by
      intro p hp; exact mem_range.mpr (by have := hf p hp; omega)
    simpa only [sum_const, smul_eq_mul] using (sum_fiberwise_of_maps_to' hm g).symm
  have ht : ∀ p ∈ pairs, (common H p).card ≤ 4 := by
    intro p hp
    exact (common_structure H hd hc p (mem_powersetCard.mp hp).2).1
  have hh0 := hist (fun p => (neighbors H p).card) hc (fun _ => 1)
  have hq0 := hist (fun p => (common H p).card) ht (fun _ => 1)
  have hh1 := hist (fun p => (neighbors H p).card) hc id
  have hh2 := hist (fun p => (neighbors H p).card) hc (fun i => i.choose 2)
  have hq1 := hist (fun p => (common H p).card) ht id
  have hP : (pairs : Finset (Finset V)).card = (Fintype.card V).choose 2 := by
    simp only [pairs, card_powersetCard, card_univ]
  simp only [sum_range_succ, sum_range_zero, sum_const,
    smul_eq_mul, Nat.mul_one, Nat.zero_add] at hh0
  simp only [sum_range_succ, sum_range_zero, sum_const,
    smul_eq_mul, Nat.mul_one, Nat.zero_add] at hq0
  simp only [sum_range_succ, sum_range_zero, id_eq,
    Nat.mul_zero, Nat.mul_one, Nat.zero_add] at hh1
  simp only [sum_range_succ, sum_range_zero, id_eq,
    Nat.mul_zero, Nat.mul_one, Nat.zero_add] at hq1
  simp only [sum_range_succ, sum_range_zero] at hh2
  norm_num [Nat.choose] at hh2
  obtain ⟨hi1, hi2⟩ := incidence_counts H hu
  obtain ⟨hf1, hf2, hf3⟩ := fiber_counts H hd hc
  simp only [h, q] at hf1 hf2 hf3 ⊢
  constructor <;> omega

end D5.S3.Combinatorics.Graph.DUFCounting
