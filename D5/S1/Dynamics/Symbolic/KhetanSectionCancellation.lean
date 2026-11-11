/- GID: D5/S1/Dynamics/Symbolic/KhetanSectionCancellation
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: General weighted-incidence cancellation and the consumed six-object grid reduction. -/

import Mathlib

/-! Weighted cancellation on simple finite incidence relations.

The objects and both key types are arbitrary; they need not be finite types.
The common-degree cancellation theorem applies to every positive natural degree
and every complex weight assignment. Summing by rows and by columns forces the
column total to vanish; an occupied row missing exactly one occupied column then
forces that column's weight to vanish.

The six-object reduction and completeness proof below are symbolic finite-set
arguments consumed by the actual lattice geometry. They use degree inequalities
and injectivity, not exhaustive incidence tables, certified finite instances,
checkers or numerical reductions. Thus the computational utility is `none`.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanSectionCancellation

open scoped BigOperators

/-! General occupied-incidence counting. The finite set consists of actual
objects; injectivity of the two keys is the simplicity condition. -/

private lemma fiber_card_le_other
    {A R C : Type*} [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (s : Finset A) (r : A → R) (c : A → C)
    (hinj : Function.Injective fun x => (r x, c x)) (i : R) :
    (s.filter fun x => r x = i).card ≤ (s.image c).card := by
  have hi : Set.InjOn c (s.filter fun x => r x = i) := by
    intro x hx y hy heq
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq
  rw [← Finset.card_image_of_injOn hi]
  apply Finset.card_le_card
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem occupied_key_bounds
    {A R C : Type*} [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (s : Finset A) (r : A → R) (c : A → C)
    (hinj : Function.Injective fun x => (r x, c x))
    (hcard : s.card = 6)
    (hr : ∀ i ∈ s.image r, 2 ≤ (s.filter fun x => r x = i).card)
    (hc : ∀ j ∈ s.image c, 2 ≤ (s.filter fun x => c x = j).card) :
    2 ≤ (s.image r).card ∧ (s.image r).card ≤ 3 := by
  have hsum := Finset.card_eq_sum_card_image r s
  have hsumle : 2 * (s.image r).card ≤
      ∑ i ∈ s.image r, (s.filter fun x => r x = i).card := by
    calc
      _ = ∑ _i ∈ s.image r, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hr
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hswap : Function.Injective fun x => (c x, r x) := by
    intro x y hxy
    exact hinj (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
  have hlo := (hc (c x) (Finset.mem_image_of_mem c hx)).trans
    (fiber_card_le_other s c r hswap (c x))
  exact ⟨hlo, by omega⟩

private lemma degree_two_of_three
    {A R : Type*} [DecidableEq A] [DecidableEq R]
    (s : Finset A) (r : A → R) (hs : s.card = 6)
    (hR : (s.image r).card = 3)
    (hmin : ∀ i ∈ s.image r, 2 ≤ (s.filter fun x => r x = i).card) :
    ∀ i ∈ s.image r, (s.filter fun x => r x = i).card = 2 := by
  intro i hi
  have hrest : 2 * ((s.image r).erase i).card ≤
      ∑ j ∈ (s.image r).erase i, (s.filter fun x => r x = j).card := by
    calc
      _ = ∑ _j ∈ (s.image r).erase i, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j hj => hmin j (Finset.mem_of_mem_erase hj)
  have he := Finset.sum_erase_add (s.image r)
    (fun j => (s.filter fun x => r x = j).card) hi
  have ht := Finset.card_eq_sum_card_image r s
  have hecard := Finset.card_erase_of_mem hi
  have hlow := hmin i hi
  omega

/-- In a simple finite incidence relation of constant positive column degree,
vanishing row sums force the weight of any column uniquely omitted by a row
to vanish. The point and key types, the number of objects and the common degree
are arbitrary. No nonvanishing hypothesis on the weights is needed. -/
theorem missing_column_weight_eq_zero
    {A R C : Type*} [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (s : Finset A) (r : A → R) (c : A → C)
    (hinj : Function.Injective fun x => (r x, c x))
    (d : ℕ) (hd : 0 < d)
    (hcol : ∀ j ∈ s.image c, (s.filter fun x => c x = j).card = d)
    (w : C → ℂ)
    (hcancel : ∀ i ∈ s.image r,
      (s.filter fun x => r x = i).sum (fun x => w (c x)) = 0)
    (i : R) (hi : i ∈ s.image r) (j : C)
    (hmissing : (s.image c) \ ((s.filter fun x => r x = i).image c) = {j}) :
    w j = 0 := by
  have htotal : s.sum (fun x => w (c x)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem r hx)]
    exact Finset.sum_eq_zero hcancel
  have htotal' : s.sum (fun x => w (c x)) = (d : ℂ) * (s.image c).sum w := by
    rw [← Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image_of_mem c hx)]
    calc
      _ = ∑ j ∈ s.image c, (d : ℂ) * w j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [hcol j hj, nsmul_eq_mul]
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcols : (s.image c).sum w = 0 := by
    rw [htotal'] at htotal
    exact (mul_eq_zero.mp htotal).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  have hJsub : (s.filter fun x => r x = i).image c ⊆ s.image c :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hJinj : Set.InjOn c (s.filter fun x => r x = i) := by
    intro x hx y hy heq
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq
  have hJsum : ((s.filter fun x => r x = i).image c).sum w = 0 := by
    rw [Finset.sum_image hJinj]
    exact hcancel i hi
  have hsd := Finset.sum_sdiff hJsub (f := w)
  rw [hmissing, Finset.sum_singleton, hcols, hJsum] at hsd
  simpa using hsd

theorem nonzero_weight_incidence
    {A R C : Type*} [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (s : Finset A) (r : A → R) (c : A → C)
    (hinj : Function.Injective fun x => (r x, c x))
    (hs : s.card = 6)
    (hr : ∀ i ∈ s.image r, 2 ≤ (s.filter fun x => r x = i).card)
    (hc : ∀ j ∈ s.image c, 2 ≤ (s.filter fun x => c x = j).card)
    (w : C → ℂ) (hw : ∀ j ∈ s.image c, w j ≠ 0)
    (hcancel : ∀ i ∈ s.image r,
      (s.filter fun x => r x = i).sum (fun x => w (c x)) = 0) :
    (s.image r).card = 2 ∨ (s.image c).card = 2 := by
  have hswap : Function.Injective fun x => (c x, r x) := by
    intro x y hxy
    exact hinj (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
  have hbR := occupied_key_bounds s r c hinj hs hr hc
  have hbC := occupied_key_bounds s c r hswap hs hc hr
  by_contra h
  have hR : (s.image r).card = 3 := by omega
  have hC : (s.image c).card = 3 := by omega
  have hrow := degree_two_of_three s r hs hR hr
  have hcol := degree_two_of_three s c hs hC hc
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let row := s.filter fun x => r x = r p
  let J := row.image c
  have hpR : r p ∈ s.image r := Finset.mem_image_of_mem r hp
  have hJsub : J ⊆ s.image c :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hJinj : Set.InjOn c row := by
    intro x hx y hy heq
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq
  have hJcard : J.card = 2 := by
    rw [Finset.card_image_of_injOn hJinj]
    exact hrow (r p) hpR
  have hdiff : ((s.image c) \ J).card = 1 := by
    rw [Finset.card_sdiff_of_subset hJsub, hC, hJcard]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hdiff
  have hmissing : w j = 0 :=
    missing_column_weight_eq_zero s r c hinj 2 (by omega) hcol w hcancel
      (r p) hpR j hj
  have hjC : j ∈ s.image c := by
    exact (Finset.mem_sdiff.mp (by rw [hj]; simp)).1
  exact hw j hjC hmissing

theorem complete_incidence_of_two
    {A R C : Type*} [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (s : Finset A) (r : A → R) (c : A → C)
    (hinj : Function.Injective fun x => (r x, c x))
    (hs : s.card = 6) (hR : (s.image r).card = 2)
    (hC : (s.image c).card ≤ 3) :
    (s.image c).card = 3 ∧
      ∀ i ∈ s.image r, ∀ j ∈ s.image c, ∃ p ∈ s, r p = i ∧ c p = j := by
  let key := fun x => (r x, c x)
  have hsub : s.image key ⊆ (s.image r).product (s.image c) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem r hx, Finset.mem_image_of_mem c hx⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective s hinj, Finset.product_eq_sprod,
    Finset.card_product, hs, hR] at hle
  have hc3 : (s.image c).card = 3 := by omega
  have hkey : (s.image key).card = 6 := by
    simpa only [key, hs] using Finset.card_image_of_injective s hinj
  have heq : s.image key = (s.image r).product (s.image c) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [Finset.card_product, hR, hc3, hkey]
  refine ⟨hc3, ?_⟩
  intro i hi j hj
  have : (i, j) ∈ s.image key := by rw [heq]; exact Finset.mem_product.mpr ⟨hi, hj⟩
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp this
  exact ⟨p, hp, congrArg Prod.fst he, congrArg Prod.snd he⟩

end D5.S1.Dynamics.Symbolic.KhetanSectionCancellation
