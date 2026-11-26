/- GID: D5/S3/Arith/Lattices/HilbertSmith/NestedResidueMatching
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/HilbertSmith/NestedResidueMatching
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Nested matching attains the exact reflected residue loss at every prime-power level. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.NormNum

/-! # Simultaneous minimization in nested residue classes -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching

open Finset
open scoped BigOperators

section Matching

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- A partial matching of the two finite sets, encoded by its edges. -/
def IsMatching (A : Finset α) (B : Finset β) (M : Finset (α × β)) : Prop :=
  M ⊆ A ×ˢ B ∧
    Set.InjOn Prod.fst (↑M : Set (α × β)) ∧
    Set.InjOn Prod.snd (↑M : Set (α × β))

private theorem IsMatching.mono {A : Finset α} {B : Finset β}
    {P M : Finset (α × β)} (hM : IsMatching A B M) (hP : P ⊆ M) :
    IsMatching A B P :=
  ⟨hP.trans hM.1, hM.2.1.mono (coe_subset.mpr hP), hM.2.2.mono (coe_subset.mpr hP)⟩

private theorem injOn_insert_of_notMem_image {δ : Type*} [DecidableEq δ]
    {M : Finset (α × β)} {f : α × β → δ} {z : α × β}
    (hi : Set.InjOn f (↑M : Set (α × β))) (hz : f z ∉ M.image f) :
    Set.InjOn f (↑(insert z M) : Set (α × β)) := by
  intro x hx y hy hxy
  rcases mem_insert.mp (mem_coe.mp hx) with rfl | hxM
  · rcases mem_insert.mp (mem_coe.mp hy) with rfl | hyM
    · rfl
    · exact (hz (mem_image.mpr ⟨y, hyM, hxy.symm⟩)).elim
  · rcases mem_insert.mp (mem_coe.mp hy) with rfl | hyM
    · exact (hz (mem_image.mpr ⟨x, hxM, hxy⟩)).elim
    · exact hi (mem_coe.mpr hxM) (mem_coe.mpr hyM) hxy

/-- Extend a matching through the admissible edges until no compatible unused
endpoints remain. A maximum-cardinality extension implements finite saturation. -/
private theorem exists_saturated_extension {A : Finset α} {B : Finset β}
    (R : α × β → Prop) {P : Finset (α × β)} (hP : IsMatching A B P)
    (hR : ∀ z ∈ P, R z) :
    ∃ M : Finset (α × β), P ⊆ M ∧ IsMatching A B M ∧
      (∀ z ∈ M, R z) ∧
      ∀ x ∈ A, ∀ y ∈ B, R (x, y) → x ∈ M.image Prod.fst ∨ y ∈ M.image Prod.snd := by
  classical
  let candidates := (A ×ˢ B).powerset.filter fun M =>
    P ⊆ M ∧ IsMatching A B M ∧ ∀ z ∈ M, R z
  have hmem (M : Finset (α × β)) :
      M ∈ candidates ↔ P ⊆ M ∧ IsMatching A B M ∧ ∀ z ∈ M, R z := by
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨And.right, fun h => ⟨h.2.1.1, h⟩⟩
  obtain ⟨M, hMc, hmax⟩ :=
    candidates.exists_max_image Finset.card ⟨P, (hmem P).2 ⟨Subset.rfl, hP, hR⟩⟩
  obtain ⟨hPM, hM, hMR⟩ := (hmem M).1 hMc
  refine ⟨M, hPM, hM, hMR, ?_⟩
  intro x hx y hy hr
  by_contra! h
  have hnew : (x, y) ∉ M := fun hm => h.1 (mem_image_of_mem Prod.fst hm)
  have hM' : IsMatching A B (insert (x, y) M) := by
    refine ⟨?_, injOn_insert_of_notMem_image hM.2.1 h.1,
      injOn_insert_of_notMem_image hM.2.2 h.2⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_product.mpr ⟨hx, hy⟩
    · exact hM.1 hz
  have hin : insert (x, y) M ∈ candidates := by
    refine (hmem _).2 ⟨fun z hz => mem_insert_of_mem (hPM hz), hM', ?_⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hr
    · exact hMR z hz
  have hc := hmax _ hin
  rw [card_insert_of_notMem hnew] at hc
  omega

/-- Process nested relations in order from the finest to the coarsest. -/
private theorem exists_saturated_chain (A : Finset α) (B : Finset β)
    (R : ℕ → α × β → Prop) (hR : ∀ j z, R j z → R (j + 1) z) (e : ℕ) :
    ∃ M : ℕ → Finset (α × β), Monotone M ∧
      ∀ j ≤ e, IsMatching A B (M j) ∧
        (∀ z ∈ M j, R j z) ∧
        ∀ x ∈ A, ∀ y ∈ B, R j (x, y) →
          x ∈ (M j).image Prod.fst ∨ y ∈ (M j).image Prod.snd := by
  classical
  induction e with
  | zero =>
    have hempty : IsMatching A B (∅ : Finset (α × β)) := by
      simp [IsMatching, Set.InjOn]
    obtain ⟨P, _, hP⟩ := exists_saturated_extension (R 0) hempty (by simp)
    exact ⟨fun _ => P, fun _ _ _ => Subset.rfl, fun j hj => by
      have : j = 0 := by omega
      subst j
      exact hP⟩
  | succ e ih =>
    obtain ⟨M, hmono, hM⟩ := ih
    obtain ⟨hMe, hMeR, _⟩ := hM e le_rfl
    obtain ⟨P, hsub, hP⟩ := exists_saturated_extension (R (e + 1)) hMe
      (fun z hz => hR e z (hMeR z hz))
    refine ⟨fun j => if j ≤ e then M j else P, ?_, ?_⟩
    · intro i j hij
      by_cases hj : j ≤ e
      · simpa only [ite_eq_left hj, ite_eq_left (hij.trans hj)] using hmono hij
      · by_cases hi : i ≤ e
        · simpa only [ite_eq_left hi, ite_eq_right hj] using (hmono hi).trans hsub
        · simp [hi, hj]
    · intro j hj
      by_cases hje : j ≤ e
      · simpa only [ite_eq_left hje] using hM j hje
      · have : j = e + 1 := by omega
        subst j
        simpa using hP

/-- A single set of the desired size can be chosen comparable with each member
of the chain. It is the prefix obtained by adding earlier matching edges first. -/
private theorem exists_comparable_subset {δ : Type*} [DecidableEq δ]
    (M : ℕ → Finset δ) (hM : Monotone M) (k : ℕ) :
    ∀ e, k ≤ (M e).card →
      ∃ S : Finset δ, S ⊆ M e ∧ S.card = k ∧
        ∀ j ≤ e, S ⊆ M j ∨ M j ⊆ S := by
  intro e
  induction e with
  | zero =>
    intro hk
    obtain ⟨S, hS, hSk⟩ := exists_subset_card_eq hk
    exact ⟨S, hS, hSk, fun j hj => Or.inl (by simpa [Nat.eq_zero_of_le_zero hj] using hS)⟩
  | succ e ih =>
    intro hk
    have hsub : M e ⊆ M (e + 1) := hM (Nat.le_succ e)
    by_cases he : k ≤ (M e).card
    · obtain ⟨S, hS, hSk, hcomp⟩ := ih he
      refine ⟨S, hS.trans hsub, hSk, ?_⟩
      intro j hj
      by_cases hje : j ≤ e
      · exact hcomp j hje
      · have : j = e + 1 := by omega
        subst j
        exact Or.inl (hS.trans hsub)
    · obtain ⟨S, hES, hS, hSk⟩ :=
        exists_subsuperset_card_eq hsub (show (M e).card ≤ k by omega) hk
      refine ⟨S, hS, hSk, ?_⟩
      intro j hj
      by_cases hje : j ≤ e
      · exact Or.inr ((hM hje).trans hES)
      · have : j = e + 1 := by omega
        subst j
        exact Or.inl hS

/-- The number of elements of a finite set carrying the label c. -/
def fiber (A : Finset α) (f : α → γ) (c : γ) : ℕ := (A.filter (fun x => f x = c)).card

private theorem fiber_mono {I A : Finset α} (h : I ⊆ A) (f : α → γ) (c : γ) :
    fiber I f c ≤ fiber A f c :=
  card_mono (filter_subset_filter _ h)

private theorem sum_fiber {I : Finset α} {t : Finset γ} {f : α → γ}
    (hf : ∀ x ∈ I, f x ∈ t) : ∑ c ∈ t, fiber I f c = I.card := by
  exact (card_eq_sum_card_fiberwise (fun x hx => hf x hx)).symm

private theorem image_fiber_card {δ : Type*} [DecidableEq δ]
    {M : Finset (α × β)} {h : α × β → δ} (hi : Set.InjOn h (↑M : Set (α × β)))
    (f : δ → γ) (c : γ) :
    fiber (M.image h) f c = (M.filter (fun z => f (h z) = c)).card := by
  have he : (M.image h).filter (fun x => f x = c) =
      (M.filter (fun z => f (h z) = c)).image h := by
    ext x
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hc⟩
      exact ⟨z, ⟨hz, hc⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hc⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hc⟩
  unfold fiber
  rw [he, card_image_of_injOn (hi.mono (coe_subset.mpr (filter_subset _ _)))]

private theorem matched_fibers {A : Finset α} {B : Finset β} {M : Finset (α × β)}
    (hM : IsMatching A B M) {f : α → γ} {g : β → γ}
    (hfg : ∀ z ∈ M, f z.1 = g z.2) (c : γ) :
    fiber (M.image Prod.fst) f c = fiber (M.image Prod.snd) g c := by
  rw [image_fiber_card hM.2.1, image_fiber_card hM.2.2]
  congr 1
  ext z
  simp only [mem_filter]
  constructor <;> rintro ⟨hz, hc⟩
  · exact ⟨hz, (hfg z hz).symm.trans hc⟩
  · exact ⟨hz, (hfg z hz).trans hc⟩

private theorem matching_images_subset {A : Finset α} {B : Finset β}
    {M : Finset (α × β)} (hM : IsMatching A B M) :
    M.image Prod.fst ⊆ A ∧ M.image Prod.snd ⊆ B := by
  constructor
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (hM.1 hz)).1
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    exact (mem_product.mp (hM.1 hz)).2

private theorem saturated_fibers {A : Finset α} {B : Finset β} {M : Finset (α × β)}
    (hM : IsMatching A B M) {f : α → γ} {g : β → γ}
    (hfg : ∀ z ∈ M, f z.1 = g z.2)
    (hsat : ∀ x ∈ A, ∀ y ∈ B, f x = g y →
       x ∈ M.image Prod.fst ∨ y ∈ M.image Prod.snd) (c : γ) :
    fiber (M.image Prod.fst) f c = min (fiber A f c) (fiber B g c) := by
  have he := matched_fibers hM hfg c
  obtain ⟨hA, hB⟩ := matching_images_subset hM
  apply le_antisymm
  · exact le_min (fiber_mono hA f c) (he.trans_le (fiber_mono hB g c))
  · by_contra! h
    have hleft := h.trans_le (min_le_left _ _)
    have hright := h.trans_le (min_le_right _ _)
    rw [he] at hright
    obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_of_card_lt_card hleft
    obtain ⟨y, hy, hy'⟩ := exists_mem_notMem_of_card_lt_card hright
    obtain ⟨hxA, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyB, hyc⟩ := mem_filter.mp hy
    rcases hsat x hxA y hyB (hxc.trans hyc.symm) with hxM | hyM
    · exact hx' (mem_filter.mpr ⟨hxM, hxc⟩)
    · exact hy' (mem_filter.mpr ⟨hyM, hyc⟩)

/-- The unsigned difference between two natural counts. -/
def gap (u v : ℕ) : ℕ := (u - v) + (v - u)

private theorem gap_add_min (u v : ℕ) : gap u v + 2 * min u v = u + v := by
  unfold gap
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right h]
    omega

private theorem gap_le_square (a : ℕ) : a ≤ a ^ 2 := by
  cases a with
  | zero => simp
  | succ a =>
    simpa only [pow_two, mul_one] using
      (Nat.mul_le_mul_left (a + 1) (show 1 ≤ a + 1 by omega))

/-- Twice the residue loss, represented over naturals. -/
def loss (t : Finset γ) (I : Finset α) (J : Finset β) (f : α → γ) (g : β → γ) : ℕ :=
  ∑ c ∈ t, gap (fiber I f c) (fiber J g c) ^ 2

/-- Capacity equals the sum of the common populations of the full fibers. -/
def capacity (t : Finset γ) (A : Finset α) (B : Finset β) (f : α → γ) (g : β → γ) : ℕ :=
  ∑ c ∈ t, min (fiber A f c) (fiber B g c)

private theorem sum_gap {t : Finset γ} {I : Finset α} {J : Finset β}
    {f : α → γ} {g : β → γ}
    (hf : ∀ x ∈ I, f x ∈ t) (hg : ∀ y ∈ J, g y ∈ t) :
    (∑ c ∈ t, gap (fiber I f c) (fiber J g c)) + 2 * capacity t I J f g =
      I.card + J.card := by
  unfold capacity
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← sum_fiber hf, ← sum_fiber hg, ← Finset.sum_add_distrib]
  exact sum_congr rfl (fun c _ => gap_add_min _ _)

private theorem loss_lower {t : Finset γ} {A I : Finset α} {B J : Finset β}
    {f : α → γ} {g : β → γ} (hI : I ⊆ A) (hJ : J ⊆ B)
    (hf : ∀ x ∈ A, f x ∈ t) (hg : ∀ y ∈ B, g y ∈ t)
    {k : ℕ} (hIk : I.card = k) (hJk : J.card = k) :
    2 * (k - capacity t A B f g) ≤ loss t I J f g := by
  have hs := sum_gap (fun x hx => hf x (hI hx)) (fun y hy => hg y (hJ hy))
  rw [hIk, hJk] at hs
  have hc : capacity t I J f g ≤ capacity t A B f g :=
    sum_le_sum (fun c _ => min_le_min (fiber_mono hI f c) (fiber_mono hJ g c))
  have hl : (∑ c ∈ t, gap (fiber I f c) (fiber J g c)) ≤ loss t I J f g :=
    sum_le_sum (fun c _ => gap_le_square _)
  omega

private theorem saturated_card {t : Finset γ} {A : Finset α} {B : Finset β}
    {M : Finset (α × β)} (hM : IsMatching A B M) {f : α → γ} {g : β → γ}
    (hf : ∀ x ∈ A, f x ∈ t) (hfg : ∀ z ∈ M, f z.1 = g z.2)
    (hsat : ∀ x ∈ A, ∀ y ∈ B, f x = g y →
      x ∈ M.image Prod.fst ∨ y ∈ M.image Prod.snd) :
    M.card = capacity t A B f g := by
  rw [← card_image_of_injOn hM.2.1,
    ← sum_fiber (fun x hx => hf x ((matching_images_subset hM).1 hx))]
  exact sum_congr rfl (fun c _ => saturated_fibers hM hfg hsat c)

private theorem loss_eq_of_comparable {t : Finset γ} {A : Finset α} {B : Finset β}
    {M S : Finset (α × β)} (hM : IsMatching A B M) (hS : IsMatching A B S)
    {f : α → γ} {g : β → γ} (hf : ∀ x ∈ A, f x ∈ t) (hg : ∀ y ∈ B, g y ∈ t)
    (hfg : ∀ z ∈ M, f z.1 = g z.2)
    (hsat : ∀ x ∈ A, ∀ y ∈ B, f x = g y →
      x ∈ M.image Prod.fst ∨ y ∈ M.image Prod.snd)
    (hbal : ∀ c ∈ t, gap (fiber A f c) (fiber B g c) ≤ 1)
    (hcomp : S ⊆ M ∨ M ⊆ S) :
    loss t (S.image Prod.fst) (S.image Prod.snd) f g =
      2 * (S.card - capacity t A B f g) := by
  rcases hcomp with hSM | hMS
  · have hcard := (card_mono hSM).trans_eq (saturated_card hM hf hfg hsat)
    rw [Nat.sub_eq_zero_of_le hcard, Nat.mul_zero]
    unfold loss
    apply sum_eq_zero
    intro c _
    rw [matched_fibers hS (fun z hz => hfg z (hSM hz)) c]
    simp [gap]
  · obtain ⟨hSA, hSB⟩ := matching_images_subset hS
    have hc (c : γ) (hc : c ∈ t) :
        gap (fiber (S.image Prod.fst) f c) (fiber (S.image Prod.snd) g c) ≤ 1 ∧
          min (fiber (S.image Prod.fst) f c) (fiber (S.image Prod.snd) g c) =
            min (fiber A f c) (fiber B g c) := by
      have hm := saturated_fibers hM hfg hsat c
      have hme := matched_fibers hM hfg c
      have hl := (hm.symm).trans_le (fiber_mono (image_subset_image hMS) f c)
      have hr := (hm.symm.trans hme).trans_le
        (fiber_mono (image_subset_image hMS) g c)
      have hla := fiber_mono hSA f c
      have hrb := fiber_mono hSB g c
      have hb := hbal c hc
      rcases le_total (fiber A f c) (fiber B g c) with h | h
      · rw [min_eq_left h] at hl hr ⊢
        have he := le_antisymm hla hl
        rw [min_eq_left (he.trans_le hr)]
        simp only [gap] at hb ⊢
        omega
      · rw [min_eq_right h] at hl hr ⊢
        have he := le_antisymm hrb hr
        rw [min_eq_right (he.trans_le hl)]
        simp only [gap] at hb ⊢
        omega
    have hcost : loss t (S.image Prod.fst) (S.image Prod.snd) f g =
        ∑ c ∈ t, gap (fiber (S.image Prod.fst) f c) (fiber (S.image Prod.snd) g c) := by
      unfold loss
      apply sum_congr rfl
      intro c hct
      have hb := (hc c hct).1
      generalize gap (fiber (S.image Prod.fst) f c) (fiber (S.image Prod.snd) g c) = a at hb ⊢
      have ha : a = 0 ∨ a = 1 := by omega
      rcases ha with rfl | rfl <;> norm_num
    have hcap : capacity t (S.image Prod.fst) (S.image Prod.snd) f g =
        capacity t A B f g := sum_congr rfl (fun c hct => (hc c hct).2)
    have hh := sum_gap (fun x hx => hf x (hSA hx)) (fun y hy => hg y (hSB hy))
    rw [← hcost, hcap, card_image_of_injOn hS.2.1, card_image_of_injOn hS.2.2] at hh
    omega

/-- For nested equivalence-by-label relations, one pair of equal-sized subsets
minimizes the squared count discrepancy at every level. The coarsest level
allows every edge. -/
theorem simultaneous_minimizer (A : Finset α) (B : Finset β) (f : ℕ → α → γ)
    (g : ℕ → β → γ) (t : ℕ → Finset γ) (e k : ℕ)
    (hcard : A.card = B.card) (hk : k ≤ A.card)
    (hnest : ∀ j < e, ∀ x y, f j x = g j y → f (j + 1) x = g (j + 1) y)
    (hcoarse : ∀ x ∈ A, ∀ y ∈ B, f e x = g e y)
    (hf : ∀ j ≤ e, ∀ x ∈ A, f j x ∈ t j)
    (hg : ∀ j ≤ e, ∀ y ∈ B, g j y ∈ t j)
    (hbal : ∀ j ≤ e, ∀ c ∈ t j, gap (fiber A (f j) c) (fiber B (g j) c) ≤ 1) :
    ∃ I ⊆ A, ∃ J ⊆ B, I.card = k ∧ J.card = k ∧
      ∀ j ≤ e, loss (t j) I J (f j) (g j) =
        2 * (k - capacity (t j) A B (f j) (g j)) := by
  let R : ℕ → α × β → Prop := fun j z => f (min j e) z.1 = g (min j e) z.2
  have hR : ∀ j z, R j z → R (j + 1) z := by
    intro j z hz
    by_cases h : j < e
    · simpa only [R, min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h)] using
        hnest j h z.1 z.2 (by simpa only [R, min_eq_left h.le] using hz)
    · simpa only [R, min_eq_right (show e ≤ j by omega),
        min_eq_right (show e ≤ j + 1 by omega)] using hz
  obtain ⟨M, hm, hM⟩ := exists_saturated_chain A B R hR e
  have he := hM e le_rfl
  have himages := matching_images_subset he.1
  have hAe : (M e).image Prod.fst = A := by
    apply eq_of_subset_of_card_le himages.1
    by_contra! h
    have h' : ((M e).image Prod.snd).card < B.card := by
      rwa [card_image_of_injOn he.1.2.2, ← card_image_of_injOn he.1.2.1, ← hcard]
    obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_of_card_lt_card h
    obtain ⟨y, hy, hy'⟩ := exists_mem_notMem_of_card_lt_card h'
    exact (he.2.2 x hx y hy (by simpa only [R, min_self] using hcoarse x hx y hy)).elim hx' hy'
  have hMe : (M e).card = A.card := (card_image_of_injOn he.1.2.1).symm.trans (congrArg card hAe)
  obtain ⟨S, hS, hSk, hcomp⟩ := exists_comparable_subset M hm k e (by simpa only [hMe] using hk)
  have hSm := he.1.mono hS
  obtain ⟨hI, hJ⟩ := matching_images_subset hSm
  refine ⟨S.image Prod.fst, hI, S.image Prod.snd, hJ,
    (card_image_of_injOn hSm.2.1).trans hSk, (card_image_of_injOn hSm.2.2).trans hSk, ?_⟩
  intro j hj
  obtain ⟨hMj, hfg, hsat⟩ := hM j hj
  rw [← hSk]
  exact loss_eq_of_comparable hMj hSm (hf j hj) (hg j hj)
    (fun z hz => by simpa only [R, min_eq_left hj] using hfg z hz)
    (fun x hx y hy hxy => hsat x hx y hy (by simpa only [R, min_eq_left hj] using hxy))
    (hbal j hj) (hcomp j hj)

end Matching

section Residues

/-- The nonnegative residue of the reflected column coordinate `-1-j`. -/
def reflected (q j : ℕ) : ℕ := q - 1 - j % q

theorem reflected_eq_iff_dvd {q : ℕ} (hq : 0 < q) (i j : ℕ) :
    i % q = reflected q j ↔ q ∣ i + j + 1 := by
  have hi := Nat.mod_lt i hq
  have hj := Nat.mod_lt j hq
  have hmod : (i + j + 1) % q = (i % q + j % q + 1) % q := by
    exact (((Nat.mod_modEq i q).add (Nat.mod_modEq j q)).add_right 1).symm
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  let s := i % q + j % q + 1
  have hs : s < 2 * q := by dsimp [s]; omega
  have hs0 : 0 < s := by dsimp [s]; omega
  change i % q = q - 1 - j % q ↔ s % q = 0
  have hsq : s % q = 0 ↔ s = q := by
    by_cases h : s < q
    · rw [Nat.mod_eq_of_lt h]
      omega
    · have hle : q ≤ s := by omega
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (show s - q < q by omega)]
      omega
  rw [hsq]
  dsimp [s]
  omega

theorem reflected_eq_reflected_iff {q : ℕ} (hq : 0 < q) (i j : ℕ) :
    reflected q i = reflected q j ↔ i % q = j % q := by
  have hi := Nat.mod_lt i hq
  have hj := Nat.mod_lt j hq
  unfold reflected
  omega

/-- Capacity for the two length-n reflected residue intervals. -/
def commonCapacity (n q : ℕ) : ℕ := n - min (n % q) (q - n % q)

private theorem row_fiber (n : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    fiber (range n) (· % q) c = n / q + if c < n % q then 1 else 0 := by
  simpa only [Nat.count_eq_card_filter_range, fiber, Nat.ModEq, Nat.mod_eq_of_lt hc]
    using Nat.count_modEq_card n hq c

private theorem reflected_fiber (n : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    fiber (range n) (reflected q) c = n / q + if q - n % q ≤ c then 1 else 0 := by
  let d := q - 1 - c
  have hd : d < q := by dsimp [d]; omega
  have hr : reflected q d = c := by
    rw [reflected, Nat.mod_eq_of_lt hd]
    dsimp [d]
    omega
  have he : (range n).filter (fun j => reflected q j = c) =
      (range n).filter (fun j => j % q = q - 1 - c) := by
    ext j
    rw [mem_filter, mem_filter]
    apply and_congr_right
    intro _
    calc
      reflected q j = c ↔ reflected q j = reflected q d := by rw [hr]
      _ ↔ j % q = d := by rw [reflected_eq_reflected_iff hq, Nat.mod_eq_of_lt hd]
  have ht : q - 1 - c < n % q ↔ q - n % q ≤ c := by
    have hr := Nat.mod_lt n hq
    omega
  calc
    _ = fiber (range n) (· % q) (q - 1 - c) := congrArg card he
    _ = _ := by simp only [row_fiber n hq (show q - 1 - c < q by omega), ht]

private theorem reflected_fibers_balanced (n : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    gap (fiber (range n) (· % q) c) (fiber (range n) (reflected q) c) ≤ 1 := by
  rw [row_fiber n hq hc, reflected_fiber n hq hc]
  unfold gap
  split_ifs <;> omega

theorem reflected_capacity (n : ℕ) {q : ℕ} (hq : 0 < q) :
    capacity (range q) (range n) (range n) (· % q) (reflected q) = commonCapacity n q := by
  have hr := Nat.mod_lt n hq
  have hc : (range q).filter (fun c => q - n % q ≤ c ∧ c < n % q) =
      Ico (q - n % q) (n % q) := by
    ext c
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  unfold capacity
  calc
    _ = ∑ c ∈ range q, (n / q + if q - n % q ≤ c ∧ c < n % q then 1 else 0) := by
      apply sum_congr rfl
      intro c hct
      rw [row_fiber n hq (mem_range.mp hct), reflected_fiber n hq (mem_range.mp hct)]
      split_ifs <;> omega
    _ = commonCapacity n q := by
      rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Finset.sum_boole, hc, Nat.card_Ico]
      change q * (n / q) + (n % q - (q - n % q)) = commonCapacity n q
      have hd := Nat.mod_add_div n q
      unfold commonCapacity
      rcases le_total (n % q) (q - n % q) with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega

/-- Twice the loss of a pair of index sets in one residue layer. -/
def residueLoss (q : ℕ) (I J : Finset ℕ) : ℕ :=
  loss (range q) I J (· % q) (reflected q)

theorem residue_loss_lower {n q k : ℕ} (hq : 0 < q) {I J : Finset ℕ}
    (hI : I ⊆ range n) (hJ : J ⊆ range n) (hIk : I.card = k) (hJk : J.card = k) :
    2 * (k - commonCapacity n q) ≤ residueLoss q I J := by
  rw [← reflected_capacity n hq]
  exact loss_lower hI hJ (fun x _ => mem_range.mpr (Nat.mod_lt x hq))
    (fun y _ => mem_range.mpr (by unfold reflected; omega)) hIk hJk

/-- Choose row and column indices that jointly minimize all p-power layers. -/
theorem exists_residue_minimizer {p n k : ℕ} (hp : 0 < p) (hk : k ≤ n) (e : ℕ) :
    ∃ I ⊆ range n, ∃ J ⊆ range n, I.card = k ∧ J.card = k ∧
      ∀ a ≤ e, residueLoss (p ^ a) I J = 2 * (k - commonCapacity n (p ^ a)) := by
  let q := fun j : ℕ => p ^ (e - j)
  have hq (j : ℕ) : 0 < q j := pow_pos hp _
  obtain ⟨I, hI, J, hJ, hIk, hJk, hopt⟩ :=
    simultaneous_minimizer (range n) (range n) (fun j i => i % q j)
      (fun j i => reflected (q j) i) (fun j => range (q j)) e k rfl (by simpa using hk)
      (fun j _ x y hxy => (reflected_eq_iff_dvd (hq (j + 1)) x y).mpr
        ((pow_dvd_pow p (show e - (j + 1) ≤ e - j by omega)).trans
          ((reflected_eq_iff_dvd (hq j) x y).mp hxy)))
      (fun x _ y _ => by simp [q, reflected, Nat.mod_one])
      (fun j _ x _ => mem_range.mpr (Nat.mod_lt x (hq j)))
      (fun j _ y _ => mem_range.mpr (show reflected (q j) y < q j by
        have := hq j
        unfold reflected
        omega))
      (fun j _ c hc => reflected_fibers_balanced n (hq j) (mem_range.mp hc))
  refine ⟨I, hI, J, hJ, hIk, hJk, ?_⟩
  intro a ha
  have he : e - (e - a) = a := by omega
  simpa only [residueLoss, q, he, reflected_capacity n (pow_pos hp a)] using
    hopt (e - a) (Nat.sub_le e a)

end Residues

end D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
