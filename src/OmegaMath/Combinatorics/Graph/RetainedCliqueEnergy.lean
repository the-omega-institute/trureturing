import OmegaBuild.Commands
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import OmegaMath.Combinatorics.Graph.ElementarySymmetricAverage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Product-weighted averaging of retained clique inequalities -/

compile_only_with_mathlib

open scoped BigOperators

namespace RetainedCliqueEnergy

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric weight carried by extensions of a fixed subset. -/
theorem sum_containing (p : ι → ℝ) (S A : Finset ι) (s : ℕ)
    (hA : A ⊆ S) (hc : A.card ≤ s) :
    (∑ W ∈ (S.powersetCard s).filter (A ⊆ ·), ∏ v ∈ W, p v) =
      (∏ v ∈ A, p v) * ∑ W ∈ (S \ A).powersetCard (s - A.card), ∏ v ∈ W, p v := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun W _ => W \ A) ?_ ?_ ?_ ?_
  · intro W hW
    have h := Finset.mem_filter.mp hW
    obtain ⟨hs, he⟩ := Finset.mem_powersetCard.mp h.1
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.sdiff_subset_sdiff hs (Subset.refl _), by rw [Finset.card_sdiff_of_subset h.2, he]⟩
  · intro W hW U hU eq
    have hw := Finset.sdiff_union_of_subset (Finset.mem_filter.mp hW).2
    have hu := Finset.sdiff_union_of_subset (Finset.mem_filter.mp hU).2
    rw [eq, hu] at hw
    exact hw.symm
  · intro T hT
    obtain ⟨hs, ht⟩ := Finset.mem_powersetCard.mp hT
    have hd : Disjoint T A := Finset.sdiff_disjoint.mono_left hs
    refine ⟨T ∪ A, ?_, Finset.union_sdiff_cancel_right hd⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.subset_union_right⟩
    · exact Finset.union_subset (hs.trans Finset.sdiff_subset) hA
    · rw [Finset.card_union_of_disjoint hd, ht]
      omega
  · intro W hW
    have h := Finset.mem_filter.mp hW
    rw [mul_comm, ← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h.2]

/-- Summing over subcliques exchanges the enclosing-set and incidence sums. -/
theorem exchange (p : ι → ℝ) (S : Finset ι) (s k : ℕ) (hk : k ≤ s)
    (f : Finset ι → ℝ) :
    (∑ W ∈ S.powersetCard s, (∏ v ∈ W, p v) * ∑ A ∈ W.powersetCard k, f A) =
      ∑ A ∈ S.powersetCard k,
        f A * ((∏ v ∈ A, p v) * ∑ T ∈ (S \ A).powersetCard (s - k), ∏ v ∈ T, p v) := by
  classical
  have hin (W : Finset ι) (hW : W ∈ S.powersetCard s) :
      W.powersetCard k = (S.powersetCard k).filter (· ⊆ W) := by
    ext A
    have hs := (Finset.mem_powersetCard.mp hW).1
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1.trans hs, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  calc
    _ = ∑ W ∈ S.powersetCard s, ∑ A ∈ S.powersetCard k,
        if A ⊆ W then f A * (∏ v ∈ W, p v) else 0 := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [hin W hW, Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun A _ => by split_ifs <;> ring
    _ = ∑ A ∈ S.powersetCard k, ∑ W ∈ S.powersetCard s,
        if A ⊆ W then f A * (∏ v ∈ W, p v) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hA
      rw [← hc, ← sum_containing p S A s hs (hc ▸ hk), Finset.mul_sum, Finset.sum_filter]
      all_goals exact Finset.sum_congr rfl fun W _ => by split_ifs <;> ring

end RetainedCliqueEnergy

namespace RetainedCliqueEnergy

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Retained clique inequalities average with product weights. The coefficients
of an edge and triangle are controlled by the complementary symmetric sums. -/
theorem average (p : ι → ℝ) (S : Finset ι) (s : ℕ) (hs : 3 ≤ s)
    (d h : Finset ι → ℝ) (β E₂ E₃ : ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i)
    (hd : ∀ A ∈ S.powersetCard 2, 0 ≤ d A)
    (hh : ∀ A ∈ S.powersetCard 3, 0 ≤ h A) (hβ : 0 ≤ β)
    (hE₂ : ∀ A ∈ S.powersetCard 2,
      (∑ T ∈ (S \ A).powersetCard (s - 2), ∏ v ∈ T, p v) ≤ E₂)
    (hE₃ : ∀ A ∈ S.powersetCard 3,
      (∑ T ∈ (S \ A).powersetCard (s - 3), ∏ v ∈ T, p v) ≤ E₃)
    (hInv : ∀ W ∈ S.powersetCard s, β * (s.choose 3 : ℝ) ≤
      (∑ A ∈ W.powersetCard 2, d A) + β * ∑ A ∈ W.powersetCard 3, h A) :
    β * (s.choose 3 : ℝ) * (∑ W ∈ S.powersetCard s, ∏ v ∈ W, p v) ≤
      E₂ * (∑ A ∈ S.powersetCard 2, (∏ v ∈ A, p v) * d A) +
        β * E₃ * (∑ A ∈ S.powersetCard 3, (∏ v ∈ A, p v) * h A) := by
  have hpos (j : ℕ) (A : Finset ι) (hA : A ∈ S.powersetCard j) :
      0 ≤ ∏ v ∈ A, p v :=
    Finset.prod_nonneg fun i hi => hp i ((Finset.mem_powersetCard.mp hA).1 hi)
  have hbound (j : ℕ) (hj : j ≤ s) (a : Finset ι → ℝ) (B : ℝ)
      (ha : ∀ A ∈ S.powersetCard j, 0 ≤ a A)
      (hB : ∀ A ∈ S.powersetCard j,
        (∑ T ∈ (S \ A).powersetCard (s - j), ∏ v ∈ T, p v) ≤ B) :
      (∑ W ∈ S.powersetCard s, (∏ v ∈ W, p v) * ∑ A ∈ W.powersetCard j, a A) ≤
        B * (∑ A ∈ S.powersetCard j, (∏ v ∈ A, p v) * a A) := by
    rw [exchange p S s j hj a, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    have h := mul_le_mul_of_nonneg_left (hB A hA) (mul_nonneg (ha A hA) (hpos j A hA))
    convert h using 1 <;> ring
  have hleft : β * (s.choose 3 : ℝ) * (∑ W ∈ S.powersetCard s, ∏ v ∈ W, p v) ≤
      (∑ W ∈ S.powersetCard s, (∏ v ∈ W, p v) * ∑ A ∈ W.powersetCard 2, d A) +
      β * (∑ W ∈ S.powersetCard s, (∏ v ∈ W, p v) * ∑ A ∈ W.powersetCard 3, h A) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro W hW
    have hineq := mul_le_mul_of_nonneg_left (hInv W hW) (hpos s W hW)
    have h₁ : (∑ A ∈ W.powersetCard 2, (∏ v ∈ W, p v) * d A) =
        (∏ v ∈ W, p v) * ∑ A ∈ W.powersetCard 2, d A := by
      rw [Finset.mul_sum]
    have h₂ : (∑ A ∈ W.powersetCard 3, β * ((∏ v ∈ W, p v) * h A)) =
        (∏ v ∈ W, p v) * β * ∑ A ∈ W.powersetCard 3, h A := by
      simp only [Finset.mul_sum, mul_assoc, mul_left_comm]
    rw [h₁, h₂]
    linarith only [hineq]
  have he := hbound 2 (by omega) d E₂ hd hE₂
  have ht := mul_le_mul_of_nonneg_left (hbound 3 hs h E₃ hh hE₃) hβ
  exact hleft.trans ((add_le_add he ht).trans_eq (by ring))

end RetainedCliqueEnergy

namespace RetainedCliqueEnergy

open Finset

variable {ι κ : Type*} [DecidableEq ι]

/-- An indexed incidence sum with each term supported on its own subset. -/
theorem exchange_indexed (p : ι → ℝ) (S : Finset ι) (s : ℕ)
    (J : Finset κ) (support : κ → Finset ι) (f : κ → ℝ)
    (hS : ∀ t ∈ J, support t ⊆ S) (hcard : ∀ t ∈ J, (support t).card ≤ s) :
    (∑ W ∈ S.powersetCard s, (∏ v ∈ W, p v) *
      ∑ t ∈ J.filter (fun t => support t ⊆ W), f t) =
      ∑ t ∈ J, f t * (∏ v ∈ support t, p v) *
        ∑ T ∈ (S \ support t).powersetCard (s - (support t).card), ∏ v ∈ T, p v := by
  calc
    _ = ∑ W ∈ S.powersetCard s, ∑ t ∈ J,
        if support t ⊆ W then f t * (∏ v ∈ W, p v) else 0 := by
      apply Finset.sum_congr rfl
      intro W _
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
    _ = ∑ t ∈ J, ∑ W ∈ S.powersetCard s,
        if support t ⊆ W then f t * (∏ v ∈ W, p v) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [mul_assoc, ← sum_containing p S (support t) s (hS t ht) (hcard t ht),
        Finset.mul_sum, Finset.sum_filter]
      all_goals exact Finset.sum_congr rfl fun W _ => by split_ifs <;> ring

end RetainedCliqueEnergy

namespace RetainedCliqueEnergy

/-- A complementary incidence bound and an elementary-symmetric lower bound
give the credit due to the retained clique invariant. -/
theorem credit {B n e P C J μ β τ E₂ E₃ d h c : ℝ}
    (hB : 0 ≤ B) (hμ : 0 ≤ 1 + μ) (hE₂ : 0 < E₂) (hh : 0 ≤ h)
    (hcurl : β * E₃ ≤ c * E₂) (hcoeff : E₂ * (B * n) = (1 + μ) * (β * τ))
    (haverage : β * τ * e ≤ E₂ * d + β * E₃ * h)
    (he : P - C * J ≤ n * e) :
    B * (P - C * J) ≤ (1 + μ) * (d + c * h) := by
  have ha := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hB) hE₂.le
  have hb := mul_le_mul_of_nonneg_left haverage hμ
  have hc := mul_le_mul_of_nonneg_right hcurl hh
  have hd := mul_le_mul_of_nonneg_left hc hμ
  have he' := congrArg (fun v : ℝ => v * e) hcoeff
  apply le_of_mul_le_mul_left _ hE₂
  ring_nf at ha hb hd he' ⊢
  linarith only [ha, hb, hd, he']

end RetainedCliqueEnergy

namespace RetainedCliqueEnergy

open Finset

variable {ι κ : Type*} [DecidableEq ι]

/-- Grouping oriented terms by support counts each weighted term exactly once. -/
theorem group_support (w : Finset ι → ℝ) (S : Finset ι) (s : ℕ) (T : Finset κ)
    (support : κ → Finset ι) (f : κ → ℝ)
    (hS : ∀ t ∈ T, support t ∈ S.powersetCard s) :
    (∑ A ∈ S.powersetCard s, w A * ∑ t ∈ T, if support t = A then f t else 0) =
      ∑ t ∈ T, w (support t) * f t := by
  classical
  calc
    _ = ∑ A ∈ S.powersetCard s, ∑ t ∈ T,
          if A = support t then w A * f t else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero, eq_comm]
    _ = ∑ t ∈ T, ∑ A ∈ S.powersetCard s,
          if A = support t then w A * f t else 0 := Finset.sum_comm
    _ = _ := by
      exact Finset.sum_congr rfl fun t ht => by simp [hS t ht]

/-- Ordered pair sums over two-element subsets recover the pair sum on the
ambient set, with each pair weighted by the product of the endpoint weights. -/
theorem group_pairs (p : ι → ℝ) (S : Finset ι) (f : ι → ι → ℝ) :
    (∑ A ∈ S.powersetCard 2, (∏ v ∈ A, p v) *
      ∑ i ∈ A, ∑ j ∈ A, if i = j then 0 else f i j) =
        ∑ i ∈ S, ∑ j ∈ S, if i = j then 0 else p i * p j * f i j := by
  classical
  let T := (S ×ˢ S).filter (fun t => t.1 ≠ t.2)
  let support (t : ι × ι) : Finset ι := {t.1, t.2}
  have hs (t : ι × ι) (ht : t ∈ T) : support t ∈ S.powersetCard 2 := by
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp ha
    exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩,
      Finset.card_eq_two.mpr ⟨_, _, he, rfl⟩⟩
  have hg := group_support (fun A => ∏ v ∈ A, p v) S 2 T support (fun t => f t.1 t.2) hs
  have unroll (A : Finset ι) (g : ι → ι → ℝ) :
      (∑ i ∈ A, ∑ j ∈ A, g i j) = ∑ t ∈ A ×ˢ A, g t.1 t.2 := by
    simp only [Finset.sum_product]
  calc
    _ = ∑ A ∈ S.powersetCard 2, (∏ v ∈ A, p v) *
          ∑ t ∈ T, if support t = A then f t.1 t.2 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      congr 1
      have he (t : ι × ι) : t ∈ T ∧ support t = A ↔ t ∈ (A ×ˢ A) ∧ t.1 ≠ t.2 := by
        constructor
        · rintro ⟨ht, rfl⟩
          exact ⟨by simp [support], (Finset.mem_filter.mp ht).2⟩
        · rintro ⟨ht, hne⟩
          have hA' := Finset.mem_powersetCard.mp hA
          obtain ⟨hi, hj⟩ := Finset.mem_product.mp ht
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA'.1 hi, hA'.1 hj⟩, hne⟩, ?_⟩
          apply Finset.eq_of_subset_of_card_le
          · exact Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
          · rw [hA'.2, Finset.card_eq_two.mpr ⟨_, _, hne, rfl⟩]
      rw [unroll]
      simp only [show (∑ t ∈ A ×ˢ A, if t.1 = t.2 then 0 else f t.1 t.2) =
          ∑ t ∈ (A ×ˢ A).filter (fun t => t.1 ≠ t.2), f t.1 t.2 by
        simp [Finset.sum_filter, ite_not]]
      rw [← Finset.sum_filter]
      congr 1
      ext t
      simpa only [Finset.mem_filter] using (he t).symm
    _ = ∑ t ∈ T, (∏ v ∈ support t, p v) * f t.1 t.2 := hg
    _ = _ := by
      have hprod (t : ι × ι) (ht : t ∈ T) :
          (∏ v ∈ support t, p v) = p t.1 * p t.2 :=
        Finset.prod_pair (Finset.mem_filter.mp ht).2
      rw [unroll]
      calc
        _ = ∑ t ∈ T, p t.1 * p t.2 * f t.1 t.2 :=
          Finset.sum_congr rfl fun t ht => by rw [hprod t ht]
        _ = _ := by simp [T, Finset.sum_filter, ite_not]

/-- Ordered triples over three-element subsets satisfy the analogous
product-weighted grouping identity. -/
theorem group_triples (p : ι → ℝ) (S : Finset ι) (f : ι → ι → ι → ℝ) :
    (∑ A ∈ S.powersetCard 3, (∏ v ∈ A, p v) *
      ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, if i = j ∨ j = k ∨ i = k then 0 else f i j k) =
        ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S,
          if i = j ∨ j = k ∨ i = k then 0 else p i * p j * p k * f i j k := by
  classical
  let distinct (t : ι × ι × ι) : Prop := ¬ (t.1 = t.2.1 ∨ t.2.1 = t.2.2 ∨ t.1 = t.2.2)
  let T := (S ×ˢ (S ×ˢ S)).filter distinct
  let support (t : ι × ι × ι) : Finset ι := {t.1, t.2.1, t.2.2}
  have hc (t : ι × ι × ι) (ht : distinct t) : (support t).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, fun h => ht (.inl h),
      fun h => ht (.inr (.inr h)), fun h => ht (.inr (.inl h)), rfl⟩
  have hs (t : ι × ι × ι) (ht : t ∈ T) : support t ∈ S.powersetCard 3 := by
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨hi, hj, hk⟩ : t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S := by simpa using ha
    exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hi, Finset.insert_subset_iff.mpr ⟨hj, Finset.singleton_subset_iff.mpr hk⟩⟩, hc t he⟩
  have hg := group_support (fun A => ∏ v ∈ A, p v) S 3 T support (fun t => f t.1 t.2.1 t.2.2) hs
  have unroll (A : Finset ι) (g : ι → ι → ι → ℝ) :
      (∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A, g i j k) =
        ∑ t ∈ A ×ˢ (A ×ˢ A), g t.1 t.2.1 t.2.2 := by
    simp only [Finset.sum_product]
  calc
    _ = ∑ A ∈ S.powersetCard 3, (∏ v ∈ A, p v) *
          ∑ t ∈ T, if support t = A then f t.1 t.2.1 t.2.2 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      congr 1
      have he (t : ι × ι × ι) : t ∈ T ∧ support t = A ↔
          t ∈ A ×ˢ (A ×ˢ A) ∧ distinct t := by
        constructor
        · rintro ⟨ht, rfl⟩
          exact ⟨by simp [support], (Finset.mem_filter.mp ht).2⟩
        · rintro ⟨ht, hne⟩
          have hA' := Finset.mem_powersetCard.mp hA
          obtain ⟨hi, hj, hk⟩ : t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A := by simpa using ht
          refine ⟨Finset.mem_filter.mpr ⟨by simp [hA'.1 hi, hA'.1 hj, hA'.1 hk], hne⟩, ?_⟩
          apply Finset.eq_of_subset_of_card_le
          · exact Finset.insert_subset_iff.mpr ⟨hi, Finset.insert_subset_iff.mpr ⟨hj, Finset.singleton_subset_iff.mpr hk⟩⟩
          · rw [hA'.2, hc t hne]
      rw [unroll]
      have he' : (∑ t ∈ A ×ˢ (A ×ˢ A),
          if t.1 = t.2.1 ∨ t.2.1 = t.2.2 ∨ t.1 = t.2.2 then 0 else f t.1 t.2.1 t.2.2) =
            ∑ t ∈ (A ×ˢ (A ×ˢ A)).filter distinct, f t.1 t.2.1 t.2.2 := by
        simp_rw [Finset.sum_filter, distinct]
        exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp_all
      rw [he', ← Finset.sum_filter]
      congr 1
      ext t
      simpa only [Finset.mem_filter] using (he t).symm
    _ = ∑ t ∈ T, (∏ v ∈ support t, p v) * f t.1 t.2.1 t.2.2 := hg
    _ = _ := by
      rw [unroll]
      calc
        _ = ∑ t ∈ T, p t.1 * p t.2.1 * p t.2.2 * f t.1 t.2.1 t.2.2 := by
          apply Finset.sum_congr rfl
          intro t ht
          have h := (Finset.mem_filter.mp ht).2
          have h₁ : t.1 ≠ t.2.1 := fun e => h (.inl e)
          have h₂ : t.1 ≠ t.2.2 := fun e => h (.inr (.inr e))
          have h₃ : t.2.1 ≠ t.2.2 := fun e => h (.inr (.inl e))
          simp [support, Finset.prod_insert, h₁, h₂, h₃, mul_assoc]
        _ = _ := by
          simp_rw [T, Finset.sum_filter, distinct]
          exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp_all

end RetainedCliqueEnergy

namespace RetainedCliqueEnergy

open Finset ElementarySymmetricAverage

variable {ι : Type*} [DecidableEq ι]

/-- Adjoining zero coordinates preserves total mass, squared mass, and every
elementary symmetric sum. -/
theorem pad (S : Finset ι) (p : ι → ℝ) (N : ℕ) (hcard : S.card ≤ N)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    ∃ q : Fin N → ℝ, (∀ i, 0 ≤ q i) ∧
      (∑ i, q i) = ∑ i ∈ S, p i ∧
      (∑ i, q i ^ 2) = ∑ i ∈ S, p i ^ 2 ∧
      ∀ k, elementary Finset.univ k q = elementary S k p := by
  classical
  let e : S ↪ Fin N := (Finset.equivFin S).toEmbedding.trans (Fin.castLEEmb hcard)
  let a : S → ℝ := fun i => p i.val
  let q : Fin N → ℝ := Function.extend e a (fun _ => 0)
  let T : Finset (Fin N) := S.attach.map e
  have hqa (i : S) : q (e i) = a i := e.injective.extend_apply a (fun _ => 0) i
  have hqz (i : Fin N) (hi : i ∉ T) : q i = 0 := by
    apply Function.extend_apply' a (fun _ => 0) i
    rintro ⟨j, rfl⟩
    exact hi (Finset.mem_map.mpr ⟨j, Finset.mem_attach _ _, rfl⟩)
  have hq₀ (i : Fin N) : 0 ≤ q i := by
    by_cases hi : i ∈ T
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
      rw [hqa]
      exact hp _ j.property
    · rw [hqz i hi]
  have hsum (f : ℝ → ℝ) (hf : f 0 = 0) :
      (∑ i, f (q i)) = ∑ i ∈ S, f (p i) := by
    have hu : (∑ i ∈ T, f (q i)) = ∑ i, f (q i) :=
      Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [hqz i hi, hf])
    rw [← hu]
    unfold T
    rw [Finset.sum_map]
    simp_rw [hqa]
    exact Finset.sum_attach S (fun i => f (p i))
  refine ⟨q, hq₀, hsum id rfl, hsum (· ^ 2) (by norm_num), ?_⟩
  intro k
  have htrim : elementary T k q = elementary Finset.univ k q := by
    unfold elementary
    apply Finset.sum_subset
    · exact Finset.powersetCard_mono (Finset.subset_univ T)
    · intro A hA hAT
      have hsize := (Finset.mem_powersetCard.mp hA).2
      have hnot : ¬ A ⊆ T := fun h => hAT (Finset.mem_powersetCard.mpr ⟨h,hsize⟩)
      have hbad : ∃ i ∈ A, i ∉ T := by simpa [Finset.subset_iff] using hnot
      obtain ⟨i, hi, hiT⟩ := hbad
      exact Finset.prod_eq_zero hi (hqz i hiT)
  rw [← htrim]
  unfold T
  rw [elementary_map]
  have ha : q ∘ e = a := funext hqa
  rw [ha]
  have hback := elementary_map (Function.Embedding.subtype (· ∈ S)) S.attach k p
  simpa [Finset.attach_map_val, a, Function.comp_def] using hback.symm

/-- Padding makes the uniform upper bound depend on the ambient cutoff. -/
theorem complement_bound (S : Finset ι) (p : ι → ℝ) (N k : ℕ)
    (hcard : S.card ≤ N) (hp : ∀ i ∈ S, 0 ≤ p i) (hmass : ∑ i ∈ S, p i ≤ 1) :
    elementary S k p ≤ ((N.choose k : ℕ) : ℝ) * (1 / (N : ℝ)) ^ k := by
  obtain ⟨q, hq, hsum, _, he⟩ := pad S p N hcard hp
  rw [← he k]
  simpa only [Finset.card_univ, Fintype.card_fin] using elementary_le_of_sum_le
    (Finset.univ : Finset (Fin N)) k q (fun i _ => hq i) 1 (hsum.trans_le hmass)

theorem pad_lower (S : Finset ι) (p : ι → ℝ) (N k : ℕ) (hN : 0 < N)
    (hcard : S.card ≤ N) (hp : ∀ i ∈ S, 0 ≤ p i) (hmass : ∑ i ∈ S, p i = 1) :
    factor N (k + 2) - (((k + 2).choose 2 : ℕ) : ℝ) * factor (N - 2) k *
      ((∑ i ∈ S, p i ^ 2) - 1 / (N : ℝ)) ≤
      ((k + 2).factorial : ℝ) * elementary S (k + 2) p := by
  obtain ⟨q, hq, hsum, hsq, he⟩ := pad S p N hcard hp
  rw [hmass] at hsum
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hvar : variance (1 / (N : ℝ)) q = (∑ i, q i ^ 2) - 1 / (N : ℝ) := by
    unfold variance
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hh : (∑ i, 2 * q i * (1 / (N : ℝ))) = 2 * (1 / (N : ℝ)) := by
      calc
        _ = ∑ i, q i * (2 * (1 / (N : ℝ))) := Finset.sum_congr rfl fun i _ => by ring
        _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [hh]
    field_simp [hn]
    <;> ring
  have hh := factorial_elementary_lower k q hq hsum
  simpa only [Fintype.card_fin, hvar, hsq, he] using hh

end RetainedCliqueEnergy
