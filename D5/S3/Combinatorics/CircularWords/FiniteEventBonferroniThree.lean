/- GID: D5/S3/Combinatorics/CircularWords/FiniteEventBonferroniThree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/FiniteEventBonferroniThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Third finite Bonferroni truncation for actual common-space event intersections. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The inequality is evaluated on one finite space, without independence hypotheses. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.FiniteEventBonferroniThree

open Finset
open scoped BigOperators Classical

universe u v
variable {α : Type u} {ι : Type v}

private theorem pointwise_three (h : ℕ) :
    (∑ p ∈ range 4, (-1:ℚ)^p * (h.choose p : ℚ)) ≤ if h=0 then 1 else 0 := by
  by_cases hh : h=0
  · simp [hh,Finset.sum_range_succ]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh
    have he := Int.alternating_sum_range_choose_eq_choose (n := k) (m := 3)
    norm_num at he
    have heq : (∑ p ∈ range 4, (-1:ℚ)^p * ((k+1).choose p : ℚ)) =
        -(k.choose 3 : ℚ) := by exact_mod_cast he
    rw [heq,if_neg (by omega : k+1 ≠ 0)]
    exact neg_nonpos.mpr (by positivity)

/-- Count an actual intersection by the corresponding subsets of occurring events. -/
theorem intersection_moment (X : Finset α) (I : Finset ι) (E : ι → α → Prop) (p : ℕ) :
    (∑ T ∈ I.powersetCard p, ((X.filter (fun x => ∀ i ∈ T, E i x)).card : ℚ)) =
      ∑ x ∈ X, (((I.filter (fun i => E i x)).card).choose p : ℚ) := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x hx
  have he : (I.powersetCard p).filter (fun T => ∀ i ∈ T, E i x) =
      (I.filter (fun i => E i x)).powersetCard p := by
    ext T
    simp only [mem_filter,mem_powersetCard,Finset.subset_iff]
    constructor
    · rintro ⟨⟨hT,hp⟩,hE⟩
      exact ⟨fun i hi => ⟨hT hi,hE i hi⟩,hp⟩
    · rintro ⟨hT,hp⟩
      exact ⟨⟨fun i hi => (hT hi).1,hp⟩,fun i hi => (hT hi).2⟩
  calc
    _ = (((I.powersetCard p).filter (fun T => ∀ i ∈ T, E i x)).card : ℚ) := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,
        Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    _ = _ := by
      rw [he,Finset.card_powersetCard]
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

/-- The third odd Bonferroni sum bounds the actual number of points avoiding every event. -/
theorem bonferroni_three (X : Finset α) (I : Finset ι) (E : ι → α → Prop) :
    (∑ p ∈ range 4, (-1:ℚ)^p *
      ∑ T ∈ I.powersetCard p, ((X.filter (fun x => ∀ i ∈ T, E i x)).card : ℚ)) ≤
      ((X.filter (fun x => ∀ i ∈ I, ¬ E i x)).card : ℚ) := by
  classical
  simp_rw [intersection_moment,mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ X, if (I.filter (fun i => E i x)).card=0 then (1:ℚ) else 0 := by
      apply sum_le_sum
      intro x hx
      exact pointwise_three _
    _ = _ := by
      have he (x : α) : (I.filter (fun i => E i x)).card=0 ↔ ∀ i ∈ I, ¬ E i x := by
        simp
      simp_rw [he]
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,
        Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end D5.S3.Combinatorics.CircularWords.FiniteEventBonferroniThree
