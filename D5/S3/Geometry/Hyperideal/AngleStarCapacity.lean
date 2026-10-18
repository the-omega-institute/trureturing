/- GID: D5/S3/Geometry/Hyperideal/AngleStarCapacity
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/AngleStarCapacity
   mirror-E: none(waiver:weighted-angle-star-capacity)
   anchors: []
   utility: none
   digest: Finite weighted angle-star capacity inequality. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19006
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.AngleStarCapacity

/-
This is the finite summation core of the mixed-matching capacity estimate.
The functions `alpha` and `neighbor` are occurrence-level angle masses.  The
second hypothesis records the actual multiplicity bound after the local
neighbor slots have been grouped by their global label.  No geometric
realization, angle formula, or equal-label assumption is hidden in the lemma.
-/
theorem weighted_star_capacity
    {I F : Type*} [Fintype I] [Fintype F] [Nonempty I]
    (π g m : ℝ) (mf : F → ℝ)
    (alpha : I → ℝ) (neighbor : I → F → ℝ) (mu : F → ℝ)
    (hπ : 0 < π)
    (hcard : g = Fintype.card I)
    (hlower : ∀ i, π < 2 * alpha i + ∑ f : F, neighbor i f)
    (htarget : (∑ i : I, alpha i) = (2 - m) * π)
    (hneighbor : ∀ f, (∑ i : I, neighbor i f) ≤
      mu f * ((2 - mf f) * π)) :
    g < 2 * (2 - m) + ∑ f : F, mu f * (2 - mf f) := by
  classical
  let R : ℝ := ∑ f : F, mu f * (2 - mf f)
  have hlocal :
      (∑ i : I, π) < ∑ i : I, (2 * alpha i + ∑ f : F, neighbor i f) := by
    refine Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset I))
      Finset.univ_nonempty ?_
    intro i hi
    exact hlower i
  have haggregate :
      (∑ i : I, (2 * alpha i + ∑ f : F, neighbor i f)) =
        2 * (∑ i : I, alpha i) + ∑ f : F, ∑ i : I, neighbor i f := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.mul_sum]
    · rw [Finset.sum_comm]
  have hneighbor_total :
      (∑ f : F, ∑ i : I, neighbor i f) ≤
        ∑ f : F, mu f * ((2 - mf f) * π) := by
    exact Finset.sum_le_sum (fun f _ => hneighbor f)
  have hneighbor_factor :
      (∑ f : F, mu f * ((2 - mf f) * π)) =
        (∑ f : F, mu f * (2 - mf f)) * π := by
    calc
      (∑ f : F, mu f * ((2 - mf f) * π)) =
          ∑ f : F, (mu f * (2 - mf f)) * π := by
        apply Finset.sum_congr rfl
        intro f hf
        ring
      _ = (∑ f : F, mu f * (2 - mf f)) * π := by
        rw [Finset.sum_mul]
  have htotal :
      (Fintype.card I : ℝ) * π <
        (2 * (2 - m) + R) * π := by
    calc
      (Fintype.card I : ℝ) * π = ∑ i : I, π := by simp
      _ < ∑ i : I, (2 * alpha i + ∑ f : F, neighbor i f) := hlocal
      _ = 2 * (∑ i : I, alpha i) + ∑ f : F, ∑ i : I, neighbor i f :=
        haggregate
      _ ≤ 2 * ((2 - m) * π) +
          ∑ f : F, mu f * ((2 - mf f) * π) := by
        rw [htarget]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hneighbor_total (2 * ((2 - m) * π))
      _ = (2 * (2 - m)) * π + R * π := by
        rw [hneighbor_factor]
        dsimp [R]
        ring
      _ = (2 * (2 - m) + R) * π := by ring
  rw [hcard]
  nlinarith [htotal, hπ]

#print axioms weighted_star_capacity

end D5.S3.Geometry.Hyperideal.AngleStarCapacity
