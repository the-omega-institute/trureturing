/- GID: D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet
   generality: G
   mirror-B: none(waiver:rh-bridge)
   mirror-E: none(waiver:rh-bridge)
   anchors: []
   utility: none
   digest: The finite association quotient carries a nonnegative pairwise Dirichlet energy; its kernel is exactly q-measurable source data, with a strict 5040 hidden-label witness. -/

import D5.S3.Arith.GoldenResource.DivisorAssociationFiber
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.DivisorAssociationDirichlet

open scoped BigOperators
open D5.S3.Arith.GoldenResource.DivisorAssociationFiber

abbrev Pair := Source × Source

def sameFiberPairs (A B C D : ℕ) : Finset Pair :=
  (box A B C D ×ˢ box A B C D).filter (fun p => q p.1 = q p.2)

/-- Pairwise Dirichlet energy inside each observed fiber. -/
def fiberEnergy (A B C D : ℕ) (u : Source → ℝ) : ℝ :=
  ∑ p ∈ sameFiberPairs A B C D, (u p.1 - u p.2) ^ 2

theorem fiberEnergy_nonneg (A B C D : ℕ) (u : Source → ℝ) :
    0 ≤ fiberEnergy A B C D u := by
  unfold fiberEnergy
  exact Finset.sum_nonneg (fun p hp => sq_nonneg _)

private theorem pair_mem_sameFiberPairs {A B C D : ℕ} {s t : Source}
    (hs : s ∈ box A B C D) (ht : t ∈ box A B C D) (hqt : q s = q t) :
    (s, t) ∈ sameFiberPairs A B C D := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, ht⟩, hqt⟩

private theorem energy_term_eq_zero {A B C D : ℕ} {u : Source → ℝ}
    (hzero : fiberEnergy A B C D u = 0) {s t : Source}
    (hs : s ∈ box A B C D) (ht : t ∈ box A B C D) (hqt : q s = q t) :
    u s = u t := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p hp => sq_nonneg (u p.1 - u p.2))).mp hzero
    (s, t) (pair_mem_sameFiberPairs hs ht hqt)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)

/-- Zero energy is equivalent to constancy on every observed fiber of the box. -/
theorem fiberEnergy_eq_zero_iff (A B C D : ℕ) (u : Source → ℝ) :
    fiberEnergy A B C D u = 0 ↔
      ∀ s ∈ box A B C D, ∀ t ∈ box A B C D, q s = q t → u s = u t := by
  constructor
  · intro hzero s hs t ht hqt
    exact energy_term_eq_zero hzero hs ht hqt
  · intro hconst
    unfold fiberEnergy
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hp'.1 with ⟨hps, hpt⟩
    have hst := hconst p.1 hps p.2 hpt hp'.2
    simp [hst]

/-- Any position function has zero energy after pullback along q. -/
theorem fiberEnergy_pullback_zero (A B C D : ℕ) (g : Position → ℝ) :
    fiberEnergy A B C D (fun s => g (q s)) = 0 := by
  apply (fiberEnergy_eq_zero_iff A B C D _).mpr
  intro s hs t ht hqt
  simp [hqt]

/-- A nonconstant hidden label in one observed fiber forces positive energy. -/
theorem fiberEnergy_pos_of_collision {A B C D : ℕ} {u : Source → ℝ}
    {s t : Source} (hs : s ∈ box A B C D) (ht : t ∈ box A B C D)
    (hqt : q s = q t) (hneq : u s ≠ u t) :
    0 < fiberEnergy A B C D u := by
  apply Finset.sum_pos'
  · intro p hp
    exact sq_nonneg _
  · refine ⟨(s, t), pair_mem_sameFiberPairs hs ht hqt, ?_⟩
    exact sq_pos_iff.mpr (sub_ne_zero.mpr hneq)

/-- The 5040 box has a strict hidden-label Dirichlet defect for the fourth exponent. -/
theorem fiberEnergy_5040_hidden_pos :
    0 < fiberEnergy 4 2 1 1 (fun s : Source => (s.2.2.2 : ℝ)) := by
  let s : Source := (1, 0, 0, 1)
  let t : Source := (2, 0, 1, 0)
  have hs : s ∈ box 4 2 1 1 := by
    simp [s, box]
  have ht : t ∈ box 4 2 1 1 := by
    simp [t, box]
  have hq : q s = q t := by
    simp [s, t, q]
  have hneq : (fun z : Source => (z.2.2.2 : ℝ)) s ≠
      (fun z : Source => (z.2.2.2 : ℝ)) t := by
    norm_num [s, t]
  exact fiberEnergy_pos_of_collision hs ht hq hneq

end D5.S3.Arith.GoldenResource.DivisorAssociationDirichlet
