/- GID: D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: At every cutoff the complete signed finite-head tail is summable and has exactly the retained-coefficient zero kernel. -/

import D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail
import D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Weil.ZetaBridge
open D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge

/-- Literal cropping of BOTH signed exterior columns. -/
private lemma actual_tail_crop (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) :
    pairedColumnTerm c (N + J) S v j = pairedColumnTerm c N S v (j + J) := by
  simp [pairedColumnTerm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The unscaled complete tail energy decreases with its cutoff. -/
private lemma actual_tail_crop_le (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (hs : Summable (pairedColumnTerm c N S v)) :
    (∑' j : ℕ, pairedColumnTerm c (N + J) S v j) ≤
      ∑' j : ℕ, pairedColumnTerm c N S v j := by
  simp_rw [actual_tail_crop]
  exact tsum_comp_le_tsum_of_inj hs
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i j h => Nat.add_right_cancel h)

/-- The coefficient-uniform lower estimate supplies summability at a later
cutoff; literal cropping recovers every original cutoff, including zero. -/
lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ)
    (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) :
    Summable (pairedColumnTerm c N S v) := by
  obtain ⟨_, _, M, hM⟩ :=
    ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower (by omega : 2 ≤ c) S hS
  have hbig : Summable (pairedColumnTerm c (N + M) S v) := by
    change Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((N + M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((N + M + j + 1 : ℕ) : ℤ))‖ ^ 2)
    exact (hM v (N + M) (by omega)).1
  have hshift : Summable (fun j : ℕ => pairedColumnTerm c N S v (j + M)) := by
    convert hbig using 1
    funext j
    exact (actual_tail_crop c N M S v j).symm
  exact Summable.comp_nat_add hshift

/-- Nonzero on the retained finite head implies positive COMPLETE actual
energy at every cutoff, by the uniform tail lower bound. -/
theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) :
    0 < ∑' j : ℕ, pairedColumnTerm c N S v j := by
  have hS : S.Nonempty := by obtain ⟨k, hk, _⟩ := hv; exact ⟨k, hk⟩
  obtain ⟨C, hC, M, hM⟩ :=
    ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower (by omega : 2 ≤ c) S hS
  have hmass : 0 < ∑ k ∈ S, ‖v k‖ ^ 2 := by
    obtain ⟨k, hk, hvk⟩ := hv
    exact (sq_pos_of_pos (norm_pos_iff.mpr hvk)).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (‖v j‖)) hk)
  let K := max N M
  have hNK : N ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have henc : C * (∑ k ∈ S, ‖v k‖ ^ 2) / ((K : ℝ) + 1) ^ (2 * S.card - 1) ≤
        ∑' j : ℕ, pairedColumnTerm c K S v j := by
    simpa only [pairedColumnTerm] using (hM v K hMK).2
  have hlo : 0 < C * (∑ k ∈ S, ‖v k‖ ^ 2) /
      ((K : ℝ) + 1) ^ (2 * S.card - 1) := by positivity
  have hpos : 0 < ∑' j : ℕ, pairedColumnTerm c K S v j := hlo.trans_le henc
  have hcrop := actual_tail_crop_le c N (K - N) S v
    (actual_tail_summable_all hc S hS N v)
  have hsum : N + (K - N) = K := by omega
  rw [hsum] at hcrop
  exact hpos.trans_le hcrop

/-- Exact kernel on the original finite coefficients, including an empty
head and the zero vector. This does not claim injectivity on all Z->C. -/
theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) :
    (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0 := by
  constructor
  · intro hz k hk
    by_contra hvk
    have hp := actual_finite_head_tail_pos hc S N v ⟨k, hk, hvk⟩
    exact hp.ne' hz
  · intro hv
    have hcol : ∀ m : ℤ, couplingColumn c S v m = 0 := by
      intro m
      unfold couplingColumn
      apply Finset.sum_eq_zero
      intro k hk
      rw [hv k hk, mul_zero]
    simp [pairedColumnTerm, hcol]

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
