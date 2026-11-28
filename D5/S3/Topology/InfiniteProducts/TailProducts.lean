/- GID: D5/S3/Topology/InfiniteProducts/TailProducts
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Products of numbers in the unit interval converge along every tail. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Omega original.

Products of numbers in the unit interval converge along every tail. At least
one tail has positive limit exactly when the deficits form a summable series.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BigOperators Topology

namespace Omega.Analysis.TailProducts

/-- The product of (n) consecutive factors beginning at (s). -/
def tailPrefix (r : ℕ → ℝ) (s n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, r (s + k)

/-- The decreasing limit of the finite products along the tail from (s). -/
noncomputable def tailProduct (r : ℕ → ℝ) (s : ℕ) : ℝ :=
  ⨅ n, tailPrefix r s n

variable (r : ℕ → ℝ) (hr : ∀ k, r k ∈ Set.Icc (0 : ℝ) 1)

include hr

theorem tailPrefix_nonneg (s n : ℕ) : 0 ≤ tailPrefix r s n :=
  Finset.prod_nonneg fun k _ => (hr (s + k)).1

private theorem tailPrefix_antitone (s : ℕ) : Antitone (tailPrefix r s) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [tailPrefix, Finset.prod_range_succ]
  exact mul_le_of_le_one_right (tailPrefix_nonneg r hr s n) (hr (s + n)).2

theorem tailPrefix_tendsto (s : ℕ) :
    Tendsto (tailPrefix r s) atTop (𝓝 (tailProduct r s)) :=
  tendsto_atTop_ciInf (tailPrefix_antitone r hr s)
    ⟨0, by rintro _ ⟨n, rfl⟩; exact tailPrefix_nonneg r hr s n⟩

/-- The deficit of a finite product is bounded by the sum of the individual deficits. -/
theorem one_sub_tailPrefix_le_sum (s n : ℕ) :
    1 - tailPrefix r s n ≤ ∑ k ∈ Finset.range n, (1 - r (s + k)) := by
  induction n with
  | zero => simp [tailPrefix]
  | succ n ih =>
    have hp : tailPrefix r s n ≤ 1 := by
      simpa [tailPrefix] using tailPrefix_antitone r hr s (Nat.zero_le n)
    have h := mul_le_of_le_one_left (sub_nonneg.mpr (hr (s + n)).2) hp
    rw [Finset.sum_range_succ, tailPrefix, Finset.prod_range_succ]
    change 1 - tailPrefix r s n * r (s + n) ≤ _ + _
    linarith only [ih, h]

private theorem tailPrefix_le_exp (s n : ℕ) :
    tailPrefix r s n ≤ Real.exp (-(∑ k ∈ Finset.range n, (1 - r (s + k)))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun k _ => (hr (s + k)).1)
  intro k _
  simpa only [neg_sub, sub_add_cancel] using Real.add_one_le_exp (r (s + k) - 1)

theorem tailProduct_nonneg (s : ℕ) : 0 ≤ tailProduct r s :=
  ge_of_tendsto' (tailPrefix_tendsto r hr s) (tailPrefix_nonneg r hr s)

/-- Divergence forces the product of every tail to vanish, including tails with zero factors. -/
theorem tailProduct_eq_zero_of_not_summable
    (h : ¬ Summable (fun k => 1 - r k)) (s : ℕ) : tailProduct r s = 0 := by
  have hs : ¬ Summable (fun k => 1 - r (s + k)) := by
    simpa only [Nat.add_comm s] using
      (summable_nat_add_iff (f := fun k => 1 - r k) s).not.mpr h
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => sub_nonneg.mpr (hr (s + k)).2)).mp hs
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum)
  exact le_antisymm (le_of_tendsto_of_tendsto' (tailPrefix_tendsto r hr s) hexp
    (tailPrefix_le_exp r hr s)) (tailProduct_nonneg r hr s)

private theorem exists_tailProduct_pos_of_summable (h : Summable (fun k => 1 - r k)) :
    ∃ s, 0 < tailProduct r s := by
  let sums : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (1 - r k)
  obtain ⟨s, hs⟩ := Metric.cauchySeq_iff.mp h.hasSum.tendsto_sum_nat.cauchySeq
    (1 / 2) (by norm_num)
  refine ⟨s, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) ?_⟩
  apply ge_of_tendsto' (tailPrefix_tendsto r hr s)
  intro n
  have hd : dist (sums (s + n)) (sums s) < 1 / 2 :=
    hs (s + n) (Nat.le_add_right s n) s le_rfl
  have hsum : sums (s + n) - sums s = ∑ k ∈ Finset.range n, (1 - r (s + k)) := by
    dsimp [sums]
    rw [Finset.sum_range_add]
    ring
  rw [Real.dist_eq, hsum] at hd
  linarith only [one_sub_tailPrefix_le_sum r hr s n, (abs_lt.mp hd).2]

/-- A zero at one site can kill a prefix product. Divergence is characterized by
vanishing of every tail product. -/
theorem all_tail_products_zero_iff :
    (∀ s, tailProduct r s = 0) ↔ ¬ Summable (fun k => 1 - r k) := by
  refine ⟨fun hz hs => ?_, tailProduct_eq_zero_of_not_summable r hr⟩
  obtain ⟨s, hs⟩ := exists_tailProduct_pos_of_summable r hr hs
  exact hs.ne' (hz s)

theorem tailProduct_zero_iff :
    tailProduct r 0 = 0 ↔ (∃ k, r k = 0) ∨ ¬ Summable (fun k => 1 - r k) := by
  constructor
  · intro hz
    by_contra! h
    obtain ⟨s, hs⟩ := exists_tailProduct_pos_of_summable r hr h.2
    have hp : 0 < tailPrefix r 0 s :=
      Finset.prod_pos fun k _ => lt_of_le_of_ne (hr (0 + k)).1 (Ne.symm (h.1 (0 + k)))
    have hsplit (n : ℕ) :
        tailPrefix r 0 (s + n) = tailPrefix r 0 s * tailPrefix r s n := by
      simp only [tailPrefix, Nat.zero_add, Finset.prod_range_add]
    have hlim := (tailPrefix_tendsto r hr 0).comp (show Tendsto (fun n : ℕ => s + n) atTop atTop by
      simpa only [Nat.add_comm s] using tendsto_add_atTop_nat s)
    have hlim' := (tailPrefix_tendsto r hr s).const_mul (tailPrefix r 0 s)
    simp only [Function.comp_def] at hlim
    simp_rw [hsplit] at hlim
    exact (mul_pos hp hs).ne' ((tendsto_nhds_unique hlim' hlim).trans hz)
  · rintro (⟨k, hk⟩ | h)
    · have hp : tailPrefix r 0 (k + 1) = 0 := by
        rw [tailPrefix, Finset.prod_range_succ, Nat.zero_add, hk, mul_zero]
      have hle : tailProduct r 0 ≤ tailPrefix r 0 (k + 1) :=
        ciInf_le ⟨0, by rintro _ ⟨n, rfl⟩; exact tailPrefix_nonneg r hr 0 n⟩ _
      exact le_antisymm (hp ▸ hle) (tailProduct_nonneg r hr 0)
    · exact tailProduct_eq_zero_of_not_summable r hr h 0

end Omega.Analysis.TailProducts
