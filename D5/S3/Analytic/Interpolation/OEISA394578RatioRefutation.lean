/- GID: D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Interpolation/OEISA394578RatioRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.claim; result=D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.result; claim=D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.claim
   digest: The native moving-point interpolation sequence cannot have ratio limit one quarter. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#15665; Refuted)
Direct frozen-project dependencies: none.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

namespace D5.S3.Analytic.Interpolation.OEISA394578RatioRefutation

open Polynomial Filter
open scoped BigOperators Topology

/-- The rational Lagrange interpolant through (1,0) and (k,1), 2 <= k <= n+1. -/
noncomputable def p (n : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Finset.range (n + 1)) (fun i : ℕ => (i : ℚ) + 1)
    (fun i => if i = 0 then 0 else 1)

/-- The source normalization, including n=0, with division in the rationals. -/
noncomputable def a (n : ℕ) : ℚ :=
  (4 ^ n / 2) * (p n).eval ((n : ℚ) + 1 / 2)

/-- The printed A394578 ratio-limit assertion, viewed in the real numbers. -/
def claim : Prop :=
  Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 (1 / 4 : ℝ))

/-- The positive tail ratios are bounded below by 4/3, contradicting the asserted limit. -/
theorem result : ¬ claim := by
  classical
  have htail : ∀ n : ℕ, 1 ≤ n →
      (1 / 2 : ℚ) ≤ (p n).eval ((n : ℚ) + 1 / 2) ∧
      (p n).eval ((n : ℚ) + 1 / 2) ≤ 3 / 2 := by
    intro n hn
    let s := Finset.range (n + 1)
    let v : ℕ → ℚ := fun i => (i : ℚ) + 1
    have hinj : Set.InjOn v s := by
      intro i hi j hj hij
      dsimp [v] at hij
      exact_mod_cast (add_right_cancel hij)
    have hz : 0 ∈ s := by simp [s]
    have hp : p n = 1 - Lagrange.basis s v 0 := by
      have hsum := Lagrange.sum_basis hinj ⟨0, hz⟩
      have hex : p n = ∑ i ∈ s.erase 0, Lagrange.basis s v i := by
        simp only [p, Lagrange.interpolate_apply]
        change (∑ i ∈ s, C (if i = 0 then (0 : ℚ) else 1) *
          Lagrange.basis s v i) = _
        rw [← Finset.add_sum_erase _ _ hz]
        simp only [ite_true, map_zero, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro i hi
        simp [(Finset.mem_erase.mp hi).1]
      rw [← Finset.add_sum_erase _ _ hz, ← hex] at hsum
      linear_combination hsum
    have hb : |(Lagrange.basis s v 0).eval ((n : ℚ) + 1 / 2)| ≤ 1 / 2 := by
      have hprod : (Lagrange.basis s v 0).eval ((n : ℚ) + 1 / 2) =
          ∏ j ∈ Finset.range n, (((n : ℚ) - (j : ℚ) - 3 / 2) / (-(j + 1 : ℚ))) := by
        simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor,
          eval_mul, eval_C, eval_sub, eval_X]
        simp only [s, v, Nat.cast_zero, zero_add]
        have he : (Finset.range (n + 1)).erase 0 = Finset.Ico 1 (n + 1) := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
          omega
        rw [he, Finset.prod_Ico_eq_prod_range]
        simp only [Nat.add_sub_cancel]
        apply Finset.prod_congr rfl
        intro j hj
        push_cast
        ring
      have hnum : (∏ j ∈ Finset.range n, |(n : ℚ) - (j : ℚ) - 3 / 2|) =
          ∏ j ∈ Finset.range n, |(j : ℚ) - 1 / 2| := by
        rw [← Finset.prod_range_reflect (fun j : ℕ => |(j : ℚ) - 1 / 2|) n]
        apply Finset.prod_congr rfl
        intro j hj
        have hjn : j ≤ n - 1 := by have := Finset.mem_range.mp hj; omega
        rw [Nat.cast_sub hjn, Nat.cast_sub hn]
        congr 1
        ring
      have hden : 0 < ∏ j ∈ Finset.range n, (j + 1 : ℚ) := by
        apply Finset.prod_pos
        intro j hj
        positivity
      have hest : (∏ j ∈ Finset.range n, |(j : ℚ) - 1 / 2|) ≤
          (1 / 2 : ℚ) * ∏ j ∈ Finset.range n, (j + 1 : ℚ) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        rw [Finset.prod_range_succ', Finset.prod_range_succ']
        norm_num
        rw [mul_comm _ (1 / 2 : ℚ)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          rw [abs_of_nonneg (by have := Nat.cast_nonneg (α := ℚ) i; linarith)]
          norm_num
          linarith
      rw [hprod, Finset.abs_prod]
      simp_rw [abs_div, abs_neg]
      have hdabs : ∀ j : ℕ, |(j : ℚ) + 1| = (j : ℚ) + 1 := by
        intro j
        exact abs_of_pos (by positivity)
      simp_rw [hdabs]
      rw [Finset.prod_div_distrib, hnum]
      exact (div_le_iff₀ hden).mpr hest
    rw [hp, eval_sub, eval_one]
    rcases abs_le.mp hb with ⟨hl, hu⟩
    constructor <;> linarith
  have hratio : ∀ n : ℕ, 1 ≤ n →
      (4 / 3 : ℝ) ≤ (a (n + 1) : ℝ) / (a n : ℝ) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := htail n hn
    obtain ⟨hslo, hshi⟩ := htail (n + 1) (by omega)
    have hpow : (0 : ℚ) < 4 ^ n / 2 := by positivity
    have hpos : (0 : ℚ) < a n := by
      unfold a
      exact mul_pos hpow (by linarith)
    have hq : (4 / 3 : ℚ) ≤ a (n + 1) / a n := by
      apply (le_div_iff₀ hpos).mpr
      unfold a
      rw [pow_succ]
      nlinarith
    have hcast : ((4 / 3 : ℚ) : ℝ) ≤ ((a (n + 1) / a n : ℚ) : ℝ) :=
      Rat.cast_le.mpr hq
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcast
  intro hc
  have hlimit := ge_of_tendsto hc (Filter.eventually_atTop.2 ⟨1, hratio⟩)
  norm_num at hlimit

end D5.S3.Analytic.Interpolation.OEISA394578RatioRefutation
