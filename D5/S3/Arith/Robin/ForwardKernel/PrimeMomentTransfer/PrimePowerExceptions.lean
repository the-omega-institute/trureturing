/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centered von Mangoldt quadratic relation has sparse prime-power exceptions. -/

import Mathlib.NumberTheory.Chebyshev
import D5.S3.Weil.ZetaTail.TailCount

/-! Arithmetic bounds for collision reduction and logarithm replacement. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

open Finset ArithmeticFunction

noncomputable section
set_option autoImplicit false

/-- Outside proper prime powers, the centered von Mangoldt value satisfies a quadratic relation. -/
theorem vonMangoldt_sub_one_quadratic (m : ℕ)
    (hm : ¬(IsPrimePow m ∧ ¬Nat.Prime m)) :
    (vonMangoldt m - 1)^2 =
      (Real.log m - 2) * (vonMangoldt m - 1) + (Real.log m - 1) := by
  by_cases hp : Nat.Prime m
  · rw [vonMangoldt_apply_prime hp]
    ring
  · rw [vonMangoldt_eq_zero_iff.mpr (fun h => hm ⟨h, hp⟩)]
    ring

private theorem log_two_le_vonMangoldt {m : ℕ} (hm : IsPrimePow m) :
    Real.log 2 ≤ vonMangoldt m := by
  rw [vonMangoldt_apply, ite_eq_left hm]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.minFac_prime hm.ne_one).two_le)

/-- Proper prime powers up to a real cutoff number at most a constant times its square root. -/
theorem proper_prime_power_count_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      (((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n)).card : ℝ) ≤
        C * Real.sqrt x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C 0 / Real.log 2, div_nonneg (le_max_right _ _) hlog.le, ?_⟩
  intro x _hx
  let s := (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n)
  have hlower : (s.card : ℝ) * Real.log 2 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    calc
      (s.card : ℝ) * Real.log 2 = ∑ _n ∈ s, Real.log 2 := by simp
      _ ≤ ∑ n ∈ s, vonMangoldt n := by
        apply Finset.sum_le_sum
        intro n hn
        exact log_two_le_vonMangoldt (Finset.mem_filter.mp hn).2.1
      _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Prime n),
          vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, _, hp⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_filter.mpr ⟨hn, hp⟩
        · intro n _ _
          exact vonMangoldt_nonneg
      _ = Chebyshev.psi x - Chebyshev.theta x :=
        (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm
  have hupper : Chebyshev.psi x - Chebyshev.theta x ≤ max C 0 * Real.sqrt x :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  calc
    (s.card : ℝ) ≤ (max C 0 * Real.sqrt x) / Real.log 2 :=
      (le_div_iff₀ hlog).mpr (hlower.trans hupper)
    _ = (max C 0 / Real.log 2) * Real.sqrt x := by ring

private theorem log_nat_add_sub_le_div (n d : ℕ) (hn : 0 < (n : ℝ)) :
    |Real.log ((n + d : ℕ) : ℝ) - Real.log n| ≤ (d : ℝ) / n := by
  rw [Nat.cast_add, abs_of_nonneg (sub_nonneg.mpr
    (Real.log_le_log hn (le_add_of_nonneg_right (Nat.cast_nonneg d))))]
  have h := Zeta23.Tail.log_add_le_log_add_div hn (Nat.cast_nonneg d)
  linarith

/-- A bounded positive shift changes the logarithm by at most the shift cap divided by the scale. -/
theorem log_shift_bound (N H M : ℝ) (n d : ℕ) (hN : 0 < N)
    (_hH : 0 ≤ H) (_hM : 0 ≤ M) (hn : N ≤ n) (hd : (d : ℝ) ≤ M * H) :
    |Real.log ((n+d : ℕ) : ℝ) - Real.log n| ≤ M * H / N := by
  have hnpos : 0 < (n : ℝ) := hN.trans_le hn
  calc
    |Real.log ((n+d : ℕ) : ℝ) - Real.log n| ≤ (d : ℝ) / n :=
      log_nat_add_sub_le_div n d hnpos
    _ ≤ (d : ℝ) / N := div_le_div_of_nonneg_left (Nat.cast_nonneg d) hN hn
    _ ≤ M * H / N := div_le_div_of_nonneg_right hd hN.le

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
