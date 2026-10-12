/- GID: D5/S3/ArithSums/A400585OddCofactorAsymptotic
   generality: G
   mirror-B: D5/B/S3/ArithSums/A400585OddCofactorAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-cofactor binomial divisor sums have a cubic reciprocal-series asymptotic. -/

/-
proof_shape: bind-only
admission_basis: open-problem-resolution
preregistration: https://github.com/the-omega-institute/trureturing/issues/15574
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field

open Filter Topology Finset

namespace D5.S3.ArithSums.A400585OddCofactorAsymptotic

/-- The odd-cofactor divisor sum. Natural division is exact on positive divisors. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if Odd (n / d) then d.choose 2 else 0

/-- The real-valued sum over the positive prefix. -/
noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, (a n : ℝ)

/-- The real cubic reciprocal series over positive integers. -/
noncomputable def Z3 : ℝ := ∑' q : ℕ, 1 / ((q + 1 : ℕ) : ℝ)^3

set_option maxHeartbeats 1000000 in
-- The limit proof combines finite sums, coercions, and dominated-series estimates.
/-- The summatory ratio tends to one along all natural indices. -/
theorem result : Tendsto (fun N : ℕ => S N / ((7 * Z3 / 48) * (N : ℝ)^3))
    atTop (𝓝 1) := by
  classical
  let f : ArithmeticFunction ℝ := ⟨fun n => if Odd n then 1 else 0, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (n.choose 2 : ℝ), by simp⟩
  have hconv (n : ℕ) : (f * g) n = (a n : ℝ) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun x y => f x * g y)]
    simp [f, g, a, Nat.cast_sum, Nat.cast_ite, mul_comm]
  have hsum (N : ℕ) : S N = ∑ q ∈ Ioc 0 N,
      if Odd q then (((N / q + 1).choose 3 : ℕ) : ℝ) else 0 := by
    simp only [S, ← hconv]
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    apply sum_congr rfl
    intro q hq
    simp only [f, g, ArithmeticFunction.coe_mk]
    by_cases ho : Odd q
    · simp only [if_pos ho, one_mul]
      have hs (m : ℕ) : (∑ d ∈ Ioc 0 m, d.choose 2) = (m + 1).choose 3 := by
        rw [← Nat.sum_Icc_choose m 2]
        symm
        apply sum_subset (by intro x hx; simp only [mem_Icc, mem_Ioc] at *; omega)
        intro x hx hnot
        simp only [mem_Ioc, mem_Icc] at *
        have : x = 1 := by omega
        simp [this]
      exact_mod_cast hs (N / q)
    · simp [ho]
  have hc (m : ℕ) : 6 * (((m + 1).choose 3 : ℕ) : ℝ) = (m : ℝ)^3 - m := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.add_one_mul_choose_eq m 2)
    push_cast at h
    rw [Nat.cast_choose_two] at h
    nlinarith
  let F : ℕ → ℕ → ℝ := fun N q =>
    if Odd q then (((N / q + 1).choose 3 : ℕ) : ℝ) / (N : ℝ)^3 else 0
  let L : ℕ → ℝ := fun q => if Odd q then 1 / (6 * (q : ℝ)^3) else 0
  have hp : Summable (fun q : ℕ => 1 / (q : ℝ)^3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hz : Z3 = ∑' q : ℕ, 1 / (q : ℝ)^3 := by
    simpa [Z3] using (hp.sum_add_tsum_nat_add 1)
  have hZpos : 0 < Z3 := by
    rw [hz]
    exact hp.tsum_pos (fun q => by positivity) 1 (by norm_num)
  have hpoint (q : ℕ) : Tendsto (fun N => F N q) atTop (𝓝 (L q)) := by
    by_cases ho : Odd q
    · have hq : 0 < q := by obtain ⟨k, hk⟩ := ho; omega
      have hqr : (q : ℝ) ≠ 0 := by positivity
      have hd : Tendsto (fun N : ℕ => ((N / q : ℕ) : ℝ) / N) atTop (𝓝 (1 / (q : ℝ))) := by
        convert (tendsto_nat_floor_mul_div_atTop (show 0 ≤ 1 / (q : ℝ) by positivity)).comp
          tendsto_natCast_atTop_atTop using 1
        funext N
        simp only [Function.comp_apply]
        rw [show (1 / (q : ℝ)) * (N : ℝ) = (N : ℝ) / q by ring, Nat.floor_div_eq_div]
      have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hh := ((hd.pow 3).sub (hd.mul (hi.pow 2))).div_const 6
      apply Tendsto.congr' (f₁ := fun N : ℕ =>
        ((((N / q : ℕ) : ℝ) / N)^3 -
          (((N / q : ℕ) : ℝ) / N) * (1 / (N : ℝ))^2) / 6)
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hNr : (N : ℝ) ≠ 0 := by positivity
        dsimp [F]
        rw [if_pos ho]
        have hh := hc (N / q)
        field_simp
        nlinarith [hh]
      · convert hh using 1
        simp only [L, if_pos ho, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
        field_simp
    · simp [F, L, ho]
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ‖F N q‖ ≤ 1 / (q : ℝ)^3 := by
    filter_upwards [eventually_ge_atTop 1] with N hN q
    have hNr : 0 < (N : ℝ) := by positivity
    by_cases ho : Odd q
    · have hq : 0 < q := by obtain ⟨k, hk⟩ := ho; omega
      have hqr : 0 < (q : ℝ) := by positivity
      have hm : 0 ≤ ((N / q : ℕ) : ℝ) := by positivity
      have hmq : ((N / q : ℕ) : ℝ) * q ≤ N := by
        exact_mod_cast Nat.div_mul_le_self N q
      have hr : ((N / q : ℕ) : ℝ) / N ≤ 1 / (q : ℝ) := by
        apply (div_le_div_iff₀ hNr hqr).mpr
        simpa using hmq
      have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ ((N / q : ℕ) : ℝ) / N) hr 3
      dsimp [F]
      rw [if_pos ho, abs_of_nonneg (by positivity)]
      have hcN := hc (N / q)
      have hle : (((N / q + 1).choose 3 : ℕ) : ℝ) ≤ ((N / q : ℕ) : ℝ)^3 := by
        nlinarith [pow_nonneg hm 3]
      calc
        _ ≤ ((N / q : ℕ) : ℝ)^3 / (N : ℝ)^3 := div_le_div_of_nonneg_right hle (by positivity)
        _ = (((N / q : ℕ) : ℝ) / N)^3 := (div_pow _ _ _).symm
        _ ≤ (1 / (q : ℝ))^3 := hcube
        _ = 1 / (q : ℝ)^3 := by simp
    · simp [F, ho]
  have ht := tendsto_tsum_of_dominated_convergence hp hpoint hbound
  have hfinite (N : ℕ) : (∑' q : ℕ, F N q) = S N / (N : ℝ)^3 := by
    rw [tsum_eq_sum (s := Ioc 0 N)]
    · rw [hsum, sum_div]
      apply sum_congr rfl
      intro q hq
      simp only [F]
      split_ifs <;> simp
    · intro q hq
      by_cases ho : Odd q
      · have hpos : 0 < q := by obtain ⟨k, hk⟩ := ho; omega
        have hNq : N < q := by simp only [mem_Ioc, not_and] at hq; exact Nat.lt_of_not_ge (hq hpos)
        norm_num [F, ho, Nat.div_eq_of_lt hNq, Nat.choose]
      · simp [F, ho]
  have heinj : Function.Injective (fun k : ℕ => 2 * k) := by intro a b h; dsimp at h; omega
  have hoinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by intro a b h; dsimp at h; omega
  have he : Summable (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ)^3) := hp.comp_injective heinj
  have ho : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ)^3) := hp.comp_injective hoinj
  have heval : (∑' k : ℕ, 1 / ((2 * k : ℕ) : ℝ)^3) = Z3 / 8 := by
    rw [hz, ← tsum_div_const]
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · push_cast
      field_simp
      ring
  have hovalue : (∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ)^3) = 7 * Z3 / 8 := by
    have h := tsum_even_add_odd (f := fun q : ℕ => 1 / (q : ℝ)^3) he ho
    change (∑' k : ℕ, 1 / ((2 * k : ℕ) : ℝ)^3) +
      (∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ)^3) =
      (∑' k : ℕ, 1 / (k : ℝ)^3) at h
    rw [heval, ← hz] at h
    linarith
  have hLs : Summable L := by
    apply hp.of_norm_bounded
    intro q
    dsimp [L]
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      have : 0 ≤ 1 / (q : ℝ)^3 := by positivity
      calc
        _ = (1 / (q : ℝ)^3) / 6 := by ring
        _ ≤ 1 / (q : ℝ)^3 := by linarith
    · simp
  have hL : (∑' q : ℕ, L q) = 7 * Z3 / 48 := by
    have h := tsum_even_add_odd (hLs.comp_injective heinj) (hLs.comp_injective hoinj)
    have he0 (k : ℕ) : L (2 * k) = 0 := by simp [L, Nat.odd_iff]
    have ho1 (k : ℕ) : L (2 * k + 1) = (1 / ((2 * k + 1 : ℕ) : ℝ)^3) / 6 := by
      simp only [L, if_pos (odd_two_mul_add_one k)]
      ring
    simp_rw [he0, ho1] at h
    rw [tsum_zero, zero_add, tsum_div_const, hovalue] at h
    linarith
  rw [hL] at ht
  have htS : Tendsto (fun N : ℕ => S N / (N : ℝ)^3) atTop (𝓝 (7 * Z3 / 48)) := by
    simpa only [hfinite] using ht
  have hC : 7 * Z3 / 48 ≠ 0 := by positivity
  have hfinal := htS.div_const (7 * Z3 / 48)
  convert hfinal using 1
  · funext N
    ring
  · simp [hC]

end D5.S3.ArithSums.A400585OddCofactorAsymptotic
