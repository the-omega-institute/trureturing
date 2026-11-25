/- GID: D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyNortonFirstDifference
   mirror-E: none(waiver:symbolic-asymptotic-theorem)
   anchors: []
   utility: none
   digest: Positive values omitted by Norton threshold first differences. -/

import D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
import Mathlib.NumberTheory.Chebyshev

/-! Prime-counting sparsity prevents the first differences from taking every positive value. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter
open scoped Topology

open D5.S3.Arith.OmegaGreedyPermutation (prime)

namespace D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference

open BeriZelinskyQuestion6

/-- Every positive integer occurs as a difference at a positive starting index. -/
def claim : Prop :=
  ∀ m : ℕ, 0 < m → ∃ n ≥ 1, a (n + 1) - a n = m

private lemma not_all_positive_values_of_eventually_double (f : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, 2 * n ≤ f n) :
    ¬ ∀ m : ℕ, 0 < m → ∃ n ≥ 1, f n = m := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  intro hall
  have hsub : Icc 1 (2 * N + 1) ⊆ (Icc 1 N).image f := by
    intro m hm
    obtain ⟨hmpos, hmle⟩ := mem_Icc.mp hm
    obtain ⟨n, hn, hfn⟩ := hall m (by omega)
    apply mem_image.mpr
    refine ⟨n, mem_Icc.mpr ⟨hn, ?_⟩, hfn⟩
    by_cases hNn : N ≤ n
    · have hbound := hN n hNn
      rw [hfn] at hbound
      omega
    · omega
  have hcard := card_le_card hsub
  have hle : 2 * N + 1 ≤ N := by
    simpa using hcard.trans (card_image_le (s := Icc 1 N) (f := f))
  omega

private lemma eventual_double_difference :
    ∀ᶠ n in atTop, 2 * n ≤ a (n + 1) - a n := by
  obtain ⟨c, hc, hbound⟩ := norton_adjacent_cancellation 2 (by norm_num)
  have hbound' : ∀ᶠ n in atTop,
      c * (prime (n - 1) : ℝ) ≤ (a (n + 1) : ℝ) - a n + 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, a] using hbound
  let K : ℝ := Real.log 4 + 1
  have hPtop : Tendsto (fun n : ℕ => (prime (n - 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop.comp
        (tendsto_sub_atTop_nat 1))
  have hcheb := Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)
  have hloglarge := (Real.tendsto_log_atTop.comp hPtop).eventually_ge_atTop (8 * K / c)
  filter_upwards [hbound', hPtop.eventually hcheb, hloglarge,
    eventually_ge_atTop 2] with n hb hpi hl hn
  let P : ℝ := prime (n - 1)
  have hP0 : 0 < P := by
    dsimp [P, prime]
    exact_mod_cast (Nat.prime_nth_prime (n - 1)).pos
  have hP1 : 1 < P := by
    dsimp [P, prime]
    exact_mod_cast (Nat.prime_nth_prime (n - 1)).one_lt
  have hLP : 0 < Real.log P := Real.log_pos hP1
  rw [Nat.floor_natCast] at hpi
  change (Nat.primeCounting (prime (n - 1)) : ℝ) ≤ K * P / Real.log P at hpi
  have hcountNat : n - 1 ≤ Nat.primeCounting (prime (n - 1)) := by
    calc
      n - 1 = Nat.primeCounting' (prime (n - 1)) :=
        (Nat.primeCounting'_nth_eq (n - 1)).symm
      _ ≤ _ := Nat.monotone_primeCounting' (Nat.le_succ _)
  have hcount : (n : ℝ) - 1 ≤ K * P / Real.log P := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hcountNat
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hh
    exact hh.trans hpi
  have hsmall : K / Real.log P ≤ c / 8 := by
    apply (div_le_iff₀ hLP).mpr
    change 8 * K / c ≤ Real.log P at hl
    have hh := (div_le_iff₀ hc).mp hl
    nlinarith
  have hcountsmall : (n : ℝ) - 1 ≤ (c / 8) * P := by
    apply hcount.trans
    calc
      K * P / Real.log P = (K / Real.log P) * P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hP0.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : 4 * (n : ℝ) ≤ c * P := by nlinarith
  have hreal : 2 * (n : ℝ) ≤ (a (n + 1) : ℝ) - a n := by
    change c * P ≤ (a (n + 1) : ℝ) - a n + 1 at hb
    linarith
  have hmono : a n ≤ a (n + 1) := by
    have hh : (a n : ℝ) ≤ a (n + 1) := by linarith
    exact_mod_cast hh
  have hcast : ((2 * n : ℕ) : ℝ) ≤ ((a (n + 1) - a n : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hmono] using hreal
  exact_mod_cast hcast

/-- The positive first differences omit at least one positive integer. -/
theorem result : ¬ claim :=
  not_all_positive_values_of_eventually_double
    (fun n => a (n + 1) - a n) eventual_double_difference

end D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference
