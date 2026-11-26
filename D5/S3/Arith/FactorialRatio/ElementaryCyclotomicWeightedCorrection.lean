/- GID: D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt]
   utility: none
   digest: Weighted prime-power correction and sampled Chebyshev transfer. -/

module

import Batteries.Tactic.OpenPrivate
public import D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
import all D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact weighted carry identity and factorial-corrected sampled Chebyshev error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

namespace D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection

open Finset ElementaryCyclotomicGcd ElementaryCyclotomicCorrection
open scoped BigOperators Nat
open private mem_levels_iff prime_power_cases level_balance log_prod_nat
  from D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd

/-- Read a coefficient at each prime-power level with its own weight. -/
noncomputable def primePowerReadout (w : ℕ → ℝ) (X : ℕ) (f : ℕ → ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, ∑ t ∈ levels p X, (f (p ^ t) : ℝ) * (w (p ^ t) * Real.log p)

private theorem readout_add (w : ℕ → ℝ) (X : ℕ) (f g : ℕ → ℕ) :
    primePowerReadout w X (fun r => f r + g r) =
      primePowerReadout w X f + primePowerReadout w X g := by
  simp only [primePowerReadout, Nat.cast_add, add_mul, sum_add_distrib]

private theorem readout_nonneg (w : ℕ → ℝ) (X : ℕ) (f : ℕ → ℕ)
    (hw : ∀ r, 0 ≤ w r) : 0 ≤ primePowerReadout w X f := by
  exact sum_nonneg fun p _ => sum_nonneg fun t _ =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hw (p ^ t)) (Real.log_natCast_nonneg p))

/-- Weighted Chebyshev sum at an integer argument, indexed by prime powers. -/
noncomputable def weightedPsi (w : ℕ → ℝ) (x : ℕ) : ℝ :=
  primePowerReadout w x (fun _ => 1)

private theorem weightedPsi_pad (w : ℕ → ℝ) {x X : ℕ} (hx : x ≤ X) :
    weightedPsi w x = primePowerReadout w X (fun r => if r ≤ x then 1 else 0) := by
  unfold weightedPsi primePowerReadout
  symm
  rw [← sum_subset (s₁ := Nat.primesLE x) (s₂ := Nat.primesLE X)]
  · refine sum_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    rw [← sum_subset (s₁ := levels p x) (s₂ := levels p X)]
    · exact sum_congr rfl fun t ht => by simp [((mem_levels_iff hprime).mp ht).2]
    · intro t ht
      obtain ⟨ht1, htx⟩ := (mem_levels_iff hprime).mp ht
      exact (mem_levels_iff hprime).mpr ⟨ht1, htx.trans hx⟩
    · intro t ht htx
      have ht1 := ((mem_levels_iff hprime).mp ht).1
      exact by simp [show ¬ p ^ t ≤ x from fun h => htx ((mem_levels_iff hprime).mpr ⟨ht1, h⟩)]
  · intro p hp
    obtain ⟨hpx, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpx.trans hx, hprime⟩
  · intro p hp hpx
    have hprime := Nat.prime_of_mem_primesLE hp
    have hlt : x < p := lt_of_not_ge fun h => hpx (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
    refine sum_eq_zero fun t ht => ?_
    have ht1 := ((mem_levels_iff hprime).mp ht).1
    have hpt : p ≤ p ^ t := by
      simpa only [pow_one] using (Nat.pow_le_pow_iff_right hprime.one_lt).mpr ht1
    simp [not_le.mpr (hlt.trans_le hpt)]

private theorem readout_one (X : ℕ) (f : ℕ → ℕ) :
    primePowerReadout (fun _ => 1) X f =
      Real.log ((∏ p ∈ Nat.primesLE X, p ^ (∑ t ∈ levels p X, f (p ^ t)) : ℕ) : ℝ) := by
  rw [log_prod_nat _ _ (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero)]
  refine sum_congr rfl fun p _ => ?_
  simp only [one_mul, Nat.cast_pow, Real.log_pow, Nat.cast_sum, sum_mul]

/-- This levelwise readout is the usual weighted von Mangoldt sum. -/
theorem weightedPsi_eq_sum_vonMangoldt (w : ℕ → ℝ) (x : ℕ) :
    weightedPsi w x = ∑ n ∈ Ioc 0 x, w n * ArithmeticFunction.vonMangoldt n := by
  classical
  let s := (Nat.primesLE x).sigma (fun p => levels p x)
  let F := fun n => w n * ArithmeticFunction.vonMangoldt n
  calc
    _ = ∑ a ∈ s, w (a.1 ^ a.2) * Real.log a.1 := by
      unfold weightedPsi primePowerReadout
      dsimp [s]
      rw [Finset.sum_sigma]
      simp
    _ = ∑ n ∈ (Ioc 0 x).filter IsPrimePow, F n := by
      refine sum_bij (fun a _ => a.1 ^ a.2) ?_ ?_ ?_ ?_
      · intro a ha
        obtain ⟨hp, ht⟩ := mem_sigma.mp ha
        have hprime := Nat.prime_of_mem_primesLE hp
        have hlevel := (mem_levels_iff hprime).mp ht
        exact mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨pow_pos hprime.pos _, hlevel.2⟩,
            (isPrimePow_nat_iff _).mpr ⟨a.1, a.2, hprime, hlevel.1, rfl⟩⟩
      · intro a ha b hb hab
        obtain ⟨hp, ht⟩ := mem_sigma.mp ha
        obtain ⟨hq, hu⟩ := mem_sigma.mp hb
        have hprime := Nat.prime_of_mem_primesLE hp
        have hprime' := Nat.prime_of_mem_primesLE hq
        have ht0 : a.2 ≠ 0 := by have := ((mem_levels_iff hprime).mp ht).1; omega
        have hu0 : b.2 ≠ 0 := by have := ((mem_levels_iff hprime').mp hu).1; omega
        obtain ⟨h₁, h₂⟩ := Nat.Prime.pow_inj' hprime hprime' ht0 hu0 hab
        cases a
        cases b
        simp_all
      · intro n hn
        obtain ⟨hnrange, hnpow⟩ := mem_filter.mp hn
        obtain ⟨p, t, hp, ht, rfl⟩ := (isPrimePow_nat_iff n).mp hnpow
        have hp' : p ≤ p ^ t := by
          simpa only [pow_one] using (Nat.pow_le_pow_iff_right hp.one_lt).mpr ht
        have hpx := (mem_Ioc.mp hnrange).2
        exact ⟨⟨p, t⟩, mem_sigma.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hp'.trans hpx, hp⟩, (mem_levels_iff hp).mpr ⟨ht, hpx⟩⟩, rfl⟩
      · intro a ha
        obtain ⟨hp, ht⟩ := mem_sigma.mp ha
        have hprime := Nat.prime_of_mem_primesLE hp
        have hpos := ((mem_levels_iff hprime).mp ht).1
        simp only [F, ArithmeticFunction.vonMangoldt_apply_pow (by omega : a.2 ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hprime]
    _ = _ := by
      refine sum_subset (filter_subset _ _) fun n hn h => ?_
      have hnp : ¬ IsPrimePow n := fun hn' => h (mem_filter.mpr ⟨hn, hn'⟩)
      simp [F, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp]

private theorem weightedPsi_one (x : ℕ) :
    weightedPsi (fun _ => 1) x = Chebyshev.psi (x : ℝ) := by
  rw [Chebyshev.psi_eq_sum_mul_log_prime]
  unfold weightedPsi primePowerReadout
  refine sum_congr rfl fun p _ => ?_
  simp [levels, Nat.card_Ico]

private theorem readout_le_mul_one (w : ℕ → ℝ) (W : ℝ) (X : ℕ) (f : ℕ → ℕ)
    (hw : ∀ r, w r ≤ W) :
    primePowerReadout w X f ≤ W * primePowerReadout (fun _ => 1) X f := by
  simp only [primePowerReadout, mul_sum, one_mul]
  refine sum_le_sum fun p _ => sum_le_sum fun t _ => ?_
  calc
    _ ≤ (f (p ^ t) : ℝ) * (W * Real.log p) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hw _) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg _)
    _ = _ := by ring

private def rowCoefficient (N r : ℕ) : ℕ :=
  (∑ i ∈ range (N + 1), carry r i) +
    ∑ j ∈ range (N + 1), if r ≤ cutoff N j then carry r j else 0

private def factorialCoefficient (N r : ℕ) : ℕ :=
  (if r = 2 then N else 0) + (if r % 2 = 1 then N / r else 0)

/-- Weighted row and gcd carry logarithm (B_w). -/
noncomputable def weightedB (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  primePowerReadout w (4 * N + 1) (rowCoefficient N)

/-- Exact weighted correction (K_w). Level two has count (N), and odd levels have
their own factorial floors. Higher powers of two have zero coefficient. -/
noncomputable def weightedK (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  primePowerReadout w (4 * N + 1) (factorialCoefficient N)

/-- Weighted logarithm of the residual indicator product. -/
noncomputable def weightedIndicator (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  primePowerReadout w (4 * N + 1) (levelIndicator N)

private theorem sampled_readout (w : ℕ → ℝ) {X : ℕ} (s : Finset ℕ) (x : ℕ → ℕ)
    (hx : ∀ i ∈ s, x i ≤ X) :
    (∑ i ∈ s, weightedPsi w (x i)) =
      primePowerReadout w X (fun r => ∑ i ∈ s, if r ≤ x i then 1 else 0) := by
  calc
    _ = ∑ i ∈ s, primePowerReadout w X (fun r => if r ≤ x i then 1 else 0) :=
      sum_congr rfl fun i hi => weightedPsi_pad w (hx i hi)
    _ = _ := by
      simp only [primePowerReadout, Nat.cast_sum, sum_mul]
      rw [sum_comm (s := s)]
      refine sum_congr rfl fun p _ => ?_
      exact sum_comm

/-- The coefficient identity holds before imposing any size or sign condition on the weights. -/
theorem weightedB_add_weightedK_add_weightedIndicator (w : ℕ → ℝ) (N : ℕ) :
    weightedB w N + weightedK w N + weightedIndicator w N =
      ∑ i ∈ range (N + 1), weightedPsi w (4 * i + 1) := by
  unfold weightedB weightedK weightedIndicator
  rw [← readout_add, ← readout_add, sampled_readout w (X := 4 * N + 1) (range (N + 1)) (fun i => 4 * i + 1)
    (fun i hi => by have := mem_range.mp hi; omega)]
  refine sum_congr rfl fun p hp => sum_congr rfl fun t ht => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have ht1 := ((mem_levels_iff hprime).mp ht).1
  have hc := prime_power_cases hprime ht1
  have hb := level_balance N _ hc.1 hc.2
  have hd := levelDeficit_prime_pow N hprime ht1
  have hf : factorialCoefficient N (p ^ t) + levelIndicator N (p ^ t) =
      levelDeficit N (p ^ t) := by
    rcases hprime.eq_two_or_odd with rfl | ho
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      simpa [factorialCoefficient, pow_succ] using hd.symm
    · have hn : p ≠ 2 := by omega
      have ho' : p ^ t % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr ho).pow)
      simpa only [factorialCoefficient, ho', ite_true, hn, ite_false] using hd.symm
  have he :
      rowCoefficient N (p ^ t) + factorialCoefficient N (p ^ t) + levelIndicator N (p ^ t) =
        ∑ i ∈ range (N + 1), if p ^ t ≤ 4 * i + 1 then 1 else 0 := by
    rw [add_assoc, hf]
    unfold levelDeficit rowCoefficient
    omega
  dsimp only
  rw [he]

/-- Explicit bound on the weighted residual indicator. -/
private theorem weightedIndicator_bounds (w : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ W) (N : ℕ) :
    0 ≤ weightedIndicator w N ∧ weightedIndicator w N ≤ W * ((4 * (N : ℝ) + 1) * Real.log 4) := by
  refine ⟨readout_nonneg w _ _ hw₀, ?_⟩
  exact (readout_le_mul_one w W _ _ hw₁).trans
    (mul_le_mul_of_nonneg_left (by rw [readout_one]; exact (log_RStar_bounds N).2) hW)

private def boundaryCoefficient (N r : ℕ) : ℕ :=
  ∑ i ∈ range (N + 1), if r = 4 * i + 1 then 1 else 0

private theorem boundaryCoefficient_le_one (N r : ℕ) : boundaryCoefficient N r ≤ 1 := by
  unfold boundaryCoefficient
  by_cases h : ∃ i ∈ range (N + 1), r = 4 * i + 1
  · obtain ⟨i, hi, hr⟩ := h
    rw [sum_eq_single_of_mem i hi]
    · simp [hr]
    · intro j _ hj
      exact ite_eq_right (by omega)
  · exact (sum_eq_zero fun i hi => ite_eq_right fun hr => h ⟨i, hi, hr⟩).le.trans (by decide)

private theorem sampled_boundary_bounds (w : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ W) (N : ℕ) :
    let d := (∑ i ∈ range (N + 1), weightedPsi w (4 * i + 1)) -
      ∑ i ∈ range (N + 1), weightedPsi w (4 * i)
    0 ≤ d ∧ d ≤ W * Chebyshev.psi ((4 * N + 1 : ℕ) : ℝ) := by
  let X := 4 * N + 1
  let s := range (N + 1)
  have h₁ : ∀ i ∈ s, 4 * i + 1 ≤ X := fun i hi => by
    have := mem_range.mp hi
    dsimp [X]
    omega
  have h₀ : ∀ i ∈ s, 4 * i ≤ X := fun i hi => by have := h₁ i hi; omega
  have hsplit :
      (∑ i ∈ s, weightedPsi w (4 * i + 1)) =
        (∑ i ∈ s, weightedPsi w (4 * i)) + primePowerReadout w X (boundaryCoefficient N) := by
    rw [sampled_readout w s _ h₁, sampled_readout w s _ h₀, ← readout_add]
    refine sum_congr rfl fun p _ => sum_congr rfl fun t _ => ?_
    have hcoeff :
        (∑ i ∈ s, if p ^ t ≤ 4 * i + 1 then (1 : ℕ) else 0) =
          (∑ i ∈ s, if p ^ t ≤ 4 * i then (1 : ℕ) else 0) + boundaryCoefficient N (p ^ t) := by
      rw [boundaryCoefficient, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      split_ifs <;> omega
    dsimp only
    rw [hcoeff]
  change 0 ≤ (∑ i ∈ s, _) - (∑ i ∈ s, _) ∧
    (∑ i ∈ s, _) - (∑ i ∈ s, _) ≤ W * Chebyshev.psi (X : ℝ)
  rw [hsplit, add_sub_cancel_left]
  refine ⟨readout_nonneg w _ _ hw₀, (readout_le_mul_one w W _ _ hw₁).trans ?_⟩
  rw [← weightedPsi_one]
  apply mul_le_mul_of_nonneg_left _ hW
  refine sum_le_sum fun p _ => sum_le_sum fun t _ => ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast boundaryCoefficient_le_one N (p ^ t))
    (by simpa only [one_mul] using Real.log_natCast_nonneg p)

/-- An explicit linear transfer error at the even mesh points. -/
theorem corrected_weighted_sample_error (w : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ W) (N : ℕ) :
    |weightedB w N + weightedK w N - ∑ i ∈ range (N + 1), weightedPsi w (4 * i)| ≤
      W * ((4 * (N : ℝ) + 1) * (Real.log 4 + 4)) := by
  have hi := weightedIndicator_bounds w W hW hw₀ hw₁ N
  have hb := sampled_boundary_bounds w W hW hw₀ hw₁ N
  dsimp only at hb
  have he := weightedB_add_weightedK_add_weightedIndicator w N
  have hpsi := Chebyshev.psi_le_const_mul_self
    (show 0 ≤ ((4 * N + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)
  have hu := mul_le_mul_of_nonneg_left hpsi hW
  push_cast at hb hu
  rw [mul_comm (Real.log 4 + 4) (4 * (N : ℝ) + 1)] at hu
  have hl : W * ((4 * (N : ℝ) + 1) * Real.log 4) ≤
      W * ((4 * (N : ℝ) + 1) * (Real.log 4 + 4)) := by
    gcongr
    linarith
  rw [abs_le]
  constructor <;> nlinarith [hi.1, hi.2, hb.1, hb.2]

end D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
