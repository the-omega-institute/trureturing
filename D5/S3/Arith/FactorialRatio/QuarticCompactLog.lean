/- GID: D5/S3/Arith/FactorialRatio/QuarticCompactLog
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/QuarticCompactLog
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Explicit quadratic logarithmic gap for the compact factorial gcd. -/

module

public import D5.S3.Arith.FactorialRatio.QuarticPrimeWitness
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev

/-! Quadratic logarithmic compression of the quartic compact factorial gcd. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.CompactFactorialGcd

open Finset Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)

/-- Finite summation by parts for weights with a linear prefix-sum bound. -/
private theorem sum_div_sqrt_le {c : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (h0 : c 0 = 0)
    (hW : ∀ m : ℕ, (∑ k ∈ range (m + 1), c k) ≤ C * (m : ℝ)) (m : ℕ) :
    (∑ k ∈ range (m + 1), c k / Real.sqrt (k : ℝ)) ≤ 2 * C * Real.sqrt m := by
  let W : ℕ → ℝ := fun j => ∑ k ∈ range (j + 1), c k
  let S : ℕ → ℝ := fun j => ∑ k ∈ range (j + 1), c k / Real.sqrt (k : ℝ)
  change ∀ j : ℕ, W j ≤ C * (j : ℝ) at hW
  have hprefix (n : ℕ) :
      S (n + 1) ≤ W (n + 1) / Real.sqrt (n + 1 : ℕ) + C * Real.sqrt (n + 1 : ℕ) := by
    induction n with
    | zero =>
      have hS1 : S 1 = c 1 := by simp [S, h0, Finset.sum_range_succ]
      have hW1 : W 1 = c 1 := by simp [W, h0, Finset.sum_range_succ]
      simpa only [Nat.zero_add, Nat.cast_one, Real.sqrt_one, div_one, mul_one, hS1, hW1]
        using (le_add_of_nonneg_right hC : c 1 ≤ c 1 + C)
    | succ n ih =>
      let k := n + 1
      let x := Real.sqrt (k : ℝ)
      let y := Real.sqrt ((k + 1 : ℕ) : ℝ)
      have hx : 0 < x := Real.sqrt_pos.2 (by dsimp [k]; positivity)
      have hxy : x ≤ y := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
      have hy : 0 < y := hx.trans_le hxy
      have hx2 : x ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
      have hdiff : W k / x - W k / y ≤ C * (y - x) := calc
        _ = W k * ((y - x) / (x * y)) := by field_simp [hx.ne', hy.ne'] <;> ring
        _ ≤ (C * (k : ℝ)) * ((y - x) / (x * y)) :=
          mul_le_mul_of_nonneg_right (hW k) (div_nonneg (sub_nonneg.mpr hxy) (by positivity))
        _ = (x / y) * (C * (y - x)) := by
          rw [← hx2]
          field_simp [hx.ne', hy.ne'] <;> ring
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            ((div_le_one hy).mpr hxy) (mul_nonneg hC (sub_nonneg.mpr hxy))
      change S k ≤ W k / x + C * x at ih
      change S (k + 1) ≤ W (k + 1) / y + C * y
      have hS : S (k + 1) = S k + c (k + 1) / y := Finset.sum_range_succ _ _
      have hWs : W (k + 1) = W k + c (k + 1) := Finset.sum_range_succ _ _
      rw [hS, hWs, add_div]
      linarith only [ih, hdiff, show C * (y - x) = C * y - C * x by ring]
  cases m with
  | zero => simp [h0]
  | succ n =>
    let x := Real.sqrt ((n + 1 : ℕ) : ℝ)
    have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
    have hx2 : x ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have h : W (n + 1) / x ≤ C * x := by
      apply (div_le_iff₀ hx).mpr
      simpa only [← hx2, pow_two, mul_assoc] using hW (n + 1)
    change S (n + 1) ≤ 2 * C * x
    have hp := hprefix n
    change S (n + 1) ≤ W (n + 1) / x + C * x at hp
    linarith only [hp, h]

private theorem sum_log_prime_div_sqrt_le (m : ℕ) :
    (∑ p ∈ primesLE m, Real.log (p : ℝ) / Real.sqrt (p : ℝ)) ≤
      2 * (Real.log 4 + 4) * Real.sqrt (m : ℝ) := by
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log (p : ℝ) else 0
  have hC : 0 ≤ Real.log 4 + 4 := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hW (j : ℕ) : (∑ k ∈ range (j + 1), c k) ≤ (Real.log 4 + 4) * (j : ℝ) := by
    change (∑ k ∈ range (j + 1), if k.Prime then Real.log (k : ℝ) else 0) ≤ _
    rw [← Finset.sum_filter Nat.Prime (fun k => Real.log (k : ℝ)),
      ← Nat.primesLE_eq_filter_range, ← Chebyshev.theta_eq_sum_primesLE_log j]
    exact (Chebyshev.theta_le_psi (j : ℝ)).trans (Chebyshev.psi_le_const_mul_self (by positivity))
  have h := sum_div_sqrt_le (c := c) hC (by simp [c]) hW m
  simp only [c, ite_div, zero_div] at h
  rw [← Finset.sum_filter Nat.Prime (fun k => Real.log (k : ℝ) / Real.sqrt (k : ℝ)),
    ← Nat.primesLE_eq_filter_range] at h
  exact h

/-- At the exact quartic parameters, the compact gcd has logarithmic excess
at most `11 * (log 4 + 4) * r^2` over the tail LCM. -/
public theorem quartic_compact_log_gap (r : ℕ) (hr : 8 ≤ r) :
    let s := (r - 1) * (r - 2)
    let T := tailLCM (r * s + (r - 1)) (r - 1)
    0 ≤ Real.log (selbergGcd r s : ℝ) - Real.log (T : ℝ) ∧
      Real.log (selbergGcd r s : ℝ) - Real.log (T : ℝ) ≤
        11 * (Real.log 4 + 4) * (r : ℝ)^2 := by
  dsimp only
  let s := (r - 1) * (r - 2)
  let H := r * s + (r - 1)
  let T := tailLCM H (r - 1)
  let G := selbergGcd r s
  let Q := G / T
  let C := Real.log 4 + 4
  have hr0 : 0 < r := by omega
  have hC : 0 ≤ C := by dsimp [C]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hs : s < r ^ 2 := quartic_size_lt_sq hr
  have hTG : T ∣ G := by
    simpa only [G, T, H, Nat.add_sub_assoc (show 1 ≤ r by omega)] using
      (compact_factorial_gcd r s (by omega) hs).1
  have hT0 : T ≠ 0 := tail_nonzero _ _
  have hG0 : G ≠ 0 := selbergGcd_ne_zero _ _
  have hQG : Q * T = G := Nat.div_mul_cancel hTG
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hQG
    exact hG0 hQG.symm
  have hgap : Real.log (G : ℝ) - Real.log (T : ℝ) = Real.log (Q : ℝ) := by
    rw [← hQG, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hQ0) (Nat.cast_ne_zero.mpr hT0),
      add_sub_cancel_right]
  change 0 ≤ Real.log (G : ℝ) - Real.log (T : ℝ) ∧
    Real.log (G : ℝ) - Real.log (T : ℝ) ≤ 11 * C * (r : ℝ)^2
  rw [hgap]
  refine ⟨Real.log_nonneg (by exact_mod_cast (Nat.pos_of_ne_zero hQ0 : 1 ≤ Q)), ?_⟩
  have hfac (p : ℕ) : Q.factorization p = G.factorization p - T.factorization p := by
    dsimp only [Q]
    rw [Nat.factorization_div hTG, Finsupp.tsub_apply]
  have hle (p : ℕ) (hp : p.Prime) : T.factorization p ≤ G.factorization p :=
    (Nat.factorization_prime_le_iff_dvd hT0 hG0).mpr hTG p hp
  have hsupp : Q.factorization.support ⊆ primesLE s := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (show p ∈ Q.primeFactors from hp)
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hprime⟩
    by_contra! hsp
    have hw := (quartic_prime_witness hr hprime).2.2 hsp
    have hg := gcd_factorization_le hprime hr0 hw.1
    rw [hw.2] at hg
    have hz : Q.factorization p = 0 := by
      rw [hfac, Nat.sub_eq_zero_of_le (le_trans hg (Nat.zero_le _))]
    exact (Finsupp.mem_support_iff.mp hp) hz
  rw [Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => by simp)]
  let f : ℕ → ℝ := fun p => (Q.factorization p : ℝ) * Real.log (p : ℝ)
  change (∑ p ∈ primesLE s, f p) ≤ _
  have hlog (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlo : (∑ p ∈ (primesLE s).filter (fun p => p ≤ r), f p) ≤ 3 * C * (r : ℝ)^2 := calc
    _ ≤ ∑ p ∈ (primesLE s).filter (fun p => p ≤ r),
          (3 * (r - 1 : ℕ) : ℝ) * ((Nat.log p r : ℝ) * Real.log (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp'
      obtain ⟨hp, hpr⟩ := Finset.mem_filter.mp hp'
      have hprime := Nat.prime_of_mem_primesLE hp
      have hw := (quartic_prime_witness hr hprime).1 hpr
      have hg := (gcd_factorization_le hprime hr0 hw.1).trans hw.2
      change G.factorization p ≤ T.factorization p + 3 * (r - 1) * Nat.log p r at hg
      have hb : Q.factorization p ≤ 3 * (r - 1) * Nat.log p r := by
        rw [hfac]
        exact Nat.sub_le_of_le_add (by simpa only [Nat.add_comm] using hg)
      have hbR : (Q.factorization p : ℝ) ≤ (3 * (r - 1 : ℕ) : ℝ) * (Nat.log p r : ℝ) := by
        exact_mod_cast hb
      dsimp [f]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hbR (hlog p hprime)
    _ ≤ ∑ p ∈ primesLE r,
          (3 * (r - 1 : ℕ) : ℝ) * ((Nat.log p r : ℝ) * Real.log (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hp).2,
          Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1⟩
      · intro p hp _
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hlog p (Nat.prime_of_mem_primesLE hp)))
    _ = (3 * (r - 1 : ℕ) : ℝ) * Chebyshev.psi (r : ℝ) := by
      rw [← Finset.mul_sum, ← Chebyshev.psi_eq_sum_mul_log_prime]
    _ ≤ 3 * C * (r : ℝ)^2 := calc
      _ ≤ (3 * (r - 1 : ℕ) : ℝ) * (C * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by positivity)) (by positivity)
      _ ≤ (3 * (r : ℝ)) * (C * (r : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        linarith
      _ = _ := by ring
  have hhi : (∑ p ∈ (primesLE s).filter (fun p => ¬ p ≤ r), f p) ≤ 8 * C * (r : ℝ)^2 := calc
    _ ≤ ∑ p ∈ (primesLE s).filter (fun p => ¬ p ≤ r),
          4 * (r : ℝ) * (Real.log (p : ℝ) / Real.sqrt (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp'
      obtain ⟨hp, hpr⟩ := Finset.mem_filter.mp hp'
      have hprime := Nat.prime_of_mem_primesLE hp
      obtain ⟨b, hb, hw⟩ := (quartic_prime_witness hr hprime).2.1
        (lt_of_not_ge hpr) (Nat.le_of_mem_primesLE hp)
      have hg : (G.factorization p : ℝ) ≤ ((selbergFactorial r s b).factorization p : ℝ) := by
        exact_mod_cast gcd_factorization_le hprime hr0 hb
      have heq : (Q.factorization p : ℝ) =
          (G.factorization p : ℝ) - (T.factorization p : ℝ) := by
        rw [hfac, Nat.cast_sub (hle p hprime)]
      have hbound : (Q.factorization p : ℝ) ≤ 4 * (r : ℝ) / Real.sqrt (p : ℝ) := by
        linarith only [heq, hg, hw]
      calc
        f p ≤ (4 * (r : ℝ) / Real.sqrt (p : ℝ)) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hbound (hlog p hprime)
        _ = _ := by ring
    _ ≤ ∑ p ∈ primesLE s, 4 * (r : ℝ) * (Real.log (p : ℝ) / Real.sqrt (p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ =>
        mul_nonneg (by positivity)
          (div_nonneg (hlog p (Nat.prime_of_mem_primesLE hp)) (Real.sqrt_nonneg _))
    _ ≤ 4 * (r : ℝ) * (2 * C * Real.sqrt (s : ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_log_prime_div_sqrt_le s) (by positivity)
    _ ≤ 4 * (r : ℝ) * (2 * C * (r : ℝ)) := by
      have hsR : (s : ℝ) ≤ (r : ℝ)^2 := by exact_mod_cast hs.le
      have hsqrt : Real.sqrt (s : ℝ) ≤ (r : ℝ) := by
        simpa only [Real.sqrt_sq (show (0 : ℝ) ≤ r by positivity)] using Real.sqrt_le_sqrt hsR
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity)
    _ = _ := by ring
  rw [← Finset.sum_filter_add_sum_filter_not (primesLE s) (fun p => p ≤ r) f]
  linarith only [hlo, hhi]

end D5.S3.Arith.FactorialRatio.CompactFactorialGcd
