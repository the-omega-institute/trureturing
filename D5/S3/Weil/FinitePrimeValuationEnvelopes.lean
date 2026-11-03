/- GID: D5/S3/Weil/FinitePrimeValuationEnvelopes
   generality: G
   mirror-B: D5/B/S3/Weil/FinitePrimeValuationEnvelopes
   mirror-E: none(waiver:qualitative-asymptotic-estimate)
   anchors: []
   utility: none
   digest: Joint finite-prime Robin upper envelope under bounded valuations. -/

import D5.S3.Weil.PrimeValuationGap
import D5.S3.Weil.GronwallUpperEnvelope
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace D5.S3.Weil.FinitePrimeValuationEnvelopes

open Filter
open scoped BigOperators Topology
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Weil.GronwallUpperEnvelope

local notation "Z" => (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℝ) / n)

/-- Raising every selected prime by the same number of layers gives the
actual sigma/n inequality used by the joint envelope. At an insert step,
factorization_mul and factorization_pow show that all other selected
valuations are unchanged. -/
private theorem finite_boost_abundancy (S : Finset ℕ) (A : ℕ → ℕ) (b : ℕ) :
    (∀ p ∈ S, p.Prime) → ∀ n : ℕ, n ≠ 0 →
      (∀ p ∈ S, n.factorization p ≤ A p) →
      Z n ≤ (∏ p ∈ S,
        (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
          (1 - (p : ℝ)⁻¹ ^ (A p + b + 1))) *
        Z ((∏ p ∈ S, p ^ b) * n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _ n _ _
      simp
  | @insert p S hpS ih =>
      intro hS n hn ha
      have hp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime :=
        fun q hq => hS q (Finset.mem_insert_of_mem hq)
      let k := (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
        (1 - (p : ℝ)⁻¹ ^ (A p + b + 1))
      have hk : 0 < k :=
        div_pos (D5.S3.Weil.PrimeValuationGap.retention_pos hp (A p))
          (D5.S3.Weil.PrimeValuationGap.retention_pos hp (A p + b))
      have hgain := D5.S3.Weil.PrimeValuationGap.prime_power_abundancy_gain hp hn
        (ha p (Finset.mem_insert_self p S)) b
      have hcross := (div_le_div_iff₀ (D5.S3.Weil.PrimeValuationGap.retention_pos hp (A p))
        (div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n hn))
          (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))).mp hgain
      have hlocal : Z n ≤ k * Z (p ^ b * n) := by
        calc
          Z n ≤ Z (p ^ b * n) * (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
              (1 - (p : ℝ)⁻¹ ^ (A p + b + 1)) :=
            (le_div_iff₀ (D5.S3.Weil.PrimeValuationGap.retention_pos hp (A p + b))).mpr
              (by simpa only [mul_comm] using hcross)
          _ = k * Z (p ^ b * n) := by dsimp only [k]; ring
      have hother : ∀ q ∈ S, (p ^ b * n).factorization q ≤ A q := by
        intro q hq
        have hqp : q ≠ p := fun e => hpS (e ▸ hq)
        rw [Nat.factorization_mul (pow_ne_zero b hp.ne_zero) hn,
          Finsupp.add_apply, hp.factorization_pow,
          Finsupp.single_eq_of_ne hqp, zero_add]
        exact ha q (Finset.mem_insert_of_mem hq)
      have htail := ih hS' (p ^ b * n)
        (mul_ne_zero (pow_ne_zero b hp.ne_zero) hn) hother
      calc
        Z n ≤ k * Z (p ^ b * n) := hlocal
        _ ≤ k * ((∏ q ∈ S,
            (1 - (q : ℝ)⁻¹ ^ (A q + 1)) /
              (1 - (q : ℝ)⁻¹ ^ (A q + b + 1))) *
            Z ((∏ q ∈ S, q ^ b) * (p ^ b * n))) :=
          mul_le_mul_of_nonneg_left htail hk.le
        _ = _ := by
          simp only [k, Finset.prod_insert hpS, mul_assoc, mul_left_comm, mul_comm]

private theorem tendsto_finite_boost_coefficient (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (A : ℕ → ℕ) :
    Tendsto (fun b : ℕ => ∏ p ∈ S,
      (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
        (1 - (p : ℝ)⁻¹ ^ (A p + b + 1))) atTop
      (𝓝 (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1)))) := by
  apply tendsto_finsetProd S
  intro p hp
  have hpow : Tendsto (fun b : ℕ => (p : ℝ)⁻¹ ^ (A p + b + 1))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hS p hp).one_lt))).const_mul
      ((p : ℝ)⁻¹ ^ (A p + 1))
    simpa only [mul_zero, ← pow_add, Nat.add_right_comm (A p) 1] using h
  have h : Tendsto (fun b : ℕ =>
      (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
        (1 - (p : ℝ)⁻¹ ^ (A p + b + 1)))
      atTop (𝓝 ((1 - (p : ℝ)⁻¹ ^ (A p + 1)) / (1 - (0 : ℝ)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub hpow) (by norm_num)
  simpa only [sub_zero, div_one] using h

private theorem fixed_finite_boost_envelope (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (A : ℕ → ℕ) (b : ℕ) (q : ℝ)
    (hq : (∏ p ∈ S,
      (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
        (1 - (p : ℝ)⁻¹ ^ (A p + b + 1))) < q) :
    ∃ N ≥ 5041, ∀ n ≥ N, (∀ p ∈ S, n.factorization p ≤ A p) →
      robinRatio n ≤ q := by
  let c : ℕ := ∏ p ∈ S, p ^ b
  let k : ℝ := ∏ p ∈ S,
    (1 - (p : ℝ)⁻¹ ^ (A p + 1)) /
      (1 - (p : ℝ)⁻¹ ^ (A p + b + 1))
  have hc : 0 < c := Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos b)
  have hk : 0 < k := Finset.prod_pos (fun p hp =>
    div_pos (D5.S3.Weil.PrimeValuationGap.retention_pos (hS p hp) (A p))
      (D5.S3.Weil.PrimeValuationGap.retention_pos (hS p hp) (A p + b)))
  change k < q at hq
  let η := (q / k - 1) / 2
  have hη : 0 < η := div_pos
    (sub_pos.mpr ((lt_div_iff₀ hk).mpr (by simpa only [one_mul] using hq))) two_pos
  have hmid : k * (1 + η) = (k + q) / 2 := by
    dsimp only [η]
    field_simp [hk.ne']
    ring
  have hmargin : k * (1 + η) < q := by rw [hmid]; linarith only [hq]
  have hscale : Tendsto (fun n : ℕ =>
      Real.log (Real.log (c * n : ℕ)) / Real.log (Real.log n)) atTop (𝓝 1) := by
    simpa only [Nat.cast_mul] using
      (D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale (Nat.cast_pos.mpr hc : (0 : ℝ) < (c : ℝ)))
  have hlim : Tendsto (fun n : ℕ => k * (1 + η) *
      (Real.log (Real.log (c * n : ℕ)) / Real.log (Real.log n)))
      atTop (𝓝 (k * (1 + η))) := by
    simpa only [mul_one] using hscale.const_mul (k * (1 + η))
  obtain ⟨N₁, hN₁⟩ := GronwallUpperEnvelope.gronwall_upper_envelope η hη
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually_lt_const hmargin)
  refine ⟨max 5041 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro n hn ha
  have hnlarge : 5041 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnm : n ≤ c * n := Nat.le_mul_of_pos_left n hc
  have hmlarge : 5041 ≤ c * n := hnlarge.trans hnm
  have hmR : (0 : ℝ) < (c * n : ℕ) := Nat.cast_pos.mpr (by omega)
  have hLn := loglog_pos hnlarge
  have hLm := loglog_pos hmlarge
  have hu : robinRatio (c * n) ≤ 1 + η := hN₁ _ (by omega)
  have hsig := finite_boost_abundancy S A b hS n hn0 ha
  change Z n ≤ k * Z (c * n) at hsig
  calc
    robinRatio n = Z n / (Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log n)) := by
      dsimp only [robinRatio]
      rw [div_div]
      congr 1
      ring
    _ ≤ (k * Z (c * n)) / (Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log n)) :=
      div_le_div_of_nonneg_right hsig (mul_pos (Real.exp_pos _) hLn).le
    _ = (k * robinRatio (c * n)) *
        (Real.log (Real.log (c * n : ℕ)) / Real.log (Real.log n)) := by
      dsimp only [robinRatio]
      field_simp [hnR.ne', hmR.ne', hLn.ne', hLm.ne', Real.exp_ne_zero]
    _ ≤ (k * (1 + η)) *
        (Real.log (Real.log (c * n : ℕ)) / Real.log (Real.log n)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hk.le)
        (div_pos hLm hLn).le
    _ ≤ q := (hN₂ n (by omega)).le

/-- Full joint finite-prime Robin upper envelope. The finite support and all
exponent bounds are inputs before one common threshold. -/
theorem bounded_finite_prime_valuation_robin_ratio (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (A : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N ≥ 5041, ∀ n ≥ N, (∀ p ∈ S, n.factorization p ≤ A p) →
      robinRatio n ≤ (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) + ε := by
  classical
  by_cases hEmpty : S = ∅
  · subst S
    obtain ⟨N, hN⟩ := GronwallUpperEnvelope.gronwall_upper_envelope ε hε
    refine ⟨max 5041 N, le_max_left _ _, ?_⟩
    intro n hn _
    simpa only [Finset.prod_empty, robinRatio] using hN n (by omega)
  · have hsmall := (tendsto_finite_boost_coefficient S hS A).eventually_lt_const
      (lt_add_of_pos_right (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) hε)
    obtain ⟨b, hb⟩ := hsmall.exists
    exact fixed_finite_boost_envelope S hS A b _ hb

#print axioms bounded_finite_prime_valuation_robin_ratio

end D5.S3.Weil.FinitePrimeValuationEnvelopes
