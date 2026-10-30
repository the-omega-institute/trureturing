/- GID: D5/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail
   generality: I
   mirror-B: D5/B/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: One simultaneous predecessor exchange controls weighted finite-block Euler tails. -/

import D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
import D5.S3.Arith.Robin.PrimeValuation5040Bridge
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The finite block uses one actual smaller integer and one removed prime layer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (layerTail)
open D5.S3.Arith.Robin.PrimeValuation5040Bridge (primeBlock_factorization)
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin (primePowerProduct)

private theorem log_tail_contraction {r s : ℝ}
    (_hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    -Real.log (1 - s * r) ≤ s * (-Real.log (1 - r)) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1 - r ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr hr1)
    (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) from by norm_num)
    hs (sub_nonneg.mpr hs1) (by ring : s + (1 - s) = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
  have he : s * (1 - r) + (1 - s) * 1 = 1 - s * r := by ring
  rw [he] at hc
  linarith

private theorem local_block_gain_lower (lambda : ℝ) {q : ℕ} (hq : q.Prime)
    (a k : ℕ) :
    (1 - (q : ℝ)⁻¹ ^ k) * (-Real.log (1 - (q : ℝ)⁻¹ ^ (a + 1))) -
        lambda * k * Real.log q ≤
      goldenPrimeLocalObjective lambda q (a + k) -
        goldenPrimeLocalObjective lambda q a := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hx : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqpos
  have hx1 : (q : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hqpos).mpr (by exact_mod_cast hq.one_lt)
  have hr1 : (q : ℝ)⁻¹ ^ (a + 1) < 1 := pow_lt_one₀ hx.le hx1 (by omega)
  have hs1 : (q : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ hx.le hx1.le
  have hc := log_tail_contraction (pow_nonneg hx.le (a + 1)) hr1
    (pow_nonneg hx.le k) hs1
  have hnew : 0 < 1 - (q : ℝ)⁻¹ ^ (a + k + 1) :=
    sub_pos.mpr (pow_lt_one₀ hx.le hx1 (by omega))
  have hold : 0 < 1 - (q : ℝ)⁻¹ ^ (a + 1) := sub_pos.mpr hr1
  have hpow : (q : ℝ)⁻¹ ^ (a + k + 1) =
      (q : ℝ)⁻¹ ^ k * (q : ℝ)⁻¹ ^ (a + 1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold goldenPrimeLocalObjective
  rw [Real.log_div hnew.ne' (sub_pos.mpr hx1).ne',
    Real.log_div hold.ne' (sub_pos.mpr hx1).ne', hpow]
  push_cast
  nlinarith only [hc]

private theorem objective_block_delta (lambda : ℝ) {u : ℕ} (hu : 0 < u)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (k : ℕ) :
    goldenResourceObjective lambda (u * (∏ q ∈ S, q) ^ k) -
        goldenResourceObjective lambda u =
      ∑ q ∈ S, (goldenPrimeLocalObjective lambda q (u.factorization q + k) -
        goldenPrimeLocalObjective lambda q (u.factorization q)) := by
  classical
  let Q := ∏ q ∈ S, q
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => (hS q hq).pos)
  have hpowfac (q : ℕ) : (Q ^ k).factorization q = if q ∈ S then k else 0 := by
    simpa only [Q, primePowerProduct, Finset.prod_pow] using
      primeBlock_factorization hS (fun _ => k) q
  have hfac (q : ℕ) : (u * Q ^ k).factorization q =
      u.factorization q + if q ∈ S then k else 0 := by
    rw [Nat.factorization_mul hu.ne' (pow_ne_zero _ hQ.ne'), Finsupp.add_apply,
      hpowfac]
  have hsupport : (u * Q ^ k).primeFactors ⊆ u.primeFactors ∪ S := by
    intro q hq
    by_contra hn
    have hnot : q ∉ u.primeFactors ∧ q ∉ S := by
      simpa only [Finset.mem_union, not_or] using hn
    have huq : u.factorization q = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.notMem_support_iff] using hnot.1
    have hneq : (u * Q ^ k).factorization q ≠ 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hq
    rw [hfac, huq, ite_eq_right hnot.2] at hneq
    exact hneq (by simp)
  rw [golden_resource_objective_sum_on lambda
      (n := u * Q ^ k) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hu (pow_pos hQ _)).ne')
      (u.primeFactors ∪ S)
      hsupport,
    golden_resource_objective_sum_on lambda (by omega) (u.primeFactors ∪ S)
      Finset.subset_union_left, ← Finset.sum_sub_distrib]
  have hext :
      (∑ q ∈ u.primeFactors ∪ S,
        (goldenPrimeLocalObjective lambda q ((u * Q ^ k).factorization q) -
          goldenPrimeLocalObjective lambda q (u.factorization q))) =
      ∑ q ∈ S,
        (goldenPrimeLocalObjective lambda q ((u * Q ^ k).factorization q) -
          goldenPrimeLocalObjective lambda q (u.factorization q)) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro q _ hq
    rw [hfac, ite_eq_right hq, Nat.add_zero, sub_self]
  rw [hext]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hfac, ite_eq_left hq]

/-- A single smaller integer obtained by replacing one occupied `P` layer by
`k` copies of every prime in `S` controls their weighted missing Euler tails.
The record ranges over every positive predecessor; `S` may be empty and its
primes need not divide `m`. The price may be any real number. -/
theorem price_record_prime_block_tail {m P k : ℕ} {lambda : ℝ}
    (S : Finset ℕ) (hm : 0 < m)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (hP : P.Prime) (hPm : P ∣ m) (hS : ∀ q ∈ S, q.Prime)
    (hk : 1 ≤ k) (hsmall : (∏ q ∈ S, q) ^ k < P) :
    (∑ q ∈ S, (1 - (q : ℝ)⁻¹ ^ k) * layerTail m q) +
        lambda * (Real.log P - (k : ℝ) * Real.log (∏ q ∈ S, q : ℕ)) <
      goldenLayerMarginal P (m.factorization P) * Real.log P ∧
      goldenLayerMarginal P (m.factorization P) * Real.log P ≤ 1 / (P : ℝ) := by
  classical
  let Q := ∏ q ∈ S, q
  let u := m / P
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => (hS q hq).pos)
  have huP : u * P = m := Nat.div_mul_cancel hPm
  have hu : 0 < u := Nat.div_pos (Nat.le_of_dvd hm hPm) hP.pos
  have hn : 0 < u * Q ^ k := Nat.mul_pos hu (pow_pos hQ _)
  have hnm : u * Q ^ k < m := by
    rw [← huP]
    exact Nat.mul_lt_mul_of_pos_left hsmall hu
  have hPnot : P ∉ S := by
    intro hPS
    have hPQ : P ≤ Q :=
      Finset.single_le_prod (fun q hq => (hS q hq).one_lt.le) hPS
    have hQpow : Q ≤ Q ^ k := Nat.le_self_pow (by omega : k ≠ 0) Q
    exact (not_lt_of_ge (hPQ.trans hQpow)) hsmall
  have hvq (q : ℕ) (hq : q ∈ S) : u.factorization q = m.factorization q := by
    have hqP : q ≠ P := by rintro rfl; exact hPnot hq
    rw [← huP, Nat.factorization_mul hu.ne' hP.ne_zero, Finsupp.add_apply,
      hP.factorization]
    simp [Ne.symm hqP]
  have hvP : u.factorization P + 1 = m.factorization P := by
    rw [← huP, Nat.factorization_mul hu.ne' hP.ne_zero, Finsupp.add_apply,
      hP.factorization]
    simp
  have hlogQ : Real.log (Q : ℝ) = ∑ q ∈ S, Real.log (q : ℝ) := by
    rw [show (Q : ℝ) = ∏ q ∈ S, (q : ℝ) by simp [Q],
      Real.log_prod (fun q hq => by exact_mod_cast (hS q hq).ne_zero)]
  have hdelta := objective_block_delta lambda hu S hS k
  have hgain :
      (∑ q ∈ S, (1 - (q : ℝ)⁻¹ ^ k) * layerTail m q) -
          lambda * k * Real.log (Q : ℝ) ≤
        goldenResourceObjective lambda (u * Q ^ k) - goldenResourceObjective lambda u := by
    calc
      _ = ∑ q ∈ S, ((1 - (q : ℝ)⁻¹ ^ k) * layerTail m q -
          lambda * k * Real.log q) := by
        rw [hlogQ, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ ≤ ∑ q ∈ S, (goldenPrimeLocalObjective lambda q (u.factorization q + k) -
          goldenPrimeLocalObjective lambda q (u.factorization q)) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [hvq q hq]
        exact local_block_gain_lower lambda (hS q hq) (m.factorization q) k
      _ = _ := hdelta.symm
  have hremove := golden_resource_objective_single_layer_delta lambda
    (by omega : 1 ≤ u) hP
  rw [huP, hvP] at hremove
  have hrec := hrecord (u * Q ^ k) hn hnm
  have hstrict :
      (∑ q ∈ S, (1 - (q : ℝ)⁻¹ ^ k) * layerTail m q) +
          lambda * (Real.log P - (k : ℝ) * Real.log (Q : ℝ)) <
        goldenLayerMarginal P (m.factorization P) * Real.log P := by
    nlinarith only [hgain, hremove, hrec]
  have hlogP : 0 < Real.log (P : ℝ) := hP.log_pos
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hPinv : (P : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hPpos).mpr (by exact_mod_cast hP.one_lt)
  have hlast : goldenLayerMarginal P (m.factorization P) * Real.log P ≤
      1 / (P : ℝ) := by
    have hb := (le_div_iff₀ hlogP).mp
      (golden_layer_marginal_le_inv_pow hP (by omega : 1 ≤ m.factorization P))
    have hp := pow_le_pow_of_le_one (inv_pos.mpr hPpos).le hPinv.le
      (by omega : 1 ≤ m.factorization P)
    simp only [pow_one, one_div] at hp ⊢
    exact hb.trans hp
  exact ⟨hstrict, hlast⟩

#print axioms price_record_prime_block_tail

end D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
