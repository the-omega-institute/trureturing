/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus
   mirror-E: none(waiver:arithmetic-inequality)
   anchors: []
   utility: none
   digest: The actual complete prime-power ledger retains a quantitative prime-square band surplus. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus

open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (tail layerTail)
open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.GronwallLowerEnvelope
open private primeContribution cutoff_lt_iff layer_tail_gt_first
  full_surplus_eq_sum prime_contribution_pos
  from D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open private loglog_curvature
  from D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus

/-- The finite contribution guaranteed at a prime strictly beyond the square cutoff. -/
def primeBandWeight (p : ℕ) : ℝ :=
  ((p : ℝ) - 2) / (2 * ((p : ℝ) - 1) * (p : ℝ)^2)

private theorem primeBandWeight_eq (p : ℕ) (hp : p.Prime) :
    primeBandWeight p =
      ((p : ℝ)⁻¹)^2 - ((p : ℝ)⁻¹)^2 / 2 / (1 - (p : ℝ)⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr hp1
  unfold primeBandWeight
  field_simp [hp0, (sub_pos.mpr hp1).ne', (sub_pos.mpr hq).ne']
  <;> ring

/-- On the actual band p² > 2z, every positive valuation pays the same
strict square-reciprocal surplus. The entire shifted prime-power tail is retained. -/
theorem prime_contribution_sqrt_two {z : ℝ} (hz : 4 ≤ z) {n p : ℕ}
    (hp : p.Prime) (hpz : (p : ℝ) ≤ z)
    (hband : 2 * z < (p : ℝ)^2) (ha : 1 ≤ n.factorization p) :
    primeBandWeight p < primeContribution z n p := by
  let q : ℝ := (p : ℝ)⁻¹
  let c : ℝ := Real.log (p : ℝ) / (z * Real.log z)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hz0 : 0 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq1 : q < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hb : cutoffExponent z p = 1 := by
    have hb1 := (cutoff_spec hz hp hpz).1
    have hb2 := (cutoff_lt_iff hz hp hpz 2).mpr (by linarith)
    omega
  have hlog := Real.log_lt_log hz0 (show z < (p : ℝ)^2 by linarith)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hpq : q^2 * (p : ℝ)^2 = 1 := by
    dsimp [q]
    rw [← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow]
  have hqz : 2*z*q^2 < 1 := by
    have hh := mul_lt_mul_of_pos_right hband (sq_pos_of_pos hq0)
    nlinarith only [hh, hpq]
  have hc : q^2 < c := by
    dsimp [c]
    apply (lt_div_iff₀ (mul_pos hz0 hL)).mpr
    have hh := mul_lt_mul_of_pos_right hqz hL
    nlinarith only [hh, hlog]
  have htail : shiftedTail q 1 < q^2 / 2 / (1 - q) := by
    simpa using (shifted_tail_bound hq0 hq1 1).2
  have hraw : q^2 < layerTail n p + ((n.factorization p : ℝ) - 1) * c := by
    by_cases he : n.factorization p = 1
    · have hh := layer_tail_gt_first (n := n) hp
      simpa [q, he] using hh
    · have ha2 : (2 : ℝ) ≤ n.factorization p := by exact_mod_cast (show 2 ≤ n.factorization p by omega)
      have hpos : 0 < layerTail n p :=
        (pow_pos hq0 _).trans (layer_tail_gt_first hp)
      have hcoef := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (n.factorization p : ℝ) - 1 by linarith)
        (hc.le.trans' (sq_nonneg q))
      nlinarith only [hcoef, hc, hpos]
  rw [primeBandWeight_eq p hp]
  change q^2 - q^2 / 2 / (1-q) < primeContribution z n p
  unfold primeContribution
  rw [hb]
  simp only [Nat.cast_one]
  change _ < layerTail n p + ((n.factorization p : ℝ) - 1) * c - shiftedTail q 1
  linarith only [hraw, htail]

/-- The literal finite band at a real cutoff, including its upper endpoint. -/
def primeBand (z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊z⌋₊).filter (fun p => 2*z < (p : ℝ)^2)

/-- The same full ledger surplus used in the existing attained-minimum theorem. -/
def arithmeticSurplus (z : ℝ) (n : ℕ) : ℝ :=
  tail n + (Real.log (n : ℝ) - Chebyshev.psi z)/(z*Real.log z) -
    fullPrimePowerResidual z

def D (z : ℝ) : ℝ := Real.sqrt z * Real.log z

def normalizedPrimeBand (z : ℝ) : ℝ :=
  D z * ∑ p ∈ primeBand z, primeBandWeight p

/-- Sum the strengthened local contribution over the actual band and preserve
the nonnegative contributions of all other primes. -/
theorem prime_band_le_full_surplus {z : ℝ} (hz : 4 ≤ z) {n : ℕ}
    (hn : 0 < n) (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    ∑ p ∈ primeBand z, primeBandWeight p ≤ arithmeticSurplus z n := by
  classical
  let S := Nat.primesLE ⌊z⌋₊
  have hdata (p : ℕ) (hp : p ∈ S) : p.Prime ∧ (p : ℝ) ≤ z ∧ 1 ≤ n.factorization p := by
    obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpz : (p : ℝ) ≤ z :=
      (Nat.le_floor_iff (by linarith : 0 ≤ z)).mp hpf
    have hpn : p ∈ n.primeFactors := by rw [hsupport]; exact hp
    exact ⟨hpp, hpz, hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpn)⟩
  have hsub : primeBand z ⊆ S := Finset.filter_subset _ _
  unfold arithmeticSurplus
  rw [full_surplus_eq_sum hz hsupport]
  calc
    _ ≤ ∑ p ∈ primeBand z, primeContribution z n p := by
      apply Finset.sum_le_sum
      intro p hp
      have h := hdata p (hsub hp)
      exact (prime_contribution_sqrt_two hz h.1 h.2.1 (Finset.mem_filter.mp hp).2 h.2.2).le
    _ ≤ ∑ p ∈ S, primeContribution z n p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      obtain ⟨hpp, hpz, ha⟩ := hdata p hp
      exact (prime_contribution_pos hz hpp hpz ha).le

/-- The explicit normalized zero contribution and curvature budget. -/
def neededReserve (z : ℝ) : ℝ :=
  (1/20 : ℝ) * (1 + 1/Real.log z) + 2/Real.sqrt z +
    (1 + 1/Real.log z)/(8*z*Real.sqrt z)

/-- A finite exact band certificate and the real weighted tail bound eliminate
every failure after the endpoint-height certificate. -/
theorem robin_margin_of_effective_band
    (hfinite : ∀ n : ℕ, 5040 < n → Real.log (n : ℝ) ≤ 101 → 0 < robinLogMargin n)
    (hband : ∀ z : ℝ, 100 ≤ z → neededReserve z < normalizedPrimeBand z)
    (hweighted : ∀ z : ℝ, 100 ≤ z →
      -((1/20 : ℝ) * (1 + 1/Real.log z) + 2/Real.sqrt z) ≤
        D z * D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel z) :
    ∀ n : ℕ, 5040 < n → 0 < robinLogMargin n := by
  intro n hn
  by_contra! h
  obtain ⟨N,z,hN,hSN,hmin,hp0,hpb,hopt,hstrict,hNs,hNm,hnotie,
    hz,hM0,hMhalf,hroot,hunique,hsupport⟩ :=
    failure_has_unique_half_shift_cutoff ⟨n,hn,h⟩
  have hH : 101 < Real.log (N : ℝ) := by
    by_contra! hH
    exact (not_lt_of_ge hSN) (hfinite N (by omega) hH)
  have hz100 : 100 ≤ z := by linarith
  have hD : 0 < D z := mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))
  let M := Real.log (N : ℝ) - z
  let K := Real.log (Real.log z) + M/(z*Real.log z) - Real.log (Real.log (z+M))
  have hK := (loglog_curvature (by linarith : 1 < z) hM0 hMhalf).2
  change K < (Real.log z+1)/(8*z^2*(Real.log z)^2) at hK
  have hK' := mul_lt_mul_of_pos_left hK hD
  have hKnorm : D z * K < (1+1/Real.log z)/(8*z*Real.sqrt z) := by
    convert hK' using 1
    have hs := Real.sq_sqrt (by linarith : 0 ≤ z)
    dsimp [D]
    field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < z)).ne',
      (Real.log_pos (by linarith : 1 < z)).ne', show z ≠ 0 by linarith]
    rw [hs]
    <;> ring
  have harith := mul_le_mul_of_nonneg_left
    (prime_band_le_full_surplus (by linarith : 4 ≤ z) (by omega : 0 < N) hsupport) hD.le
  change normalizedPrimeBand z ≤ D z * arithmeticSurplus z N at harith
  have hledger := robin_margin_eq_complete_signed_ledger (by linarith : 4 ≤ z)
    (by omega : 0 < N) hsupport
  have hledger' : robinLogMargin N =
      D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel z +
        arithmeticSurplus z N - K := hledger
  have hscale := congrArg (fun y : ℝ => D z * y) hledger'
  rw [mul_sub, mul_add] at hscale
  have hb := hband z hz100
  have hw := hweighted z hz100
  have hfail := mul_nonpos_of_nonneg_of_nonpos hD.le hSN
  unfold neededReserve at hb
  linarith only [hscale, harith, hb, hw, hKnorm, hfail]

end D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
