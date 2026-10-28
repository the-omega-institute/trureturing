/- GID: D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer
   generality: I
   mirror-B: D5/B/S3/Arith/ExponentExchange/PriceRecordMissingLayer
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Full positive-price predecessor records uniformly bound every smaller prime's missing-layer Euler tail. -/

import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.GoldenLayerMarginalDecay

namespace D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenLayerMarginalDecay

noncomputable section

/-- A square comparison controls the entire logarithmic tail by one layer. -/
private theorem log_tail_le_twice_gain {x r : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hr : 0 ≤ r) (hrlt : r < 1) :
    -Real.log (1 - r) ≤ 2 * Real.log ((1 - r * x) / (1 - r)) := by
  have hd : 0 < 1 - r := sub_pos.mpr hrlt
  have hn : 0 < 1 - r * x := by
    have hrx := mul_le_mul_of_nonneg_left hxhalf hr
    nlinarith
  have hs : 1 - r ≤ (1 - r * x) ^ 2 := by
    nlinarith [mul_nonneg hr (by linarith : 0 ≤ 1 - 2 * x), sq_nonneg (r * x)]
  have hlog := Real.log_le_log hd hs
  rw [Real.log_pow] at hlog
  rw [Real.log_div hn.ne' hd.ne']
  norm_num at hlog
  linarith

/-- Removing a larger prime and inserting a smaller prime at a full predecessor record
forces a strict next-layer gain comparison and a uniform logarithmic Euler-tail bound.
The smaller prime's valuation may be zero. -/
theorem price_record_missing_layer {m P q : ℕ} {lambda : ℝ}
    (hm : 0 < m) (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (hP : P.Prime) (hPm : P ∣ m) (hq : q.Prime) (hqP : q < P) :
    let u := m / P
    let n := u * q
    let r := (q : ℝ)⁻¹ ^ (m.factorization q + 1)
    0 < n ∧ n < m ∧ u * P = m ∧
      u.factorization P + 1 = m.factorization P ∧
      u.factorization q = m.factorization q ∧
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q +
          lambda * (Real.log P - Real.log q) <
        goldenLayerMarginal P (m.factorization P) * Real.log P ∧
      goldenLayerMarginal P (m.factorization P) * Real.log P ≤ 1 / (P : ℝ) ∧
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q < 1 / (P : ℝ) ∧
      0 < r ∧ r ≤ 1 / (q : ℝ) ∧ (1 / (q : ℝ)) ≤ 1 / 2 ∧
      -Real.log (1 - r) < 2 / (P : ℝ) := by
  let u := m / P
  have huP : u * P = m := Nat.div_mul_cancel hPm
  have hu : 0 < u := Nat.div_pos (Nat.le_of_dvd hm hPm) hP.pos
  have hn : 0 < u * q := Nat.mul_pos hu hq.pos
  have hnm : u * q < m := by
    rw [← huP]
    exact Nat.mul_lt_mul_of_pos_left hqP hu
  have hfac := Nat.factorization_mul hu.ne' hP.ne_zero
  have hvP : u.factorization P + 1 = m.factorization P := by
    rw [← huP, hfac, Finsupp.add_apply, hP.factorization]
    simp
  have hvq : u.factorization q = m.factorization q := by
    rw [← huP, hfac, Finsupp.add_apply, hP.factorization]
    simp [hqP.ne]
  have hdP := golden_resource_objective_single_layer_delta lambda hu hP
  have hdq := golden_resource_objective_single_layer_delta lambda hu hq
  rw [huP, hvP] at hdP
  rw [hvq] at hdq
  have hexchange :
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q +
          lambda * (Real.log P - Real.log q) <
        goldenLayerMarginal P (m.factorization P) * Real.log P := by
    have hr := hrecord (u * q) hn hnm
    nlinarith only [hr, hdP, hdq]
  have hlogP : 0 < Real.log (P : ℝ) := hP.log_pos
  have hlogq : 0 < Real.log (q : ℝ) := hq.log_pos
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
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
  have hprice : 0 < lambda * (Real.log P - Real.log q) :=
    mul_pos hlambda (sub_pos.mpr
      (Real.log_lt_log hqpos (by exact_mod_cast hqP)))
  have hgain : goldenLayerMarginal q (m.factorization q + 1) * Real.log q <
      1 / (P : ℝ) := by linarith
  have hx : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqpos
  have hxlt : (q : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hqpos).mpr (by exact_mod_cast hq.one_lt)
  have hxhalf : (q : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hq.two_le : (2 : ℝ) ≤ q)
  let r := (q : ℝ)⁻¹ ^ (m.factorization q + 1)
  have hr : 0 < r := pow_pos hx _
  have hrle : r ≤ (q : ℝ)⁻¹ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hx.le hxlt.le
      (by omega : 1 ≤ m.factorization q + 1)
  have hrl : r < 1 := hrle.trans_lt hxlt
  have htail := log_tail_le_twice_gain hx.le hxhalf hr.le hrl
  have hgain_eq : goldenLayerMarginal q (m.factorization q + 1) * Real.log q =
      Real.log ((1 - r * (q : ℝ)⁻¹) / (1 - r)) := by
    unfold goldenLayerMarginal
    rw [div_mul_cancel₀ _ hlogq.ne', pow_succ]
  have htailbound : -Real.log (1 - r) < 2 / (P : ℝ) := by
    rw [← hgain_eq] at htail
    linarith
  exact ⟨hn, hnm, huP, hvP, hvq, hexchange, hlast, hgain,
    hr, by simpa only [one_div] using hrle, by simpa only [one_div] using hxhalf,
    htailbound⟩

#print axioms price_record_missing_layer

end

end D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
