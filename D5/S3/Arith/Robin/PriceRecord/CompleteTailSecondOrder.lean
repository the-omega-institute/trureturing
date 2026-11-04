/- GID: D5/S3/Arith/Robin/PriceRecord/CompleteTailSecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CompleteTailSecondOrder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Complete original Euler-tail second order at all positive-price full records. -/

/- SOURCE DRAFT ONLY, 2026-11-05: not elaborated, compiled, kernel checked,
   registered or accepted. Intended canonical inputs: supplied dev46927cc.
   This file is outside the canonical tree. No new axiom or proof hole is used.
   The final theorem retains every positive price and every strict positive
   predecessor. In particular, m is never replaced by a global optimizer.
   Classical PNT and finite Abel estimates are reused, with both endpoints.
   No Robin endpoint sign, RH result, or literature novelty is asserted. -/

import D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder

open Finset Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity

private def squareInterval (m : ℕ) : Finset ℕ :=
  (Ioc (layerPrime m 2) (largestPrime m)).filter Nat.Prime

private def squareSum (m : ℕ) : ℝ :=
  ∑ p ∈ squareInterval m, (1 : ℝ) / (p : ℝ) ^ 2

private def secondEndpoint (t : ℝ) : ℝ :=
  1 / (t * Real.log t) - 1 / (t * Real.log t ^ 2)

/-- Exact valuation partition of the same record integer, including Q=1. -/
private theorem record_partition {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    layerPrime m 2 ≤ largestPrime m ∧
    m.primeFactors.filter (fun p => m.factorization p = 1) = squareInterval m ∧
    tail m = (∑ p ∈ squareInterval m, -Real.log (1 - 1 / (p : ℝ) ^ 2)) +
      ∑ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), layerTail m p := by
  classical
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure hm hlambda hrecord
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  have hP2 : 2 ≤ largestPrime m :=
    (Nat.prime_of_mem_primeFactors hr).two_le.trans (le_sup (f := id) hr)
  have hQP : layerPrime m 2 ≤ largestPrime m := by
    apply max_le (by omega : 1 ≤ largestPrime m)
    apply Finset.sup_le
    intro p hp
    exact le_sup (f := id) (mem_filter.mp hp).1
  have hset : m.primeFactors.filter (fun p => m.factorization p = 1) =
      squareInterval m := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpm, hpval⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpm
      have hQp : layerPrime m 2 < p := by
        by_contra! hpQ
        have hh := valuation_below_layer_prime hprime hanti hpQ
        omega
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hQp, le_sup (f := id) hpm⟩, hprime⟩
    · intro hp
      obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
      obtain ⟨hQp, hpP⟩ := mem_Ioc.mp hpI
      have hpm : p ∈ m.primeFactors := by
        rw [hsupport]
        exact Nat.mem_primesLE.mpr ⟨hpP, hprime⟩
      have hlo : 1 ≤ m.factorization p := hprime.factorization_pos_of_dvd
        (by omega : m ≠ 0) (Nat.dvd_of_mem_primeFactors hpm)
      have hhi := valuation_above_layer_prime (by omega : 0 < m)
        (by norm_num : 1 ≤ (2 : ℕ)) hprime hQp
      exact mem_filter.mpr ⟨hpm, by omega⟩
  refine ⟨hQP, hset, ?_⟩
  have hnot : m.primeFactors.filter (fun p => ¬ 2 ≤ m.factorization p) =
      squareInterval m := by
    rw [← hset]
    apply filter_congr
    intro p hp
    have hlo : 1 ≤ m.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (by omega : m ≠ 0) (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hsplit := sum_filter_add_sum_filter_not m.primeFactors
    (fun p => 2 ≤ m.factorization p) (layerTail m)
  rw [hnot] at hsplit
  have hsimple : (∑ p ∈ squareInterval m, layerTail m p) =
      ∑ p ∈ squareInterval m, -Real.log (1 - 1 / (p : ℝ) ^ 2) := by
    apply sum_congr rfl
    intro p hp
    have hv := (mem_filter.mp (hset.symm ▸ hp)).2
    simp only [layerTail, hv, Nat.reduceAdd, inv_pow, one_div]
  rw [hsimple] at hsplit
  simpa only [tail, add_comm] using hsplit.symm

/-- The imported quadratic logarithm estimate pays the replacement error. -/
private theorem square_log_error {p : ℕ} (hp : p.Prime) :
    0 ≤ -Real.log (1 - 1 / (p : ℝ) ^ 2) - 1 / (p : ℝ) ^ 2 ∧
    -Real.log (1 - 1 / (p : ℝ) ^ 2) - 1 / (p : ℝ) ^ 2 ≤
      1 / (p : ℝ) ^ 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  let x : ℝ := 1 / (p : ℝ) ^ 2
  have hx0 : 0 ≤ x := by positivity
  have hxhalf : x ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hp0 2)).mpr
    nlinarith
  have hlo := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
  have hhi := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le hx0 hxhalf
  have hxsq : x ^ 2 = 1 / (p : ℝ) ^ 4 := by dsimp [x]; ring
  change 0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ _
  rw [← hxsq]
  constructor <;> linarith

/-- A complete-tail comparison, not just a bound on the valuation-one sum.
The deliberately crude cardinality bound is sufficient at second order. -/
private theorem record_tail_square_error {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    0 ≤ tail m - squareSum m ∧
    tail m - squareSum m ≤
      (largestPrime m : ℝ) / (layerPrime m 2 : ℝ) ^ 4 +
        6 / (largestPrime m : ℝ) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨_, _, hsplit⟩ := record_partition hm hlambda hrecord
  let Q : ℝ := layerPrime m 2
  let S := squareInterval m
  let e : ℕ → ℝ := fun p => -Real.log (1 - 1 / (p : ℝ) ^ 2) - 1 / (p : ℝ) ^ 2
  let H := ∑ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), layerTail m p
  have hQ0 : 0 < Q := by
    have hQ1 : 1 ≤ layerPrime m 2 := le_max_left _ _
    dsimp [Q]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ1)
  have he (p : ℕ) (hp : p ∈ S) : 0 ≤ e p ∧ e p ≤ 1 / Q ^ 4 := by
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    have hpQ : Q ≤ (p : ℝ) := by
      dsimp [Q]
      exact_mod_cast (mem_Ioc.mp hpI).1.le
    exact ⟨(square_log_error hprime).1, (square_log_error hprime).2.trans
      (one_div_le_one_div_of_le (pow_pos hQ0 4)
        (pow_le_pow_left₀ hQ0.le hpQ 4))⟩
  have hcard : (S.card : ℝ) ≤ (largestPrime m : ℝ) := by
    calc
      _ ≤ ((Ioc (layerPrime m 2) (largestPrime m)).card : ℝ) := by
        exact_mod_cast card_le_card (filter_subset Nat.Prime _)
      _ ≤ (largestPrime m : ℝ) := by
        simp only [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le (largestPrime m) (layerPrime m 2)
  have hE : (∑ p ∈ S, e p) ≤ (largestPrime m : ℝ) / Q ^ 4 := by
    calc
      _ ≤ (S.card : ℝ) * (1 / Q ^ 4) := by
        simpa only [nsmul_eq_mul] using sum_le_card_nsmul S e (1 / Q ^ 4)
          (fun p hp => (he p hp).2)
      _ ≤ (largestPrime m : ℝ) * (1 / Q ^ 4) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hH0 : 0 ≤ H := sum_nonneg fun p hp =>
    layer_tail_nonneg m (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
  have hH := HigherValuationTail.higher_valuation_tail hm hlambda hrecord
  have hid : tail m - squareSum m = (∑ p ∈ S, e p) + H := by
    rw [hsplit]
    dsimp [squareSum, S, e, H]
    rw [sum_sub_distrib]
    ring
  rw [hid]
  exact ⟨add_nonneg (sum_nonneg fun p hp => (he p hp).1) hH0, add_le_add hE hH⟩

/-- Full-family filter statement. All analytic premises are discharged inside
the proof from public suppliers, rather than passed in as missing estimates. -/
private theorem record_complete_tail_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      (Real.sqrt (largestPrime (m x) : ℝ) * Real.log (largestPrime (m x) : ℝ) *
        tail (m x) - Real.sqrt 2) + Real.sqrt 2 * (2 + Real.log 2 / 2)) l (𝓝 0) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => layerPrime (m x) 2
  let L : α → ℝ := fun x => Real.log (P x)
  let H : α → ℝ := fun x => Real.log (Q x)
  let R : α → ℝ := fun x => Q x ^ 2 / (2 * P x)
  let s : α → ℝ := fun x => Q x / Real.sqrt (P x)
  let B : α → ℝ := fun x => L x / H x
  let K : α → ℝ := fun x => Real.sqrt (P x) * L x ^ 2
  let c : ℝ := Real.log 2
  let k : ℝ := Real.sqrt 2
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by norm_num)
  have hk2 : k ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hQnonneg (x : α) : 0 ≤ Q x := Nat.cast_nonneg _
  have hL : Tendsto L l atTop := Real.tendsto_log_atTop.comp hP
  have hscaled0 : Tendsto (fun x => L x * (R x - 1) + c) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    obtain ⟨T, _, hT⟩ := LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity
      2 (by norm_num) epsilon hepsilon
    filter_upwards [hP.eventually_ge_atTop T] with x hx
    simpa only [Real.dist_eq, sub_zero, Nat.cast_ofNat, P, Q, L, R, c] using
      hT (m x) (hm x) (lambda x) (hlambda x) (hrecord x) hx
  have hscaled : Tendsto (fun x => L x * (R x - 1)) l (𝓝 (-c)) := by
    simpa only [add_sub_cancel_right, zero_sub] using hscaled0.sub_const c
  have hR : Tendsto R l (𝓝 1) := by
    have hzero : Tendsto (fun x => R x - 1) l (𝓝 0) := by
      apply (hscaled.div_atTop hL).congr'
      filter_upwards [hL.eventually_gt_atTop 0] with x hx
      exact mul_div_cancel_left₀ (R x - 1) hx.ne'
    simpa only [sub_add_cancel, zero_add] using hzero.add_const 1
  have hQsq : Tendsto (fun x => Q x ^ 2) l atTop := by
    have htwo : Tendsto (fun x => 2 * R x) l (𝓝 2) := by
      simpa only [mul_one] using hR.const_mul 2
    apply (htwo.pos_mul_atTop (by norm_num) hP).congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hx
    dsimp [R, P]
    field_simp [hx.ne']
    <;> ring
  have hQ : Tendsto Q l atTop :=
    (Real.tendsto_sqrt_atTop.comp hQsq).congr'
      (Eventually.of_forall fun x => Real.sqrt_sq (hQnonneg x))
  have hH : Tendsto H l atTop := Real.tendsto_log_atTop.comp hQ
  have hlogR : Tendsto (fun x => Real.log (R x)) l (𝓝 0) := by
    simpa only [Real.log_one] using hR.log (by norm_num : (1 : ℝ) ≠ 0)
  have hsquare : ∀ᶠ x in l, s x ^ 2 = 2 * R x := by
    filter_upwards [hP.eventually_gt_atTop 0] with x hx
    dsimp [s, R, P]
    rw [div_pow, Real.sq_sqrt hx.le]
    field_simp [hx.ne']
    <;> ring
  have hs : Tendsto s l (𝓝 k) := by
    have hh := (hR.const_mul 2).sqrt
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hx
    dsimp [s, R]
    rw [show 2 * (Q x ^ 2 / (2 * P x)) = Q x ^ 2 / P x by
      field_simp [hx.ne'] <;> ring,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (hQnonneg x)]
  have hsD : Tendsto (fun x => L x * (s x - k)) l (𝓝 (-c / k)) := by
    have hh := (hscaled.const_mul 2).div (hs.add_const k) (by positivity : k + k ≠ 0)
    have hvalue : 2 * (-c) / (k + k) = -c / k := by
      field_simp [hk0.ne', (by positivity : k + k ≠ 0)] <;> ring
    rw [hvalue] at hh
    apply hh.congr'
    filter_upwards [hsquare, hP.eventually_gt_atTop 0] with x hx hp
    have hs0 : 0 ≤ s x := div_nonneg (hQnonneg x) (Real.sqrt_nonneg _)
    have hden : s x + k ≠ 0 := (by positivity : 0 < s x + k).ne'
    have hid : (s x - k) * (s x + k) = 2 * (R x - 1) := by nlinarith
    symm
    apply (eq_div_iff hden).mpr
    calc
      (L x * (s x - k)) * (s x + k) = L x * ((s x - k) * (s x + k)) := by ring
      _ = 2 * (L x * (R x - 1)) := by rw [hid]; ring
  have hlogid : ∀ᶠ x in l, 2 * H x = L x + c + Real.log (R x) := by
    filter_upwards [hP.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0] with x hp hq
    dsimp [R, H, L, c]
    rw [Real.log_div (pow_ne_zero 2 hq.ne') (mul_ne_zero (by norm_num) hp.ne'),
      Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
    ring
  have hHL : Tendsto (fun x => H x / L x) l (𝓝 (1 / 2 : ℝ)) := by
    have hh := ((tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).add
      ((hlogR.const_add c).div_atTop hL)).div_const 2
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hlogid, hL.eventually_gt_atTop 0] with x hx hl
    symm
    calc
      H x / L x = ((L x + c + Real.log (R x)) / 2) / L x := by
        rw [show H x = (L x + c + Real.log (R x)) / 2 by linarith]
      _ = (1 + (c + Real.log (R x)) / L x) / 2 := by
        field_simp [hl.ne']
        <;> ring
  have hB : Tendsto B l (𝓝 2) := by
    simpa [B] using
      hHL.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hBD : Tendsto (fun x => L x * (B x - 2)) l (𝓝 (-2 * c)) := by
    have hh : Tendsto (fun x => -(B x * (c + Real.log (R x)))) l (𝓝 (-2 * c)) := by
      convert (hB.mul (hlogR.const_add c)).neg using 1 <;> ring
    apply hh.congr'
    filter_upwards [hlogid, hH.eventually_gt_atTop 0] with x hx hh
    have hid : L x - 2 * H x = -(c + Real.log (R x)) := by linarith
    calc
      -(B x * (c + Real.log (R x))) = B x * (L x - 2 * H x) := by rw [hid]; ring
      _ = L x * (B x - 2) := by dsimp [B]; field_simp [hh.ne']
  have hmain : Tendsto
      (fun x => L x * (Real.sqrt (P x) * L x / (Q x * H x) - k))
      l (𝓝 (-k * c / 2)) := by
    have hh := (hBD.sub (hsD.const_mul k)).div hs hk0.ne'
    have hvalue : (-2 * c - k * (-c / k)) / k = -k * c / 2 := by
      field_simp [hk0.ne']
      nlinarith [congrArg (fun t : ℝ => c * t) hk2]
    rw [hvalue] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0,
      hH.eventually_gt_atTop 0] with x hp hq hh
    have hsne : s x ≠ 0 := (div_pos hq (Real.sqrt_pos.mpr hp)).ne'
    have hnorm : Real.sqrt (P x) * L x / (Q x * H x) = B x / s x := by
      dsimp [B, s]
      field_simp [hq.ne', hh.ne', (Real.sqrt_pos.mpr hp).ne']
      <;> ring
    rw [hnorm]
    calc
      (L x * (B x - 2) - k * (L x * (s x - k))) / s x =
          (L x * (B x - k * s x)) / s x := by
        congr 1
        nlinarith [congrArg (fun t : ℝ => L x * t) hk2]
      _ = L x * (B x / s x - k) := by field_simp [hsne]
  have hsecond : Tendsto (fun x => K x / (Q x * H x ^ 2)) l (𝓝 (2 * k)) := by
    have hh := (hB.pow 2).div hs hk0.ne'
    have hvalue : (2 : ℝ) ^ 2 / k = 2 * k := by
      apply (div_eq_iff hk0.ne').mpr
      nlinarith
    rw [hvalue] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0,
      hH.eventually_gt_atTop 0] with x hp hq hh
    dsimp [B, s, K]
    field_simp [hq.ne', hh.ne', (Real.sqrt_pos.mpr hp).ne']
    <;> ring

  -- The arithmetic error is negligible at K=sqrt(P)*log(P)^2.
  have logSmall (r : ℝ) (hr : 0 < r) :
      Tendsto (fun x => L x ^ 2 / P x ^ r) l (𝓝 0) := by
    simpa only [Real.rpow_two, Function.comp_def, L, P] using
      ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hr).tendsto_div_nhds_zero.comp hP)
  have hrootSmall : Tendsto (fun x => L x ^ 2 / Real.sqrt (P x)) l (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using logSmall (1 / 2) (by norm_num)
  have hK0 (x : α) : 0 ≤ K x := mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have harithmetic : Tendsto (fun x => K x * (tail (m x) - squareSum (m x)))
      l (𝓝 0) := by
    have hmajor : Tendsto
        (fun x => L x ^ 2 / Real.sqrt (P x) + 6 * (L x ^ 2 / P x ^ (1 / 6 : ℝ)))
        l (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        hrootSmall.add ((logSmall (1 / 6) (by norm_num)).const_mul 6)
    refine squeeze_zero' ?_ ?_ hmajor
    · exact Eventually.of_forall fun x => mul_nonneg (hK0 x)
        (record_tail_square_error (hm x) (hlambda x) (hrecord x)).1
    · filter_upwards [hP.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0,
        hR.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
        with x hp hq hr
      have hQ2 : P x ≤ Q x ^ 2 := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2 * P x)).mp hr.le
        change (1 / 2 : ℝ) * (2 * P x) ≤ Q x ^ 2 at hh
        linarith
      have hQ4 : P x ^ 2 ≤ Q x ^ 4 := by
        simpa only [← pow_mul] using pow_le_pow_left₀ hp.le hQ2 2
      have hquot : P x / Q x ^ 4 ≤ 1 / P x := by
        apply (div_le_div_iff₀ (pow_pos hq 4) hp).mpr
        nlinarith
      have hfirstError : K x * (P x / Q x ^ 4) ≤ L x ^ 2 / Real.sqrt (P x) := by
        calc
          _ ≤ K x * (1 / P x) := mul_le_mul_of_nonneg_left hquot (hK0 x)
          _ = (Real.sqrt (P x) / P x) * L x ^ 2 := by dsimp [K]; ring
          _ = _ := by rw [Real.sqrt_div_self]; ring
      have hpower : P x ^ (2 / 3 : ℝ) = Real.sqrt (P x) * P x ^ (1 / 6 : ℝ) := by
        dsimp [P]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
        norm_num
      have hrepeatError : K x * (6 / P x ^ (2 / 3 : ℝ)) =
          6 * (L x ^ 2 / P x ^ (1 / 6 : ℝ)) := by
        rw [hpower]
        dsimp [K]
        field_simp [hp.ne', (Real.sqrt_pos.mpr hp).ne',
          (Real.rpow_pos_of_pos hp _).ne']
        calc
          _ = (Real.sqrt (P x) * (Real.sqrt (P x))⁻¹) *
              (L x ^ 2 * (P x ^ (1 / 6 : ℝ))⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hp).ne']; ring
      have hh := mul_le_mul_of_nonneg_left
        (record_tail_square_error (hm x) (hlambda x) (hrecord x)).2 (hK0 x)
      change K x * (tail (m x) - squareSum (m x)) ≤
        K x * (P x / Q x ^ 4 + 6 / P x ^ (2 / 3 : ℝ)) at hh
      rw [mul_add, hrepeatError] at hh
      exact hh.trans (add_le_add hfirstError (le_refl _))

  -- Retain the finite upper Abel endpoint before showing its scaled limit.
  have hlogroot : Tendsto (fun x => L x / Real.sqrt (P x)) l (𝓝 0) := by
    apply (hrootSmall.div_atTop hL).congr'
    filter_upwards [hL.eventually_gt_atTop 0, hP.eventually_gt_atTop 0] with x hx hp
    field_simp [hx.ne', (Real.sqrt_pos.mpr hp).ne']
    <;> ring
  have hinvroot : Tendsto (fun x => 1 / Real.sqrt (P x)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hP)
  have hupperEndpoint : Tendsto (fun x => K x * secondEndpoint (P x)) l (𝓝 0) := by
    have hz : Tendsto (fun x => L x / Real.sqrt (P x) - 1 / Real.sqrt (P x)) l (𝓝 0) := by
      simpa only [sub_zero] using hlogroot.sub hinvroot
    apply hz.congr'
    filter_upwards [hP.eventually_gt_atTop 0, hL.eventually_gt_atTop 0] with x hp hl
    symm
    calc
      K x * secondEndpoint (P x) = (Real.sqrt (P x) / P x) * (L x - 1) := by
        change (Real.sqrt (P x) * L x ^ 2) *
          (1 / (P x * L x) - 1 / (P x * L x ^ 2)) = _
        field_simp [hp.ne', hl.ne']
        <;> ring
      _ = L x / Real.sqrt (P x) - 1 / Real.sqrt (P x) := by
        rw [Real.sqrt_div_self]
        ring
  have hAbelMajor : Tendsto (fun x => K x *
      (2 / (Q x * H x ^ 3) + 5 / (Q x * H x ^ 9))) l (𝓝 0) := by
    have hh := ((hsecond.div_atTop hH).const_mul 2).add
      ((hsecond.div_atTop ((tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp hH)).const_mul 5)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [hQ.eventually_gt_atTop 0, hH.eventually_gt_atTop 0] with x hq hh
    simp only [Function.comp_apply]
    field_simp [hq.ne', hh.ne']
    <;> ring
  have hAbel : Tendsto (fun x => K x *
      (squareSum (m x) - secondEndpoint (Q x) + secondEndpoint (P x))) l (𝓝 0) := by
    obtain ⟨Y, _, hY⟩ := PrimeSquareTail.prime_square_tail_logarithmic_refinements
    apply squeeze_zero_norm' (a := fun x => K x *
      (2 / (Q x * H x ^ 3) + 5 / (Q x * H x ^ 9)))
    · filter_upwards [hQ.eventually_ge_atTop Y] with x hx
      have hQP : Q x ≤ P x := by
        dsimp [Q, P]
        exact_mod_cast (record_partition (hm x) (hlambda x) (hrecord x)).1
      have hh := (hY (Q x) (P x) hx hQP).1
      have hfinite : |squareSum (m x) - secondEndpoint (Q x) + secondEndpoint (P x)| ≤
          2 / (Q x * H x ^ 3) + 5 / (Q x * H x ^ 9) := by
        simpa only [squareSum, squareInterval, secondEndpoint, Q, P, H,
          Nat.floor_natCast] using hh
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 x)]
      exact mul_le_mul_of_nonneg_left hfinite (hK0 x)
    · exact hAbelMajor
  have hlowerEndpoint : Tendsto
      (fun x => L x * (Real.sqrt (P x) * L x * secondEndpoint (Q x) - k))
      l (𝓝 (-k * (2 + c / 2))) := by
    have hh := hmain.sub hsecond
    have hvalue : -k * c / 2 - 2 * k = -k * (2 + c / 2) := by ring
    rw [hvalue] at hh
    apply hh.congr'
    filter_upwards [hQ.eventually_gt_atTop 0, hH.eventually_gt_atTop 0] with x hq hh
    change L x * (Real.sqrt (P x) * L x / (Q x * H x) - k) -
      (Real.sqrt (P x) * L x ^ 2) / (Q x * H x ^ 2) =
      L x * (Real.sqrt (P x) * L x *
        (1 / (Q x * H x) - 1 / (Q x * H x ^ 2)) - k)
    field_simp [hq.ne', hh.ne']
    <;> ring
  have htotal := (((harithmetic.add hAbel).sub hupperEndpoint).add hlowerEndpoint).add_const
    (k * (2 + c / 2))
  have htotal' : Tendsto
      (fun x =>
        K x * (tail (m x) - squareSum (m x)) +
          K x * (squareSum (m x) - secondEndpoint (Q x) + secondEndpoint (P x)) -
          K x * secondEndpoint (P x) +
          L x * (Real.sqrt (P x) * L x * secondEndpoint (Q x) - k) +
          k * (2 + c / 2)) l (𝓝 0) := by
    simpa using htotal
  apply htotal'.congr'
  exact Eventually.of_forall fun x => by dsimp [K, P, L, k, c]; ring

/-- The complete original Euler tail has a uniform logarithmic second-order
law over every literal strict positive-price full predecessor record.
The threshold is chosen before both m and lambda. -/
theorem price_record_complete_tail_second_order (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      |Real.log (largestPrime m : ℝ) *
        (Real.sqrt (largestPrime m : ℝ) * Real.log (largestPrime m : ℝ) * tail m -
          Real.sqrt 2) + Real.sqrt 2 * (2 + Real.log 2 / 2)| < epsilon := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ n : ℕ, 0 < n → n < v.1 →
      goldenResourceObjective v.2 n < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let lambda : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have hh := record_complete_tail_limit m lambda (fun x => x.2.1)
    (fun x => x.2.2.1) (fun x => x.2.2.2) hP
  have hevent := (Metric.tendsto_nhds.mp hh) epsilon hepsilon
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hevent)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn lam hlam hrecord hlarge
  let x : S := ⟨(n, lam), hn, hlam, hrecord⟩
  have hx := hT (largestPrime n : ℝ) ((le_max_left T 2).trans hlarge) x rfl
  simpa only [Real.dist_eq, sub_zero] using hx

-- This command is source for the caller's future check; it has not been run.
#print axioms price_record_complete_tail_second_order

end D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder
