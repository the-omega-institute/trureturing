/- GID: D5/S3/Arith/Robin/RestrictedDivisorStrictInventory
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/RestrictedDivisorStrictInventory
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Nonlinear forced-divisor maxima have strict own-clock Euler inventory. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Data.Finset.Max

noncomputable section
open Set Finset

namespace D5.S3.Arith.Robin.RestrictedDivisorStrictInventory

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion

local notation "price" => D5.S3.Arith.Robin.ActualRobinClockCovariance.g

private theorem prime_delta {n q : ℕ} (hn : 1 ≤ n) (hq : q.Prime) :
    originalObjective (n * q)-originalObjective n =
      goldenLayerMarginal q (n.factorization q + 1) * Real.log q -
        (Real.log (Real.log (Real.log (n : ℝ) + Real.log q)) -
          Real.log (Real.log (Real.log (n : ℝ)))) := by
  have hnq : 1 ≤ n * q := by nlinarith [hq.pos]
  have hd := golden_resource_objective_single_layer_delta 0 hn hq
  rw [golden_resource_sigma_identity 0 hn,
    golden_resource_sigma_identity 0 hnq] at hd
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  unfold originalObjective
  rw [Nat.cast_mul, Real.log_mul hn0 hq0]
  simp only [zero_mul, sub_zero] at hd
  push_cast at hd
  linarith

private theorem log_mul_le {p u v : ℕ} (hp : 0 < p) (hu : 0 < u)
    (huv : u ≤ v) : Real.log (p * u : ℕ) ≤ Real.log (p * v : ℕ) := by
  apply Real.log_le_log
  · exact_mod_cast Nat.mul_pos hp hu
  · exact_mod_cast Nat.mul_le_mul_left p huv

/-- A maximum on the actual forced-divisor domain has the strict own-clock
layer counts. The saturated stack uses an inactive bound at a larger parent
clock; mandatory bottom layers are explicitly protected and already active. -/
theorem restricted_divisor_maximum_strict_inventory
    {p m V W : ℕ} (hp : p.Prime) (hm : 0 < m) (hV : 0 < V)
    (hmW : m ∣ W) (hWV : W ∣ V) (hW : 0 < W) (hpV : ¬p ∣ V)
    {a : ℝ} (hclock : 1 < Real.log (p * m : ℕ))
    (hparent : Real.log (p * V : ℕ) < a)
    (hsaturated : ∀ q : ℕ, q.Prime →
      goldenLayerMarginal q (V.factorization q + 1) ≤ price a)
    (hforced : ∀ q : ℕ, q.Prime → 0 < m.factorization q →
      price (Real.log (p * m : ℕ)) < goldenLayerMarginal q (m.factorization q))
    (hmax : ∀ U : ℕ, 0 < U → m ∣ U → U ∣ V →
      originalObjective (p * U) ≤ originalObjective (p * W)) :
    ∀ q : ℕ, W.factorization q = optimalLayerCount (price (Real.log (p * W : ℕ))) q := by
  let b := Real.log (p * W : ℕ)
  have hbase : Real.log (p * m : ℕ) ≤ b :=
    log_mul_le hp.pos hm (Nat.le_of_dvd hW hmW)
  have hb : 1 < b := hclock.trans_le hbase
  have hba : b < a :=
    (log_mul_le hp.pos hW (Nat.le_of_dvd hV hWV)).trans_lt hparent
  have hprice : 0 < price b := by
    exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hb))
  have hfacWV := (Nat.factorization_le_iff_dvd hW.ne' hV.ne').mpr hWV
  have hfacmW := (Nat.factorization_le_iff_dvd hm.ne' hW.ne').mpr hmW
  have hneq {q : ℕ} (he : 0 < W.factorization q ∨ 0 < V.factorization q) : q ≠ p := by
    intro hqp
    subst q
    have hz := Nat.factorization_eq_zero_of_not_dvd hpV
    have hwz : W.factorization p = 0 := by have := hfacWV p; omega
    omega
  have hnext : ∀ q : ℕ, q.Prime →
      goldenLayerMarginal q (W.factorization q + 1) < price b := by
    intro q hq
    rcases eq_or_lt_of_le (hfacWV q) with he | he
    · rw [he]
      exact (hsaturated q hq).trans_lt
        (D5.S3.Arith.Robin.EulerLayerPhaseSeparation.price_strictAnti hb hba)
    · have hqp : q ≠ p := hneq (Or.inr (by omega))
      have hWqV : W * q ∣ V := by
        apply (Nat.factorization_le_iff_dvd (mul_ne_zero hW.ne' hq.ne_zero) hV.ne').mp
        rw [Nat.factorization_mul hW.ne' hq.ne_zero]
        intro r
        by_cases hrq : r = q
        · subst r
          simpa [hq.factorization] using (show W.factorization q + 1 ≤ V.factorization q by omega)
        · simpa [hq.factorization, hrq] using hfacWV r
      have hc := hmax (W * q) (Nat.mul_pos hW hq.pos)
        (hmW.trans (dvd_mul_right W q)) hWqV
      have hd := prime_delta (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hW.ne')) hq
      have hfp : (p * W).factorization q = W.factorization q := by
        simp [Nat.factorization_mul hp.ne_zero hW.ne', hp.factorization, hqp]
      rw [hfp] at hd
      rw [Nat.mul_assoc] at hd
      have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
      have ht := loglog_tangent hb (by linarith : 1 < b + Real.log q)
        (by linarith : b ≠ b + Real.log q)
      change _ < (b + Real.log q-b) * price b at ht
      have hmul : goldenLayerMarginal q (W.factorization q + 1) * Real.log q <
          price b * Real.log q := by
        dsimp [b] at ht
        nlinarith [hc]
      exact (mul_lt_mul_iff_left₀ hlq).mp (by simpa [mul_comm] using hmul)
  have hlast : ∀ q : ℕ, q.Prime → 0 < W.factorization q →
      price b < goldenLayerMarginal q (W.factorization q) := by
    intro q hq hepos
    rcases eq_or_lt_of_le (hfacmW q) with he | he
    · have hbaseprice : price b ≤ price (Real.log (p * m : ℕ)) := by
        rcases eq_or_lt_of_le hbase with heq | hlt
        · rw [heq]
        · exact (D5.S3.Arith.Robin.EulerLayerPhaseSeparation.price_strictAnti hclock hlt).le
      rw [← he]
      exact hbaseprice.trans_lt (hforced q hq (by omega))
    · have hqW : q ∣ W := by
        by_contra h
        have hz := Nat.factorization_eq_zero_of_not_dvd h
        omega
      have hqp : q ≠ p := hneq (Or.inl hepos)
      let T := W/q
      have hT : 0 < T := Nat.div_pos (Nat.le_of_dvd hW hqW) hq.pos
      have hTq : T * q = W := Nat.div_mul_cancel hqW
      have hmT : m ∣ T := by
        apply (Nat.factorization_le_iff_dvd hm.ne' hT.ne').mp
        rw [show T = W/q from rfl, Nat.factorization_div hqW]
        intro r
        by_cases hrq : r = q
        · subst r
          simpa [hq.factorization] using (show m.factorization q ≤ W.factorization q-1 by omega)
        · simpa [hq.factorization, hrq] using hfacmW r
      have hTV : T ∣ V := (Nat.div_dvd_of_dvd hqW).trans hWV
      have hc := hmax T hT hmT hTV
      have hcclock : 1 < Real.log (p * T : ℕ) :=
        hclock.trans_le (log_mul_le hp.pos hm (Nat.le_of_dvd hT hmT))
      have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
      have hlog : b = Real.log (p * T : ℕ) + Real.log q := by
        dsimp [b]
        rw [← hTq, ← Nat.mul_assoc, Nat.cast_mul,
          Real.log_mul (by exact_mod_cast (mul_ne_zero hp.ne_zero hT.ne'))
            (by exact_mod_cast hq.ne_zero)]
      have ht := loglog_tangent hb hcclock (by linarith : b ≠ Real.log (p * T : ℕ))
      have hd := prime_delta (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hT.ne')) hq
      have hfp : (p * T).factorization q + 1 = W.factorization q := by
        have hf := congrArg (fun f : ℕ →₀ ℕ => f q)
          (Nat.factorization_mul hT.ne' hq.ne_zero)
        rw [hTq] at hf
        simp only [Finsupp.add_apply, hq.factorization, Finsupp.single_eq_same] at hf
        simpa [Nat.factorization_mul hp.ne_zero hT.ne', hp.factorization, hqp] using hf.symm
      rw [hfp, Nat.mul_assoc, hTq] at hd
      have hmul : price b * Real.log q <
          goldenLayerMarginal q (W.factorization q) * Real.log q := by
        rw [← hlog] at hd
        nlinarith
      exact (mul_lt_mul_iff_left₀ hlq).mp (by simpa [mul_comm] using hmul)
  intro q
  change W.factorization q = optimalLayerCount (price b) q
  by_cases hq : q.Prime
  · have hi := positive_layers_eq_count_interval hprice hq
    apply Nat.le_antisymm
    · by_cases he : W.factorization q = 0
      · omega
      · have hmemb : W.factorization q ∈ Set.Icc 1 (optimalLayerCount (price b) q) := by
          rw [← hi]
          exact ⟨by omega, hq, hlast q hq (by omega)⟩
        exact hmemb.2
    · by_contra h
      have hmemb : W.factorization q + 1 ∈ Set.Icc 1 (optimalLayerCount (price b) q) := by
        exact ⟨by omega, by omega⟩
      rw [← hi] at hmemb
      exact (not_lt_of_ge (hnext q hq).le) hmemb.2.2
  · simp [Nat.factorization_eq_zero_of_not_prime W hq, optimalLayerCount, hq]

private theorem forced_5040_active {b : ℝ} (hb : 243 ≤ b)
    {q : ℕ} (hq : q.Prime) (he : 0 < (5040 : ℕ).factorization q) :
    price b < goldenLayerMarginal q ((5040 : ℕ).factorization q) := by
  have hb0 : 0 < b := by linarith
  have hlog : 1 < Real.log b :=
    (Real.lt_log_iff_exp_lt hb0).mpr (Real.exp_one_lt_three.trans_le (by linarith))
  have hprice : price b < (1 / 25 : ℝ) := by
    unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
    apply (div_lt_div_iff₀ (mul_pos hb0 (by linarith)) (by norm_num)).mpr
    nlinarith
  have hopt : IsGoldenResourceOptimal (1 / 25) 5040 :=
    fun n hn => (golden_resource_unique_optimum hn).1
  have hthreshold := (golden_resource_optimal_iff_layer_thresholds
    (by norm_num : (0 : ℝ) < 1 / 25) (by norm_num : 1 ≤ (5040 : ℕ))).mp hopt
  have hq5040 : q ∣ 5040 := by
    by_contra h
    have hz := Nat.factorization_eq_zero_of_not_dvd h
    omega
  exact hprice.trans_le (hthreshold.2 q hq hq5040)

/-- The original strict comparison against every proper 5040-forced divisor
is equivalent to comparison against the divisors with strict own-clock
inventory. If a proper divisor ties or beats V, a classified proper maximum
exists. No terminal sign or equality of good and full endpoints is assumed. -/
theorem strict_5040_divisor_comparison_iff_inventory
    {p P V : ℕ} (hp : p.Prime) (hpP : p < P) (hV : 0 < V)
    (hpV : ¬p ∣ V)
    (hclock : 243 ≤ Real.log (p * 5040 : ℕ))
    (hsaturated : ∀ q : ℕ, q.Prime →
      goldenLayerMarginal q (V.factorization q + 1) ≤ price (Real.log (P * V : ℕ))) :
    (∀ U : ℕ, 0 < U → 5040 ∣ U → U ∣ V → U < V →
      originalObjective (p * U) < originalObjective (p * V)) ↔
    (∀ U : ℕ, 0 < U → 5040 ∣ U → U ∣ V → U < V →
      (∀ q : ℕ, U.factorization q = optimalLayerCount (price (Real.log (p * U : ℕ))) q) →
      originalObjective (p * U) < originalObjective (p * V)) := by
  classical
  constructor
  · intro h U hU hmU hUV hlt _
    exact h U hU hmU hUV hlt
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨U, hU, hmU, hUV, hlt, hvalue⟩ := hn
    let D := V.divisors.filter (fun Z => 5040 ∣ Z ∧ Z < V)
    have hUD : U ∈ D := by
      simp [D, Nat.mem_divisors, hV.ne', hmU, hUV, hlt]
    obtain ⟨W, hWD, hWmax⟩ := Finset.exists_max_image D
      (fun Z => originalObjective (p * Z)) ⟨U, hUD⟩
    have hmem := Finset.mem_filter.mp hWD
    have hWV : W ∣ V := (Nat.mem_divisors.mp hmem.1).1
    have hmW : 5040 ∣ W := hmem.2.1
    have hWlt : W < V := hmem.2.2
    have hW : 0 < W := by
      by_contra hz
      have he : W = 0 := by omega
      subst W
      exact hV.ne' (by simpa using hWV)
    have hVvalue : originalObjective (p * V) ≤ originalObjective (p * W) :=
      hvalue.trans (hWmax U hUD)
    have hwholemax : ∀ Z : ℕ, 0 < Z → 5040 ∣ Z → Z ∣ V →
        originalObjective (p * Z) ≤ originalObjective (p * W) := by
      intro Z _ hmZ hZV
      by_cases he : Z = V
      · simpa [he] using hVvalue
      · have hZlt : Z < V := lt_of_le_of_ne (Nat.le_of_dvd hV hZV) he
        apply hWmax Z
        simp [D, Nat.mem_divisors, hV.ne', hmZ, hZV, hZlt]
    have hparent : Real.log (p * V : ℕ) < Real.log (P * V : ℕ) := by
      apply Real.log_lt_log
      · exact_mod_cast Nat.mul_pos hp.pos hV
      · exact_mod_cast Nat.mul_lt_mul_of_pos_right hpP hV
    have hclass := restricted_divisor_maximum_strict_inventory hp (by norm_num) hV
      hmW hWV hW hpV (by linarith : 1 < Real.log (p * 5040 : ℕ)) hparent
      hsaturated (fun q hq he => forced_5040_active hclock hq he) hwholemax
    exact (not_lt_of_ge hVvalue) (h W hW hmW hWV hWlt hclass)

private theorem original_maximum_next_layer {p N q : ℕ}
    (hmax : originalMaximizes p N) (hclock : 1 < Real.log (N : ℝ))
    (hq : q.Prime) :
    goldenLayerMarginal q (N.factorization q + 1) < price (Real.log (N : ℝ)) := by
  have hN : 0 < N := by have := hmax.1; omega
  have hc := hmax.2.2 (N * q)
    (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hN.ne' hq.ne_zero))
    (hmax.2.1.trans (dvd_mul_right N q))
  have hd := prime_delta hmax.1 hq
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have ht := loglog_tangent hclock
    (by linarith : 1 < Real.log (N : ℝ) + Real.log q)
    (by linarith : Real.log (N : ℝ) ≠ Real.log (N : ℝ) + Real.log q)
  have hmul : goldenLayerMarginal q (N.factorization q + 1) * Real.log q <
      price (Real.log (N : ℝ)) * Real.log q := by
    nlinarith [hc]
  exact (mul_lt_mul_iff_left₀ hlq).mp (by simpa [mul_comm] using hmul)

private theorem original_maximum_removable_layer {p N q : ℕ}
    (hp : p.Prime) (hmax : originalMaximizes p N)
    (hclock : 1 < Real.log (N : ℝ)) (hq : q.Prime)
    (hrem : (5040 * p).factorization q < N.factorization q) :
    price (Real.log (N : ℝ)) < goldenLayerMarginal q (N.factorization q) := by
  have hN : 0 < N := by have := hmax.1; omega
  have hqN : q ∣ N := by
    by_contra h
    have hz := Nat.factorization_eq_zero_of_not_dvd h
    omega
  let T := N / q
  have hT : 0 < T := Nat.div_pos (Nat.le_of_dvd hN hqN) hq.pos
  have hTq : T * q = N := Nat.div_mul_cancel hqN
  have hfloorN := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (by norm_num : (5040 : ℕ) ≠ 0) hp.ne_zero) hN.ne').mpr hmax.2.1
  have hfloorT : 5040 * p ∣ T := by
    apply (Nat.factorization_le_iff_dvd
      (mul_ne_zero (by norm_num : (5040 : ℕ) ≠ 0) hp.ne_zero) hT.ne').mp
    rw [show T = N / q from rfl, Nat.factorization_div hqN]
    intro r
    by_cases hrq : r = q
    · subst r
      simpa [hq.factorization] using
        (show (5040 * p).factorization q ≤ N.factorization q - 1 by omega)
    · simpa [hq.factorization, hrq] using hfloorN r
  have hc := hmax.2.2 T (Nat.one_le_iff_ne_zero.mpr hT.ne') hfloorT
  have hT3 : (3 : ℝ) ≤ (T : ℝ) := by
    have hfloor3 : (3 : ℕ) ≤ 5040 * p := by nlinarith [hp.pos]
    exact_mod_cast hfloor3.trans (Nat.le_of_dvd hT hfloorT)
  have hTclock : 1 < Real.log (T : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hT)).mpr
      (Real.exp_one_lt_three.trans_le hT3)
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlog : Real.log (N : ℝ) = Real.log (T : ℝ) + Real.log q := by
    rw [← hTq, Nat.cast_mul, Real.log_mul
      (by exact_mod_cast hT.ne') (by exact_mod_cast hq.ne_zero)]
  have ht := loglog_tangent hclock hTclock
    (by linarith : Real.log (N : ℝ) ≠ Real.log (T : ℝ))
  have hstep : Real.log (T : ℝ) - Real.log (N : ℝ) = -Real.log q := by linarith
  rw [hstep] at ht
  have hd := prime_delta (Nat.one_le_iff_ne_zero.mpr hT.ne') hq
  have hfp : T.factorization q + 1 = N.factorization q := by
    have hf := congrArg (fun f : ℕ →₀ ℕ => f q)
      (Nat.factorization_mul hT.ne' hq.ne_zero)
    rw [hTq] at hf
    simpa only [Finsupp.add_apply, hq.factorization, Finsupp.single_eq_same] using hf.symm
  rw [hfp, hTq, ← hlog] at hd
  have hmul : price (Real.log (N : ℝ)) * Real.log q <
      goldenLayerMarginal q (N.factorization q) * Real.log q := by
    nlinarith [hc]
  exact (mul_lt_mul_iff_left₀ hlq).mp (by simpa [mul_comm] using hmul)

/-- Every full-domain original maximizing tie with `243 ≤ log N < p` has
exactly its mandatory p layer. Removing that layer leaves the complete strict
Euler inventory at the same actual clock, including absent and nonprime stacks. -/
theorem original_maximum_strict_inventory {p N : ℕ} (hp : p.Prime)
    (hmax : originalMaximizes p N) (hlate : 243 ≤ Real.log (N : ℝ))
    (hlarge : Real.log (N : ℝ) < (p : ℝ)) :
    N.factorization p = 1 ∧ ∃ U : ℕ, N = p * U ∧ 0 < U ∧ 5040 ∣ U ∧
      ¬p ∣ U ∧ ∀ q : ℕ,
        U.factorization q = optimalLayerCount (price (Real.log (N : ℝ))) q := by
  have hN : 0 < N := by have := hmax.1; omega
  have hclock : 1 < Real.log (N : ℝ) := by linarith
  have hprice : 0 < price (Real.log (N : ℝ)) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hclock))
  have hp7 : 7 < p := by
    have h : (7 : ℝ) < p := by linarith
    exact_mod_cast h
  have hp5040 : ¬p ∣ 5040 := by
    intro hd
    rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 * 7 by norm_num] at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · rcases hp.dvd_mul.mp hd with hd | hd
        · have h := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) (hp.dvd_of_dvd_pow hd)
          omega
        · have h := Nat.le_of_dvd (by norm_num : 0 < (3 : ℕ)) (hp.dvd_of_dvd_pow hd)
          omega
      · have h := Nat.le_of_dvd (by norm_num : 0 < (5 : ℕ)) hd
        omega
    · have h := Nat.le_of_dvd (by norm_num : 0 < (7 : ℕ)) hd
      omega
  have hfloorp : (5040 * p).factorization p = 1 := by
    rw [Nat.factorization_mul (by norm_num : (5040 : ℕ) ≠ 0) hp.ne_zero]
    simp [Nat.factorization_eq_zero_of_not_dvd hp5040, hp.factorization]
  have hpinactive : goldenLayerMarginal p 1 < price (Real.log (N : ℝ)) := by
    have hm := D5.S3.Arith.GoldenLayerMarginalDecay.golden_layer_marginal_le_inv_pow
      hp (a := 1) le_rfl
    have hm' : goldenLayerMarginal p 1 ≤ 1 / ((p : ℝ) * Real.log p) := by
      simpa only [pow_one, div_mul_eq_div_div, one_div] using hm
    exact hm'.trans_lt
      (D5.S3.Arith.Robin.EulerLayerPhaseSeparation.price_strictAnti hclock hlarge)
  have hpN : p ∣ N := (dvd_mul_left p 5040).trans hmax.2.1
  have hpone : N.factorization p = 1 := by
    have hepos := hp.factorization_pos_of_dvd hN.ne' hpN
    by_contra h
    have he : 1 < N.factorization p := by omega
    have hrem : (5040 * p).factorization p < N.factorization p := by
      rwa [hfloorp]
    have hactive := original_maximum_removable_layer hp hmax hclock hp hrem
    have hdec := golden_layer_strict_decrease hp (by norm_num : 1 ≤ (1 : ℕ)) he
    exact (lt_asymm hactive (hdec.trans hpinactive))
  obtain ⟨k, hk⟩ := hmax.2.1
  let U := 5040 * k
  have hNU : N = p * U := by dsimp [U]; rw [hk]; ring
  have hU : 0 < U := by
    by_contra h
    have hz : U = 0 := by omega
    rw [hz, Nat.mul_zero] at hNU
    omega
  have hmU : 5040 ∣ U := dvd_mul_right 5040 k
  have hfp : N.factorization p = U.factorization p + 1 := by
    rw [hNU, Nat.factorization_mul hp.ne_zero hU.ne']
    simp [hp.factorization, Nat.add_comm]
  have hpU : ¬p ∣ U := by
    intro hd
    have hepos := hp.factorization_pos_of_dvd hU.ne' hd
    omega
  have hfac (q : ℕ) (hqp : q ≠ p) : N.factorization q = U.factorization q := by
    rw [hNU, Nat.factorization_mul hp.ne_zero hU.ne']
    simp [hp.factorization, hqp]
  have hnext : ∀ q : ℕ, q.Prime →
      goldenLayerMarginal q (U.factorization q + 1) < price (Real.log (N : ℝ)) := by
    intro q hq
    by_cases hqp : q = p
    · subst q
      simpa [Nat.factorization_eq_zero_of_not_dvd hpU] using hpinactive
    · rw [← hfac q hqp]
      exact original_maximum_next_layer hmax hclock hq
  have hfacmU := (Nat.factorization_le_iff_dvd
    (by norm_num : (5040 : ℕ) ≠ 0) hU.ne').mpr hmU
  have hlast : ∀ q : ℕ, q.Prime → 0 < U.factorization q →
      price (Real.log (N : ℝ)) < goldenLayerMarginal q (U.factorization q) := by
    intro q hq hepos
    have hqp : q ≠ p := by
      intro heq
      subst q
      have hz := Nat.factorization_eq_zero_of_not_dvd hpU
      omega
    rcases eq_or_lt_of_le (hfacmU q) with he | he
    · rw [← he]
      exact forced_5040_active hlate hq (by omega)
    · have hfloorq : (5040 * p).factorization q = (5040 : ℕ).factorization q := by
        rw [Nat.factorization_mul (by norm_num : (5040 : ℕ) ≠ 0) hp.ne_zero]
        simp [hp.factorization, hqp]
      have hrem : (5040 * p).factorization q < N.factorization q := by
        rw [hfloorq, hfac q hqp]
        exact he
      have ha := original_maximum_removable_layer hp hmax hclock hq hrem
      rwa [hfac q hqp] at ha
  refine ⟨hpone, U, hNU, hU, hmU, hpU, ?_⟩
  intro q
  by_cases hq : q.Prime
  · have hi := positive_layers_eq_count_interval hprice hq
    apply Nat.le_antisymm
    · by_cases he : U.factorization q = 0
      · omega
      · have hmemb : U.factorization q ∈
            Set.Icc 1 (optimalLayerCount (price (Real.log (N : ℝ))) q) := by
          rw [← hi]
          exact ⟨by omega, hq, hlast q hq (by omega)⟩
        exact hmemb.2
    · by_contra h
      have hmemb : U.factorization q + 1 ∈
          Set.Icc 1 (optimalLayerCount (price (Real.log (N : ℝ))) q) :=
        ⟨by omega, by omega⟩
      rw [← hi] at hmemb
      exact (not_lt_of_ge (hnext q hq).le) hmemb.2.2
  · simp [Nat.factorization_eq_zero_of_not_prime U hq, optimalLayerCount, hq]

end D5.S3.Arith.Robin.RestrictedDivisorStrictInventory

namespace D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
#print axioms restricted_divisor_maximum_strict_inventory
#print axioms strict_5040_divisor_comparison_iff_inventory
#print axioms original_maximum_strict_inventory
end D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
