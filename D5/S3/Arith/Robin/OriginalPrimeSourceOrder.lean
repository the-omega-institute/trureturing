/- GID: D5/S3/Arith/Robin/OriginalPrimeSourceOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalPrimeSourceOrder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Legal two-prime exchange orders original clocks and nests complete inventories. -/

import D5.S3.Arith.Robin.OriginalMaximumPurePackets
import D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
import D5.S3.Arith.Robin.ActualTwoPriceDefect

/-!
The legal exchange is the late, large-label branch of AVB10--AVB14 in
`Library/ArithSums/nicolas2025comparison.md`. Maximality is always the literal
original positive-integer comparison on the complete `5040*p` class.
The result supplies the closed inventory interval when the two inventories
agree. It asserts neither attainment nor cofinal good-edge existence, and
pays no signed moment or normalizer transfer.
-/

noncomputable section
open Classical Set

namespace D5.S3.Arith.Robin.OriginalPrimeSourceOrder

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.OriginalMaximumPurePackets
open D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount

local notation "λ₀" => D5.S3.Arith.Robin.ActualRobinClockCovariance.g
local notation "W" => (fun n : ℕ =>
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / (n : ℝ)))

private theorem inventory_is_strict_integer {U : ℕ} (hU : 0 < U) {t : ℝ}
    (ht : 1 < t)
    (hcounts : ∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ t) q) :
    U = strictInteger (λ₀ t) := by
  have hprice : 0 < λ₀ t := price_pos ht
  apply Nat.eq_of_factorization_eq hU.ne'
    (by have := strictInteger_pos hprice; omega)
  intro q
  rw [hcounts, strictInteger_counts hprice]

private theorem inventory_label_absent {U q : ℕ} (hU : 0 < U) (hq : q.Prime)
    {t : ℝ} (ht : 1 < t) (htq : t < (q : ℝ))
    (hcounts : ∀ s : ℕ, U.factorization s = optimalLayerCount (λ₀ t) s) :
    ¬q ∣ U :=
  first_absent hU hq ht (htq.trans (first_clock_spec hq).1).le hcounts

private theorem first_layer_euler {p U : ℕ} (hp : p.Prime) (hU : 0 < U)
    (hpU : ¬p ∣ U) :
    W (p * U) = W U + goldenLayerMarginal p 1 * Real.log p := by
  have hd := golden_resource_objective_single_layer_delta 0 (by omega : 1 ≤ U) hp
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ U),
    golden_resource_sigma_identity 0 (by nlinarith [hp.pos] : 1 ≤ U * p),
    Nat.factorization_eq_zero_of_not_dvd hpU] at hd
  simp only [zero_mul, sub_zero, zero_add] at hd
  rw [Nat.mul_comm U p] at hd
  linarith

/-- The actual opposite-class competitors exclude a reversed pair of clocks.
Both swapped layers are first layers; all four integers retain the full core. -/
private theorem legal_exchange_clock_order {p r U V : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p < r) (hU : 0 < U) (hV : 0 < V)
    (hcoreU : 5040 ∣ U) (hcoreV : 5040 ∣ V)
    (hpU : ¬p ∣ U) (hrU : ¬r ∣ U) (hpV : ¬p ∣ V) (hrV : ¬r ∣ V)
    (hmaxN : originalMaximizes p (p * U))
    (hmaxM : originalMaximizes r (r * V)) :
    Real.log r - Real.log p ≤ Real.log (r * V : ℕ) - Real.log (p * U : ℕ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV
  have hdelta : 0 < Real.log (r : ℝ) - Real.log p :=
    sub_pos.mpr (Real.log_lt_log hpR (by exact_mod_cast hpr))
  have hpVfloor : 5040 * p ∣ p * V := by
    simpa [Nat.mul_comm 5040 p] using Nat.mul_dvd_mul_left p hcoreV
  have hrUfloor : 5040 * r ∣ r * U := by
    simpa [Nat.mul_comm 5040 r] using Nat.mul_dvd_mul_left r hcoreU
  have hsmall := legal_clock hp.pos (by nlinarith [hp.pos] : 1 ≤ p * V) hpVfloor
  have hcN := hmaxN.2.2 (p * V) (by nlinarith [hp.pos]) hpVfloor
  have hcM := hmaxM.2.2 (r * U) (by nlinarith [hr.pos]) hrUfloor
  have hlogsN : Real.log (p * U : ℕ) = Real.log p + Real.log U := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hUR.ne']
  have hlogsM : Real.log (r * V : ℕ) = Real.log r + Real.log V := by
    rw [Nat.cast_mul, Real.log_mul hrR.ne' hVR.ne']
  have hlogsPV : Real.log (p * V : ℕ) = Real.log p + Real.log V := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hVR.ne']
  have hlogsRU : Real.log (r * U : ℕ) = Real.log r + Real.log U := by
    rw [Nat.cast_mul, Real.log_mul hrR.ne' hUR.ne']
  have hEuler : W (p * V) + W (r * U) = W (p * U) + W (r * V) := by
    rw [first_layer_euler hp hV hpV, first_layer_euler hr hU hrU,
      first_layer_euler hp hU hpU, first_layer_euler hr hV hrV]
    ring
  by_contra horder
  have hreverse : Real.log (r * V : ℕ) - Real.log (p * U : ℕ) <
      Real.log r - Real.log p := lt_of_not_ge horder
  have hrect := strict_loglog_rectangle hsmall
    (b := Real.log (p * U : ℕ)) (c := Real.log (r * V : ℕ))
    (d := Real.log (r * U : ℕ)) (by linarith) (by linarith) (by linarith)
  unfold originalObjective at hcN hcM
  linarith

/-- Every pair of original maximizing ties in the late, large-label regime
has ordered clocks and nested complete inventories. Equal inventories supply
the full closed inventory interval consumed by `GoodEdge`. -/
theorem original_prime_source_order {p r N M : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hmaxN : originalMaximizes p N) (hmaxM : originalMaximizes r M)
    (hlateN : 243 ≤ Real.log (N : ℝ)) (hlateM : 243 ≤ Real.log (M : ℝ))
    (hlargeN : Real.log (N : ℝ) < (p : ℝ))
    (hlargeM : Real.log (M : ℝ) < (p : ℝ)) :
    ∃ U V : ℕ, N = p * U ∧ M = r * V ∧ 0 < U ∧ 0 < V ∧
      5040 ∣ U ∧ 5040 ∣ V ∧ ¬p ∣ U ∧ ¬r ∣ U ∧ ¬p ∣ V ∧ ¬r ∣ V ∧
      U ∣ V ∧ Real.log r - Real.log p ≤ Real.log (M : ℝ) - Real.log (N : ℝ) ∧
      Real.log (N : ℝ) < Real.log (M : ℝ) ∧
      (∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ (Real.log (N : ℝ))) q) ∧
      (∀ q : ℕ, V.factorization q = optimalLayerCount (λ₀ (Real.log (M : ℝ))) q) ∧
      (U = V → ∀ t ∈ Icc (Real.log (N : ℝ)) (Real.log (M : ℝ)),
        ∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ t) q) := by
  have hprR : (p : ℝ) < r := by exact_mod_cast hpr
  have hN1 : 1 < Real.log (N : ℝ) := by linarith
  have hM1 : 1 < Real.log (M : ℝ) := by linarith
  obtain ⟨_, U, hNU, hU, hcoreU, hpU, hcountsU⟩ :=
    original_maximum_strict_inventory hp hmaxN hlateN hlargeN
  obtain ⟨_, V, hMV, hV, hcoreV, hrV, hcountsV⟩ :=
    original_maximum_strict_inventory hr hmaxM hlateM (hlargeM.trans hprR)
  have hrU := inventory_label_absent hU hr hN1 (hlargeN.trans hprR) hcountsU
  have hpV := inventory_label_absent hV hp hM1 hlargeM hcountsV
  have horder := legal_exchange_clock_order hp hr hpr hU hV hcoreU hcoreV
    hpU hrU hpV hrV (hNU ▸ hmaxN) (hMV ▸ hmaxM)
  rw [← hNU, ← hMV] at horder
  have hdelta : 0 < Real.log (r : ℝ) - Real.log p :=
    sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hp.pos) hprR)
  have hNM : Real.log (N : ℝ) < Real.log (M : ℝ) := by linarith
  have hpriceN : 0 < λ₀ (Real.log (N : ℝ)) := price_pos hN1
  have hpriceM : 0 < λ₀ (Real.log (M : ℝ)) := price_pos hM1
  have hIU := inventory_is_strict_integer hU hN1 hcountsU
  have hIV := inventory_is_strict_integer hV hM1 hcountsV
  have hUV : U ∣ V := by
    rw [hIU, hIV]
    exact strictInteger_dvd hpriceN hpriceM
      (price_antitone hN1 hNM.le)
  refine ⟨U, V, hNU, hMV, hU, hV, hcoreU, hcoreV, hpU, hrU, hpV, hrV,
    hUV, horder, hNM, hcountsU, hcountsV, ?_⟩
  intro heq t ht q
  have ht1 : 1 < t := hN1.trans_le ht.1
  have hpriceT : 0 < λ₀ t := price_pos ht1
  have hUt : U ∣ strictInteger (λ₀ t) := by
    rw [hIU]
    exact strictInteger_dvd hpriceN hpriceT
      (price_antitone hN1 ht.1)
  have htV : strictInteger (λ₀ t) ∣ V := by
    rw [hIV]
    exact strictInteger_dvd hpriceT hpriceM
      (price_antitone ht1 ht.2)
  have htU : strictInteger (λ₀ t) = U := Nat.dvd_antisymm (by simpa only [heq] using htV) hUt
  rw [← htU, strictInteger_counts hpriceT]

end D5.S3.Arith.Robin.OriginalPrimeSourceOrder

#print axioms D5.S3.Arith.Robin.OriginalPrimeSourceOrder.original_prime_source_order
