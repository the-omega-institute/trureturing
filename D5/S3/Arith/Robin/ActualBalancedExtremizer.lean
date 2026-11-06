/- GID: D5/S3/Arith/Robin/ActualBalancedExtremizer
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualBalancedExtremizer
   mirror-E: none(waiver:qualitative-all-integer-reduction)
   anchors: []
   utility: none
   digest: A Robin failure yields an attained minimum and a unique internal-price optimizer. -/



import D5.S3.Arith.Robin.ActualRobinInterval
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.GronwallUpperEnvelope

/-!
An original nonpositive Robin margin yields an attained global minimum.
A negative witness and the eventual Gronwall upper envelope confine a
minimum to a finite segment; if all margins are nonnegative, the original
nonpositive witness is already a minimum. Equality failures are retained.

Strict log-log tangency supports the same integer at its internal price.
Finite Robin safety and the genuine boundary optimizer extend strict
support to all positive integers. Uniqueness identifies the existing
strict and maximal prime-layer inventories and excludes every layer tie.

The classical minimum-to-CA mechanism overlaps Caveney--Nicolas--Sondow,
On SA, CA, and GA numbers, arXiv:1112.6010v2, section 2.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.ActualBalancedExtremizer

open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PaddingRatio

/-- A genuine tail lower bound; no conditionally complete liminf inference. -/
private theorem margin_eventually_ge (b : ℝ) (hb : b < 0) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → b ≤ robinLogMargin n := by
  have he : 0 < Real.exp (-b) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (neg_pos.mpr hb))
  obtain ⟨K, hK⟩ :=
    D5.S3.Weil.GronwallUpperEnvelope.gronwall_upper_envelope
      (Real.exp (-b) - 1) he
  refine ⟨max K 5041, ?_⟩
  intro n hn
  have hn' : 5041 ≤ n := (le_max_right _ _).trans hn
  have hnK : K ≤ n := (le_max_left _ _).trans hn
  have hpos : 0 < robinRatio n :=
    div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega)))
      (mul_pos (mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (by omega)))
        (loglog_pos hn'))
  have hratio : robinRatio n ≤ Real.exp (-b) := by
    have hu := hK n hnK
    dsimp only [robinRatio]
    linarith only [hu]
  rw [robin_log_margin_eq_neg_log hn']
  have hlog := (Real.log_le_iff_le_exp hpos).mpr hratio
  linarith only [hlog]

/-- The finite minimization is constructed from a negative witness, rather
than assumed. The other branch retains equality failures. -/
private theorem failure_minimum
    (hfailure : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n ≤ 0) :
    ∃ N : ℕ, 5040 < N ∧ robinLogMargin N ≤ 0 ∧
      ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m := by
  classical
  by_cases hneg : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n < 0
  · obtain ⟨n₀, hn₀, hc⟩ := hneg
    obtain ⟨K, hK⟩ := margin_eventually_ge (robinLogMargin n₀ / 2) (by linarith)
    let T := max K (n₀ + 1)
    let s := Finset.Ico 5041 T
    have hn₀s : n₀ ∈ s := by
      exact Finset.mem_Ico.mpr ⟨by omega,
        (Nat.lt_succ_self n₀).trans_le (le_max_right _ _)⟩
    obtain ⟨N, hNs, hNmin⟩ := s.exists_min_image robinLogMargin ⟨n₀, hn₀s⟩
    have hNn₀ : robinLogMargin N ≤ robinLogMargin n₀ := hNmin n₀ hn₀s
    refine ⟨N, ?_, hNn₀.trans hc.le, ?_⟩
    · have hNlo := (Finset.mem_Ico.mp hNs).1
      omega
    · intro m hm
      by_cases hmT : m < T
      · exact hNmin m (Finset.mem_Ico.mpr ⟨by omega, hmT⟩)
      · have hKm : K ≤ m := (le_max_left _ _).trans (Nat.le_of_not_gt hmT)
        have htail := hK m hKm
        linarith only [hNn₀, hc, htail]
  · obtain ⟨N, hN, hSN⟩ := hfailure
    refine ⟨N, hN, hSN, ?_⟩
    intro m hm
    have hnonneg : 0 ≤ robinLogMargin m := by
      by_contra h
      exact hneg ⟨m, hm, lt_of_not_ge h⟩
    exact hSN.trans hnonneg

/-- The supporting objective keeps the original integer, sigma/n and
internal slope. Distinct equal-margin integers also give strict support. -/
private theorem restricted_strict_support {N : ℕ} (hN : 5040 < N)
    (hminimum : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (m : ℕ) (hm : 5040 < m) (hmN : m ≠ N) :
    goldenResourceObjective (price (Real.log N)) m <
      goldenResourceObjective (price (Real.log N)) N := by
  have hlogs : Real.log (N : ℝ) ≠ Real.log (m : ℝ) := by
    intro heq
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega : 0 < m)
    have heqR : (N : ℝ) = (m : ℝ) := Real.strictMonoOn_log.injOn hN0 hm0 heq
    have heqNat : N = m := by exact_mod_cast heqR
    exact hmN heqNat.symm
  have ht : Real.log (Real.log (Real.log m)) - Real.log (Real.log (Real.log N)) <
      price (Real.log N) * (Real.log m - Real.log N) := by
    simpa only [D5.S3.Arith.Robin.ActualRobinClockCovariance.g, price, mul_comm] using
      D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
        (log_gt_one (by omega : 3 ≤ N)) (log_gt_one (by omega : 3 ≤ m)) hlogs
  have hs := hminimum m hm
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W] at hs
  dsimp only [robinThreshold] at hs
  rw [golden_resource_sigma_identity _ (by omega : 1 ≤ m),
    golden_resource_sigma_identity _ (by omega : 1 ≤ N)]
  change W m - price (Real.log N) * Real.log m <
    W N - price (Real.log N) * Real.log N
  linarith only [ht, hs]

/-- The finite Robin alternative is paid by an existing unconditional
theorem, transported through the public original-margin/ratio bridge. -/
private theorem finite_margin_pos {n : ℕ} (hn : 5040 < n) (hcap : n ≤ 55440) :
    0 < robinLogMargin n := by
  have hf := D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870
    hn (by omega : n < 223092870)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsR : 0 < (ArithmeticFunction.sigma 1 n : ℝ) :=
    Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega))
  have hll := loglog_pos (by omega : 5041 ≤ n)
  have hden : 0 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) :=
    mul_pos (Real.exp_pos _) hll
  have hratio_eq : robinRatio n = ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
      (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) := by
    simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
    ring
  have hratio_lt : robinRatio n < 1 := by
    rw [hratio_eq]
    exact (div_lt_one hden).mpr hf
  have hratio_pos : 0 < robinRatio n :=
    div_pos hsR (mul_pos (mul_pos (Real.exp_pos _) hnR) hll)
  rw [robin_log_margin_eq_neg_log (by omega : 5041 ≤ n)]
  exact neg_pos.mpr (Real.log_neg hratio_pos hratio_lt)

/-- Any actual original Robin failure has an attained global margin
minimum at the SAME integer that uniquely optimizes the original price
objective over EVERY positive integer at lambda = 1/(log N * log(log N)).
No attainment, bounded-tail, optimizer, endpoint-sign or GA2 premise is
assumed. Equality failures are included. All threshold ties are excluded
only after full-domain uniqueness has been proved. -/
theorem failure_has_unique_internal_optimizer
    (hfailure : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n ≤ 0) :
    ∃ N : ℕ, 55440 < N ∧ robinLogMargin N ≤ 0 ∧
      (∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m) ∧
      0 < price (Real.log N) ∧ price (Real.log N) < boundaryPrice ∧
      IsGoldenResourceOptimal (price (Real.log N)) N ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ N →
        goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) N) ∧
      N = strictInteger (price (Real.log N)) ∧
      N = maximalInteger (price (Real.log N)) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        price (Real.log N) ≠ goldenLayerMarginal p k) := by
  classical
  obtain ⟨N, hN, hSN, hminimum⟩ := failure_minimum hfailure
  have hlarge : 55440 < N := by
    by_contra h
    exact (not_lt_of_ge hSN) (finite_margin_pos hN (le_of_not_gt h))
  have hpricePos : 0 < price (Real.log N) := price_pos (log_gt_one (by omega))
  have hB : 5040 < boundaryCap := by rw [boundaryCap_eq_55440]; norm_num
  have hBN : boundaryCap < N := by simpa only [boundaryCap_eq_55440] using hlarge
  have hBpos : 1 ≤ boundaryCap := by omega
  have hNpos : 1 ≤ N := by omega
  have hBstrict := restricted_strict_support hN hminimum boundaryCap hB (by omega)
  have hBopt : IsGoldenResourceOptimal boundaryPrice boundaryCap :=
    (maximalInteger_spec boundaryPrice_spec.1).2.2.1
  have hbaseN := objective_support hBpos hNpos hBopt
  have hlogBN : Real.log (boundaryCap : ℝ) < Real.log (N : ℝ) :=
    Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hBN)
  have hprice : price (Real.log N) < boundaryPrice := by
    by_contra h
    have hge : boundaryPrice ≤ price (Real.log N) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hge (sub_pos.mpr hlogBN).le
    have hs := hBstrict
    rw [golden_resource_sigma_identity _ hBpos,
      golden_resource_sigma_identity _ hNpos] at hs
    change W boundaryCap - price (Real.log N) * Real.log boundaryCap <
      W N - price (Real.log N) * Real.log N at hs
    nlinarith only [hbaseN, hs, hmul]
  have hstrict : ∀ m : ℕ, 1 ≤ m → m ≠ N →
      goldenResourceObjective (price (Real.log N)) m <
        goldenResourceObjective (price (Real.log N)) N := by
    intro m hm hmN
    by_cases hmlarge : 5040 < m
    · exact restricted_strict_support hN hminimum m hmlarge hmN
    · have hmB : m < boundaryCap := by omega
      have hlogmB : Real.log (m : ℝ) < Real.log (boundaryCap : ℝ) :=
        Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hmB)
      have hbase := objective_support hBpos hm hBopt
      have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hprice) (sub_neg.mpr hlogmB)
      have hsmall : goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) boundaryCap := by
        rw [golden_resource_sigma_identity _ hm, golden_resource_sigma_identity _ hBpos]
        change W m - price (Real.log N) * Real.log m <
          W boundaryCap - price (Real.log N) * Real.log boundaryCap
        nlinarith only [hbase, hneg]
      exact hsmall.trans hBstrict
  have hopt : IsGoldenResourceOptimal (price (Real.log N)) N := by
    intro m hm
    by_cases heq : m = N
    · subst m
      exact le_rfl
    · exact (hstrict m hm heq).le
  have hunique : ∀ m : ℕ, 1 ≤ m →
      IsGoldenResourceOptimal (price (Real.log N)) m → m = N := by
    intro m hm hoptm
    by_contra hne
    exact (not_lt_of_ge (hoptm N hNpos)) (hstrict m hm hne)
  have hNs : N = strictInteger (price (Real.log N)) :=
    (hunique _ (strictInteger_pos hpricePos) (strict_is_optimal hpricePos)).symm
  have hNm : N = maximalInteger (price (Real.log N)) :=
    (hunique _ (maximalInteger_spec hpricePos).1 (maximalInteger_spec hpricePos).2.2.1).symm
  refine ⟨N, hlarge, hSN, hminimum, hpricePos, hprice, hopt, hstrict, hNs, hNm, ?_⟩
  intro p k hp hk heq
  have hw := (weak_layer_iff hpricePos hp hk).mpr heq.le
  have hs : k ≤ (strictInteger (price (Real.log N))).factorization p := by
    simpa only [← hNs, ← hNm] using hw
  exact (ne_of_lt ((strict_layer_iff hpricePos hp hk).mp hs)) heq

end D5.S3.Arith.Robin.ActualBalancedExtremizer
