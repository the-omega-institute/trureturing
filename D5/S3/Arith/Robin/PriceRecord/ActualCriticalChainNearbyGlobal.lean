import D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import D5.S3.Arith.Robin.ActualTwoPriceDefect
import D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
The finite descending chain of smallest actual minimum-secant predecessors
preserves support on the original integer prefix. At its first logarithmic
budget crossing, the last edge's gap makes the predecessor affordable for every
prime through its next prime. Layer thresholds and the least finite tie then
give an actual least global fixed-price optimizer.

The constants are uniform over all positive prices and all original strict
records. The original bank, prescribed-b payment and RH are not concluded.

Ordinary mathematical input: Sections I--III of
answer-critical-predecessor-chain-common-stock-20261112.txt,
SHA256 2f645d8859aabb812a8e0220cef5199e616ef9da313fd98edddc2cbfbf863e2b.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal

open Finset Filter
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
open D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap

private def Record (mu : ℝ) (r : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n < r →
    goldenResourceObjective mu n < goldenResourceObjective mu r

private def Supports (m : ℕ) (t : ℝ) (r : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ m →
    goldenResourceObjective t n ≤ goldenResourceObjective t r

private def LeastSupports (m : ℕ) (t : ℝ) (r : ℕ) : Prop :=
  Supports m t r ∧ ∀ n : ℕ, 0 < n → n ≤ m →
    goldenResourceObjective t n = goldenResourceObjective t r → r ≤ n

private def ell (n : ℕ) : ℝ :=
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)

private def secant (r q : ℕ) : ℝ :=
  (ell r - ell q) / Real.log ((r : ℝ) / q)

private theorem price_formula (t : ℝ) {n : ℕ} (hn : 0 < n) :
    goldenResourceObjective t n = ell n - t * Real.log n :=
  golden_resource_sigma_identity t (by omega)

private theorem gap_identity {r q : ℕ} (hr : 0 < r) (hq : 0 < q) :
    Real.log ((r : ℝ) / q) = Real.log r - Real.log q :=
  Real.log_div (by exact_mod_cast hr.ne') (by exact_mod_cast hq.ne')

private theorem log_strict {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Real.log (a : ℝ) < Real.log b :=
  Real.log_lt_log (by exact_mod_cast ha) (by exact_mod_cast hab)

private theorem gap_positive {r q : ℕ} (hq : 0 < q) (hqr : q < r) :
    0 < Real.log ((r : ℝ) / q) := by
  rw [gap_identity (hq.trans hqr) hq]
  exact sub_pos.mpr (log_strict hq hqr)

private def MinSecant (r q : ℕ) : Prop :=
  0 < q ∧ q < r ∧ ∀ n : ℕ, 0 < n → n < r → secant r q ≤ secant r n

private theorem exists_min_secant {r : ℕ} (hr : 1 < r) : ∃ q, MinSecant r q := by
  classical
  obtain ⟨q, hq, hmin⟩ := (Icc 1 (r - 1)).exists_min_image (secant r)
    ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨hq1, hqr⟩ := mem_Icc.mp hq
  refine ⟨q, by omega, by omega, ?_⟩
  intro n hn hnr
  exact hmin n (mem_Icc.mpr ⟨by omega, by omega⟩)

/- Nat.find, rather than an arbitrary finite argmin, fixes the essential tie rule. -/
private def predecessor (r : ℕ) : ℕ :=
  by
    classical
    exact if hr : 1 < r then Nat.find (exists_min_secant hr) else 1

private def critical (r : ℕ) : ℝ := secant r (predecessor r)

private theorem predecessor_spec {r : ℕ} (hr : 1 < r) :
    MinSecant r (predecessor r) := by
  classical
  simpa only [predecessor, dite_eq_left hr] using Nat.find_spec (exists_min_secant hr)

private theorem predecessor_smallest {r q : ℕ} (hr : 1 < r)
    (hq : MinSecant r q) : predecessor r ≤ q := by
  classical
  simpa only [predecessor, dite_eq_left hr] using Nat.find_min' (exists_min_secant hr) hq

private theorem secant_support {r : ℕ} (hr : 1 < r) {u : ℝ}
    (hrecord : Record u r) :
    u < critical r ∧
    goldenResourceObjective (critical r) (predecessor r) =
      goldenResourceObjective (critical r) r ∧
    LeastSupports r (critical r) (predecessor r) := by
  let q := predecessor r
  let v := critical r
  obtain ⟨hq, hqr, hmin⟩ := predecessor_spec hr
  have hr0 : 0 < r := by omega
  have hell0 (n : ℕ) (hn : 0 < n) : goldenResourceObjective 0 n = ell n := by
    simpa only [zero_mul, sub_zero] using price_formula 0 hn
  have hmin0 : ∀ n : ℕ, 0 < n → n < r →
      (goldenResourceObjective 0 r - goldenResourceObjective 0 q) /
          Real.log ((r : ℝ) / q) ≤
        (goldenResourceObjective 0 r - goldenResourceObjective 0 n) /
          Real.log ((r : ℝ) / n) := by
    intro n hn hnr
    simpa only [secant, hell0 r hr0, hell0 q hq, hell0 n hn] using hmin n hn hnr
  have hbase : u < v ∧ goldenResourceObjective v q = goldenResourceObjective v r ∧
      Supports r v r := by
    simpa only [v, q, critical, secant, Supports, hell0 r hr0,
      hell0 (predecessor r) hq] using
      ActualMinSecantPredecessorLogGap.secant_support hq hqr hrecord hmin0
  obtain ⟨huv, htie, hsupport⟩ := hbase
  have hmax : Supports r v q := by
    intro n hn hnr
    rw [htie]
    exact hsupport n hn hnr
  refine ⟨huv, htie, hmax, ?_⟩
  intro n hn hnr heq
  by_contra hnot
  have hnq : n < q := by omega
  have hnr' : n < r := hnq.trans hqr
  have hsec : secant r n = v := by
    apply (div_eq_iff (gap_positive hn hnr').ne').mpr
    rw [htie, price_formula v hn, price_formula v hr0] at heq
    rw [gap_identity hr0 hn]
    nlinarith
  have hnmin : MinSecant r n := by
    refine ⟨hn, hnr', ?_⟩
    intro k hk hkr
    rw [hsec]
    exact hmin k hk hkr
  exact (not_lt_of_ge (predecessor_smallest hr hnmin)) hnq

private theorem record_of_least {m r : ℕ} (hrm : r ≤ m) {t : ℝ}
    (h : LeastSupports m t r) : Record t r := by
  intro n hn hnr
  have hle := h.1 n hn (hnr.le.trans hrm)
  apply lt_of_le_of_ne hle
  intro heq
  exact (not_lt_of_ge (h.2 n hn (hnr.le.trans hrm) heq)) hnr

private theorem earlier_record {m r : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    {mu t : ℝ} (hmut : mu < t) (hsupport : Supports m t r) : Record mu r := by
  intro n hn hnr
  have hle := hsupport n hn (hnr.le.trans hrm)
  have hlog := log_strict hn hnr
  have hpos := mul_pos (sub_pos.mpr hmut) (sub_pos.mpr hlog)
  rw [price_formula t hn, price_formula t hr] at hle
  rw [price_formula mu hn, price_formula mu hr]
  nlinarith

/- Support is extended to the ORIGINAL domain by an explicit price-change
inequality above r; no globality, divisibility, or inventory monotonicity is used. -/
private theorem support_step {m r : ℕ} (hr : 1 < r) (hrm : r ≤ m)
    {u : ℝ} (h : LeastSupports m u r) :
    u < critical r ∧ LeastSupports m (critical r) (predecessor r) := by
  obtain ⟨huv, htie, hlocal⟩ := secant_support hr (record_of_least hrm h)
  have hr0 : 0 < r := by omega
  have higher (n : ℕ) (hnr : r < n) (hnm : n ≤ m) :
      goldenResourceObjective (critical r) n < goldenResourceObjective (critical r) r := by
    have hn : 0 < n := hr0.trans hnr
    have hle := h.1 n hn hnm
    have hpos := mul_pos (sub_pos.mpr huv) (sub_pos.mpr (log_strict hr0 hnr))
    rw [price_formula u hn, price_formula u hr0] at hle
    rw [price_formula (critical r) hn, price_formula (critical r) hr0]
    nlinarith
  refine ⟨huv, ?_, ?_⟩
  · intro n hn hnm
    by_cases hnr : n ≤ r
    · exact hlocal.1 n hn hnr
    · rw [htie]
      exact (higher n (by omega) hnm).le
  · intro n hn hnm heq
    by_cases hnr : n ≤ r
    · exact hlocal.2 n hn hnr heq
    · have := (predecessor_spec hr).2.1
      omega

private def node (m : ℕ) : ℕ → ℕ
  | 0 => m
  | i + 1 => predecessor (node m i)

private def entryPrice (mu : ℝ) (m : ℕ) : ℕ → ℝ
  | 0 => mu
  | i + 1 => if 1 < node m i then critical (node m i) else entryPrice mu m i

private theorem node_shift (m i : ℕ) : node m (i + 1) = node (predecessor m) i := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [node] using congrArg predecessor ih

/- This is a genuinely finite descending chain ending at 1, subsequently
constant. Its prefix through the first budget crossing is used below. -/
private theorem chain_terminates {m : ℕ} (hm : 0 < m) : ∃ N, node m N = 1 := by
  revert hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases h : 1 < m
    · obtain ⟨hq, hqm, _⟩ := predecessor_spec h
      obtain ⟨N, hN⟩ := ih (predecessor m) hqm hq
      exact ⟨N + 1, (node_shift m N).trans hN⟩
    · have : m = 1 := by omega
      exact ⟨0, this⟩

private theorem chain_state {m : ℕ} (hm : 0 < m) {mu : ℝ}
    (hrecord : Record mu m) (i : ℕ) :
    0 < node m i ∧ node m i ≤ m ∧ Record mu (node m i) ∧
      mu ≤ entryPrice mu m i ∧ LeastSupports m (entryPrice mu m i) (node m i) := by
  induction i with
  | zero =>
    change 0 < m ∧ m ≤ m ∧ Record mu m ∧ mu ≤ mu ∧ LeastSupports m mu m
    refine ⟨hm, le_rfl, hrecord, le_rfl, ?_, ?_⟩
    · intro n hn hnm
      rcases hnm.eq_or_lt with rfl | hnm
      · exact le_rfl
      · exact (hrecord n hn hnm).le
    · intro n hn hnm heq
      by_contra h
      exact (ne_of_lt (hrecord n hn (by omega))) heq
  | succ i ih =>
    obtain ⟨hr, hrm, hrec, hprice, hsupport⟩ := ih
    by_cases hr1 : 1 < node m i
    · obtain ⟨hq, hqr, _⟩ := predecessor_spec hr1
      obtain ⟨huv, hnext⟩ := support_step hr1 hrm hsupport
      have hmunu := hprice.trans_lt huv
      have hqrecord := earlier_record hq (hqr.le.trans hrm) hmunu hnext.1
      simpa only [node, entryPrice, ite_eq_left hr1] using
        And.intro hq (And.intro (hqr.le.trans hrm)
          (And.intro hqrecord (And.intro hmunu.le hnext)))
    · have hrone : node m i = 1 := by omega
      have hpred : predecessor (node m i) = node m i := by
        rw [predecessor, dite_eq_right hr1, hrone]
      simpa only [node, entryPrice, ite_eq_right hr1, hpred] using
        And.intro hr (And.intro hrm (And.intro hrec (And.intro hprice hsupport)))

/- The incoming price at every nonterminal node is strictly below its next
critical price, by support_step. Therefore these are the strictly increasing
actual critical prices, with the SAME original mu record at every node. -/
private theorem first_crossing {m : ℕ} (hm : 0 < m) {mu B : ℝ}
    (hrecord : Record mu m) (hB : 0 < B) (hBm : B < Real.log m) :
    ∃ a q : ℕ, 1 < a ∧ a ≤ m ∧ Record mu a ∧ q = predecessor a ∧
      0 < q ∧ q < a ∧
      Real.log m - Real.log a < B ∧ B ≤ Real.log m - Real.log q ∧
      mu < critical a ∧ LeastSupports m (critical a) q := by
  classical
  obtain ⟨N, hN⟩ := chain_terminates hm
  have hex : ∃ i, B ≤ Real.log m - Real.log (node m i) := by
    refine ⟨N, ?_⟩
    simpa only [hN, Nat.cast_one, Real.log_one, sub_zero] using hBm.le
  let s := Nat.find hex
  have hs : B ≤ Real.log m - Real.log (node m s) := Nat.find_spec hex
  have hs0 : s ≠ 0 := by
    intro heq
    have : B ≤ 0 := by simpa only [heq, node, sub_self] using hs
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs0
  have hprev : Real.log m - Real.log (node m k) < B := by
    exact lt_of_not_ge (Nat.find_min hex (by omega : k < s))
  obtain ⟨ha, ham, harec, hprice, hasupport⟩ := chain_state hm hrecord k
  have ha1 : 1 < node m k := by
    by_contra hn
    have he : node m k = 1 := by omega
    have : Real.log m < B := by
      simpa only [he, Nat.cast_one, Real.log_one, sub_zero] using hprev
    linarith
  obtain ⟨hq, hqa, _⟩ := predecessor_spec ha1
  obtain ⟨hstep, hqsupport⟩ := support_step ha1 ham hasupport
  refine ⟨node m k, predecessor (node m k), ha1, ham, harec, rfl,
    hq, hqa, hprev, ?_, hprice.trans_lt hstep, hqsupport⟩
  simpa only [hk, Nat.succ_eq_add_one, node] using hs

private theorem largest_prime_two {r : ℕ} (hr : 1 < r) : 2 ≤ largestPrime r := by
  obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
  exact hp.two_le.trans
    (le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hpr, by omega⟩))

private theorem prime_not_dvd_above {r p : ℕ} (hr : 0 < r) (hp : p.Prime)
    (h : largestPrime r < p) : ¬p ∣ r := by
  intro hd
  have := le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hd, hr.ne'⟩)
  exact (not_lt_of_ge this) h

private theorem prime_after_exists (P : ℕ) : ∃ q : ℕ, q.Prime ∧ P < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (P + 1)
  exact ⟨q, hp, by omega⟩

private def primeAfter (P : ℕ) : ℕ := Nat.find (prime_after_exists P)

private theorem prime_after_spec (P : ℕ) :
    (primeAfter P).Prime ∧ P < primeAfter P := Nat.find_spec (prime_after_exists P)

private theorem prime_after_bertrand {P : ℕ} (hP : 2 ≤ P) : primeAfter P < 2 * P := by
  obtain ⟨q, hq, hPq, hqP⟩ := Nat.exists_prime_lt_and_le_two_mul P (by omega)
  have hmin : primeAfter P ≤ q := Nat.find_min' (prime_after_exists P) ⟨hq, hPq⟩
  have hne : q ≠ 2 * P := by
    intro he
    have hd : 2 ∣ q := by rw [he]; exact dvd_mul_right 2 P
    have hq2 := (Nat.dvd_prime hq).mp hd
    rcases hq2 with h | h
    · omega
    · omega
  omega

private theorem occupied_price {m r p : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    (hp : p.Prime) (hpr : p ∣ r) {t : ℝ} (h : Supports m t r) :
    t ≤ goldenLayerMarginal p (r.factorization p) := by
  have ha : 1 ≤ r.factorization p := (hp.dvd_iff_one_le_factorization hr.ne').mp hpr
  exact ActualMinSecantPredecessorLogGap.occupied_top_price hr hp
    (fun n hn hnr => h n hn (hnr.trans hrm)) ha

private theorem occupied_strict_price {m r p : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    (hp : p.Prime) (hpr : p ∣ r) {t : ℝ} (h : LeastSupports m t r) :
    t < goldenLayerMarginal p (r.factorization p) := by
  have hle := occupied_price hr hrm hp hpr h.1
  apply lt_of_le_of_ne hle
  intro heq
  have hdpos : 0 < r / p := Nat.div_pos (Nat.le_of_dvd hr hpr) hp.pos
  have hmul := Nat.div_mul_cancel hpr
  have hfac : (r / p).factorization p + 1 = r.factorization p := by
    have hf := congrArg (fun n : ℕ => n.factorization p) hmul
    simpa [Nat.factorization_mul hdpos.ne' hp.ne_zero, hp.factorization] using hf
  have hdelta := golden_resource_objective_single_layer_delta t (by omega : 1 ≤ r / p) hp
  rw [hmul, hfac, ← heq, sub_self, zero_mul] at hdelta
  have htie : goldenResourceObjective t (r / p) = goldenResourceObjective t r := by
    linarith
  have hleast := h.2 (r / p) hdpos ((Nat.div_le_self _ _).trans hrm) htie
  exact (not_lt_of_ge hleast) (Nat.div_lt_self hr hp.one_lt)

private theorem affordable_next_price {m r p : ℕ} (hr : 0 < r) (hp : p.Prime)
    (hbudget : r * p ≤ m) {t : ℝ} (h : Supports m t r) :
    goldenLayerMarginal p (r.factorization p + 1) ≤ t := by
  have hc := h (r * p) (Nat.mul_pos hr hp.pos) hbudget
  have hd := golden_resource_objective_single_layer_delta t (by omega : 1 ≤ r) hp
  have hnet : 0 ≤ (t - goldenLayerMarginal p (r.factorization p + 1)) * Real.log p := by
    nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp.log_pos).mp hnet)

/- All p<=Q are ACTUALLY affordable. All p>Q are absent and are controlled
by the strictly decreasing actual first-layer price. The imported criterion's
sufficiency proof sums the objective on the union of the two finite supports. -/
private theorem budget_to_global {m r : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    {t : ℝ} (ht : 0 < t) (h : Supports m t r)
    (hbudget : r * primeAfter (largestPrime r) ≤ m) :
    IsGoldenResourceOptimal t r := by
  let Q := primeAfter (largestPrime r)
  obtain ⟨hQ, hPQ⟩ := prime_after_spec (largestPrime r)
  have hQmissing := prime_not_dvd_above hr hQ hPQ
  have hQprice := affordable_next_price hr hQ hbudget h
  rw [Nat.factorization_eq_zero_of_not_dvd hQmissing, zero_add] at hQprice
  apply (golden_resource_optimal_iff_layer_thresholds ht (by omega : 1 ≤ r)).mpr
  refine ⟨?_, fun p hp hpr => occupied_price hr hrm hp hpr h⟩
  intro p hp
  by_cases hpQ : p ≤ Q
  · exact affordable_next_price hr hp
      ((Nat.mul_le_mul_left r hpQ).trans hbudget) h
  · have hQp : Q < p := by omega
    have hmissing := prime_not_dvd_above hr hp (hPQ.trans hQp)
    rw [Nat.factorization_eq_zero_of_not_dvd hmissing, zero_add]
    exact golden_layer_marginal_one_threshold_of_le hp hQ hQp.le hQprice

/- Leastness rules out every occupied zero layer. This identifies the SAME
actual r with the existing strictInteger, then reuses its divisibility-least
global property. There is no canonical substitution for the original m. -/
private theorem budget_to_least_global {m r : ℕ} (hr : 0 < r) (hrm : r ≤ m)
    {t : ℝ} (ht : 0 < t) (h : LeastSupports m t r)
    (hbudget : r * primeAfter (largestPrime r) ≤ m) :
    (∀ n : ℕ, 0 < n → goldenResourceObjective t n ≤ goldenResourceObjective t r) ∧
    (∀ n : ℕ, 0 < n → goldenResourceObjective t n = goldenResourceObjective t r → r ≤ n) := by
  have hg := budget_to_global hr hrm ht h.1 hbudget
  have hthreshold := (golden_resource_optimal_iff_layer_thresholds ht (by omega)).mp hg
  have hcounts (p : ℕ) : r.factorization p = optimalLayerCount t p := by
    by_cases hp : p.Prime
    · apply le_antisymm
      · by_cases hd : p ∣ r
        · have ha : 1 ≤ r.factorization p := (hp.dvd_iff_one_le_factorization hr.ne').mp hd
          have hactive : r.factorization p ∈
              {k : ℕ | 1 ≤ k ∧ p.Prime ∧ t < goldenLayerMarginal p k} :=
            ⟨ha, hp, occupied_strict_price hr hrm hp hd h⟩
          rw [positive_layers_eq_count_interval ht hp] at hactive
          exact hactive.2
        · simp only [Nat.factorization_eq_zero_of_not_dvd hd, Nat.zero_le]
      · by_contra hn
        have ha : r.factorization p + 1 ≤ optimalLayerCount t p := by omega
        have hmem : r.factorization p + 1 ∈
            {k : ℕ | 1 ≤ k ∧ p.Prime ∧ t < goldenLayerMarginal p k} := by
          rw [positive_layers_eq_count_interval ht hp]
          exact ⟨by omega, ha⟩
        exact (not_lt_of_ge (hthreshold.1 p hp)) hmem.2.2
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp, optimalLayerCount, hp]
  have hspec := strictInteger_spec ht
  have hcanonical : r = strictInteger t := by
    apply Nat.eq_of_factorization_eq hr.ne' (by have := hspec.1; omega)
    intro p
    exact (hcounts p).trans (strictInteger_counts ht p).symm
  refine ⟨fun n hn => hg n (by omega), ?_⟩
  intro n hn heq
  have hnopt : IsGoldenResourceOptimal t n := by
    intro k hk
    rw [heq]
    exact hg k hk
  rw [hcanonical]
  exact Nat.le_of_dvd hn (hspec.2.2.2 n (by omega) hnopt)

/- The uniform quantifier order is obtained on the space of ALL pairs
(actual integer, original positive price) satisfying the full record condition.
The private UnitRate in the supplier is only projected; no exposure is needed. -/
private theorem uniform_mass :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, 2 ≤ r → ∀ mu : ℝ, 0 < mu → Record mu r →
      A ≤ (largestPrime r : ℝ) →
      (largestPrime r : ℝ) / 2 ≤ Real.log r ∧
        Real.log r ≤ 2 * (largestPrime r : ℝ) := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ Record v.2 v.1}
  let r : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (r x)
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have hratio : Tendsto (fun x => Real.log (r x : ℝ) / P x) l (𝓝 1) :=
    (record_mass_limits r mu (fun x => x.2.1) (fun x => x.2.2.1)
      (fun x => x.2.2.2) hP).2.2.1
  have hlo : ∀ᶠ x in l, (1 / 2 : ℝ) < Real.log (r x : ℝ) / P x :=
    hratio.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hhi : ∀ᶠ x in l, Real.log (r x : ℝ) / P x < 2 :=
    hratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_comap.mp (hlo.and hhi))
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn t ht hrec hlarge
  let x : S := ⟨(n, t), hn, ht, hrec⟩
  have hx := hA (largestPrime n : ℝ) ((le_max_left A 2).trans hlarge) x rfl
  have hpos : (0 : ℝ) < largestPrime n := by
    have := largest_prime_two (by omega : 1 < n)
    exact_mod_cast (by omega : 0 < largestPrime n)
  have hl := (lt_div_iff₀ hpos).mp hx.1
  have hh := (div_lt_iff₀ hpos).mp hx.2
  constructor <;> linarith

private theorem node_prime_bound {A : ℝ} (hA : 0 < A)
    (hmass : ∀ r : ℕ, 2 ≤ r → ∀ mu : ℝ, 0 < mu → Record mu r →
      A ≤ (largestPrime r : ℝ) →
      (largestPrime r : ℝ) / 2 ≤ Real.log r ∧ Real.log r ≤ 2 * (largestPrime r : ℝ))
    {m r : ℕ} (hm : 2 ≤ m) (hr : 1 < r) (hrm : r ≤ m)
    {mu : ℝ} (hmu : 0 < mu) (hmrec : Record mu m) (hrrec : Record mu r)
    (hlarge : A ≤ (largestPrime m : ℝ)) :
    (largestPrime r : ℝ) ≤ 4 * (largestPrime m : ℝ) := by
  have hPm0 : (0 : ℝ) ≤ largestPrime m := Nat.cast_nonneg _
  by_cases hPr : A ≤ (largestPrime r : ℝ)
  · have hlo := (hmass r (by omega) mu hmu hrrec hPr).1
    have hhi := (hmass m hm mu hmu hmrec hlarge).2
    have hlog : Real.log (r : ℝ) ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < r)) (by exact_mod_cast hrm)
    linarith
  · have : (largestPrime r : ℝ) < A := lt_of_not_ge hPr
    linarith

private theorem bounded_prime_log {r : ℕ} (hr : 1 < r) {mu : ℝ}
    (hmu : 0 < mu) (hrecord : Record mu r) {B : ℝ}
    (hPrB : (largestPrime r : ℝ) ≤ B) :
    Real.log (r : ℝ) ≤ B * Real.log (4 * B ^ 2) := by
  have hPr2 : (2 : ℝ) ≤ largestPrime r := by exact_mod_cast largest_prime_two hr
  have hPr0 : (0 : ℝ) < largestPrime r := by linarith
  have hB0 : 0 < B := hPr0.trans_le hPrB
  have hsq := pow_le_pow_left₀ hPr0.le hPrB 2
  have hPrsq : (4 : ℝ) ≤ (largestPrime r : ℝ) ^ 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hPr2 2
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < 4 * (largestPrime r : ℝ) ^ 2)
    (show 4 * (largestPrime r : ℝ) ^ 2 ≤ 4 * B ^ 2 by nlinarith)
  have hnonneg : 0 ≤ Real.log (4 * (largestPrime r : ℝ) ^ 2) :=
    Real.log_nonneg (by nlinarith)
  exact (record_log_envelope (by omega : 2 ≤ r) hmu hrecord).trans
    (mul_le_mul hPrB hlog hnonneg hB0.le)

/- Elementary real-variable bookkeeping only. Its threshold is chosen once,
before m, mu and all chain nodes. The squared-log limit absorbs the ONE last
edge, not a sum over an unknown number of edges. -/
private theorem quantitative_threshold (A B c : ℝ) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℝ, T ≤ P →
      A ≤ P ∧ Real.exp 4 ≤ P ∧ 0 < Real.log (8 * P) ∧
      B * Real.log (4 * B ^ 2) < P / 2 - Real.log (8 * P) ∧
      Real.log (8 * P) + c * Real.log (4 * P) * Real.log (Real.log (4 * P)) ≤
        (8 + 4 * c) * Real.log P * Real.log (Real.log P) ∧
      (8 + 4 * c) * Real.log P * Real.log (Real.log P) < P / 2 := by
  let D := 8 + 4 * c
  have hD : 0 < D := by dsimp [D]; positivity
  have hlogratio : Tendsto (fun P : ℝ => Real.log P / P) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun P : ℝ => Real.log 8 / P) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h8ratio : Tendsto (fun P : ℝ => Real.log (8 * P) / P) atTop (𝓝 0) := by
    have hsum : Tendsto (fun P : ℝ => Real.log 8 / P + Real.log P / P)
        atTop (𝓝 0) := by simpa using hconst.add hlogratio
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with P hP
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hP.ne', add_div]
  have hfactor : Tendsto (fun P : ℝ => (1 / 2 : ℝ) - Real.log (8 * P) / P)
      atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub h8ratio
  have hdiff : Tendsto (fun P : ℝ => P / 2 - Real.log (8 * P)) atTop atTop := by
    apply (hfactor.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_id).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with P hP
    dsimp only [id]
    field_simp [hP.ne']
    <;> ring
  have hsquare : Tendsto (fun P : ℝ => D * (Real.log P ^ 2 / P)) atTop (𝓝 0) := by
    simpa using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.const_mul D)
  have hLL : Tendsto (fun P : ℝ => Real.log (Real.log P)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hall : ∀ᶠ P : ℝ in atTop,
      A ≤ P ∧ Real.exp 4 ≤ P ∧ 0 < Real.log (8 * P) ∧
      B * Real.log (4 * B ^ 2) < P / 2 - Real.log (8 * P) ∧
      Real.log (8 * P) + c * Real.log (4 * P) * Real.log (Real.log (4 * P)) ≤
        D * Real.log P * Real.log (Real.log P) ∧
      D * Real.log P * Real.log (Real.log P) < P / 2 := by
    filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (Real.exp 4),
      hLL.eventually_ge_atTop 1,
      hdiff.eventually_gt_atTop (B * Real.log (4 * B ^ 2)),
      hsquare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with P hAP hP4 hLL1 hdiffP hsquareP
    have hP0 := (Real.exp_pos 4).trans_le hP4
    have hL4 : 4 ≤ Real.log P := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 4) hP4
    have hL0 : 0 < Real.log P := by linarith
    have h4log : Real.log (4 : ℝ) ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    have h8log : Real.log (8 : ℝ) ≤ 7 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
      linarith
    have h2log : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h4id : Real.log (4 * P) = Real.log 4 + Real.log P :=
      Real.log_mul (by norm_num) hP0.ne'
    have h8id : Real.log (8 * P) = Real.log 8 + Real.log P :=
      Real.log_mul (by norm_num) hP0.ne'
    have h4lower : Real.log P ≤ Real.log (4 * P) := by
      rw [h4id]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have h4upper : Real.log (4 * P) ≤ 2 * Real.log P := by
      rw [h4id]
      linarith
    have hLL4lower : Real.log (Real.log P) ≤ Real.log (Real.log (4 * P)) :=
      Real.log_le_log hL0 h4lower
    have hLL4upper : Real.log (Real.log (4 * P)) ≤ 2 * Real.log (Real.log P) := by
      have hh := Real.log_le_log (hL0.trans_le h4lower) h4upper
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL0.ne'] at hh
      linarith
    have hprod : Real.log (4 * P) * Real.log (Real.log (4 * P)) ≤
        (2 * Real.log P) * (2 * Real.log (Real.log P)) :=
      mul_le_mul h4upper hLL4upper (by linarith) (by positivity)
    have h8upper : Real.log (8 * P) ≤ 8 * Real.log P := by
      rw [h8id]
      linarith
    have hLLsquare : Real.log P * Real.log (Real.log P) ≤ Real.log P ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hL0) hL0.le
      nlinarith
    have hsmall : D * Real.log P ^ 2 < P / 2 := by
      have hh : D * Real.log P ^ 2 / P < (1 / 2 : ℝ) := by
        simpa only [mul_div_assoc] using hsquareP
      have := (div_lt_iff₀ hP0).mp hh
      linarith
    refine ⟨hAP, hP4, ?_, hdiffP, ?_, ?_⟩
    · rw [h8id]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
    · have hweight := mul_le_mul_of_nonneg_left hprod hc.le
      have h8weight : 8 * Real.log P ≤ 8 * Real.log P * Real.log (Real.log P) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hLL1 (by positivity : 0 ≤ 8 * Real.log P)
      dsimp [D]
      nlinarith
    · have := mul_le_mul_of_nonneg_left hLLsquare hD.le
      change D * Real.log P * Real.log (Real.log P) < P / 2
      nlinarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro P hP
  exact hT P ((le_max_left _ _).trans hP)

/- Absolute C,T precede EVERY actual m, EVERY original positive mu and its
full positive-predecessor record condition. The output is the true LEAST tied
GLOBAL fixed-price optimizer, with both logarithmic budget bounds and t>mu.
This endpoint does not settle the original bank/prescribed-b/payment or RH. -/
theorem actual_record_nearby_least_global_optimizer :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective mu n < goldenResourceObjective mu m) →
      T ≤ (largestPrime m : ℝ) →
      ∃ r : ℕ, ∃ t : ℝ, 1 < r ∧ r < m ∧ mu < t ∧
        Real.log (8 * (largestPrime m : ℝ)) ≤ Real.log ((m : ℝ) / r) ∧
        Real.log ((m : ℝ) / r) ≤
          C * Real.log (largestPrime m : ℝ) * Real.log (Real.log (largestPrime m : ℝ)) ∧
        (∀ n : ℕ, 0 < n → goldenResourceObjective t n ≤ goldenResourceObjective t r) ∧
        (∀ n : ℕ, 0 < n →
          goldenResourceObjective t n = goldenResourceObjective t r → r ≤ n) := by
  obtain ⟨c, G, hc, hG, hgap⟩ := actual_min_secant_predecessor_eventual_log_gap
  obtain ⟨A, hA, hmass⟩ := uniform_mass
  let B : ℝ := max (max G (Real.exp 4)) 2
  have hB2 : 2 ≤ B := le_max_right _ _
  have hGB : G ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hBexp : Real.exp 4 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨T, hT, hquant⟩ := quantitative_threshold A B c hc
  refine ⟨8 + 4 * c, T, by positivity, hT, ?_⟩
  intro m hm mu hmu hrecord hlarge
  let P : ℝ := largestPrime m
  obtain ⟨hAP, hPexp, hcutpos, hnear, hupper, hsmall⟩ := hquant P hlarge
  have hm0 : 0 < m := by omega
  have hP0 : 0 < P := (Real.exp_pos 4).trans_le hPexp
  have hclock := (hmass m hm mu hmu hrecord hAP).1
  have hE0 : 0 ≤ B * Real.log (4 * B ^ 2) := by
    have hBsq : (4 : ℝ) ≤ B ^ 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB2 2
    have hlog : 0 ≤ Real.log (4 * B ^ 2) := Real.log_nonneg (by nlinarith)
    exact mul_nonneg (by linarith) hlog
  have hcutclock : Real.log (8 * P) < Real.log (m : ℝ) := by linarith
  obtain ⟨a, q, ha, ham, harec, hqa, hq, hqa_lt, hprev, hcross, hmut, hsupport⟩ :=
    first_crossing hm0 hrecord hcutpos hcutclock
  have hPaB : B ≤ (largestPrime a : ℝ) := by
    by_contra hn
    have hbounded := bounded_prime_log ha hmu harec (le_of_not_ge hn)
    linarith
  have hPaP : (largestPrime a : ℝ) ≤ 4 * P :=
    node_prime_bound hA hmass hm ha ham hmu hrecord harec hAP
  have hqmin := (predecessor_spec ha).2.2
  have hliteral : ∀ n : ℕ, 0 < n → n < a →
      (Real.log ((ArithmeticFunction.sigma 1 a : ℝ) / a) -
        Real.log ((ArithmeticFunction.sigma 1 q : ℝ) / q)) / Real.log ((a : ℝ) / q) ≤
      (Real.log ((ArithmeticFunction.sigma 1 a : ℝ) / a) -
        Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)) / Real.log ((a : ℝ) / n) := by
    intro n hn hna
    simpa only [hqa, secant, ell] using hqmin n hn hna
  have hedge := (hgap a (by omega) mu hmu harec q hq hqa_lt hliteral
    (hGB.trans hPaB)).2
  have hPa0 : (0 : ℝ) < largestPrime a :=
    (Real.exp_pos 4).trans_le (hBexp.trans hPaB)
  have hLa4 : 4 ≤ Real.log (largestPrime a : ℝ) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 4) (hBexp.trans hPaB)
  have hLapos : 0 < Real.log (largestPrime a : ℝ) := by linarith
  have hLLanonneg : 0 ≤ Real.log (Real.log (largestPrime a : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hLale := Real.log_le_log hPa0 hPaP
  have hLLale := Real.log_le_log hLapos hLale
  have hlog4Pnonneg : 0 ≤ Real.log (4 * P) := hLapos.le.trans hLale
  have hprod := mul_le_mul hLale hLLale hLLanonneg hlog4Pnonneg
  have hprodC := mul_le_mul_of_nonneg_left hprod hc.le
  have htotal : Real.log m - Real.log q ≤
      (8 + 4 * c) * Real.log P * Real.log (Real.log P) := by
    rw [gap_identity (by omega : 0 < a) hq] at hedge
    nlinarith
  have hq1 : 1 < q := by
    by_contra hn
    have hqone : q = 1 := by omega
    rw [hqone, Nat.cast_one, Real.log_one, sub_zero] at htotal
    linarith
  have hqm : q < m := hqa_lt.trans_le ham
  have hqrecord : Record mu q :=
    earlier_record hq hqm.le hmut hsupport.1
  have hPqP : (largestPrime q : ℝ) ≤ 4 * P :=
    node_prime_bound hA hmass hm hq1 hqm.le hmu hrecord hqrecord hAP
  let Q := primeAfter (largestPrime q)
  have hQprime := (prime_after_spec (largestPrime q)).1
  have hQbound : (Q : ℝ) ≤ 8 * P := by
    have hb : (Q : ℝ) < 2 * (largestPrime q : ℝ) := by
      exact_mod_cast prime_after_bertrand (largest_prime_two hq1)
    linarith
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQprime.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR0 : (0 : ℝ) < m := by exact_mod_cast hm0
  have hlogbudget : Real.log ((q : ℝ) * Q) ≤ Real.log m := by
    rw [Real.log_mul hq0.ne' hQ0.ne']
    have hlogQ := Real.log_le_log hQ0 hQbound
    linarith
  have hbudget : q * Q ≤ m := by
    have hh := (Real.log_le_log_iff (mul_pos hq0 hQ0) hmR0).mp hlogbudget
    exact_mod_cast hh
  have hglobal := budget_to_least_global hq hqm.le (hmu.trans hmut) hsupport hbudget
  refine ⟨q, critical a, hq1, hqm, hmut, ?_, ?_, hglobal.1, hglobal.2⟩
  · rw [gap_identity hm0 hq]
    exact hcross
  · rw [gap_identity hm0 hq]
    exact htotal

end D5.S3.Arith.Robin.PriceRecord.ActualCriticalChainNearbyGlobal

