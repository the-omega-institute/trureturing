/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordElementaryPrimeTails
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordElementaryPrimeTails
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: One eventual extra layer uniformly over all primes of original records. -/
/- proof_shape: content
admission_basis: escape-witness
escape_witness: eventual_exchange_window and finite_odd_prime_floor construct
one eventual two-prime exchange window before any varying prime is chosen,
and obtain a uniform lower marginal bound for every odd prime of valuation
at least two. odd_count_bound converts it to the strict own-clock count bound.
The existing binary endpoint supplies p=2. The consumed private adapter
golden_layer_strict_p_contraction is bind-only, used by odd_count_bound;
its adjacent-layer separation is reused from the public canonical library.
utility: none. This is unbounded asymptotic analysis with arbitrary original
positive record prices and all natural prime indices, not a bounded instance,
enumeration, checker or numerical reduction. Higher-layer critical residuals
and the original-record RH lower-bound criterion are existing library results,
not new claims here. The full prescribed bank, Robin beyond 5040 and RH are
not established by this theorem.

The weighted boundary, window fee and window logarithmic mass estimates
are reused at their public declarations in ActualRecordElementarySingleTwoTail. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail
import D5.S3.Arith.Robin.PriceRecord.ActualRecordCriticalResidual
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform single extra layer over all original records and all primes.
The original positive record price is arbitrary. The comparison uses the
integer's own-clock price, without an infinite-record-tail assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (beta beta_nat beta_pos)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_above_layer_prime signed_exchange_certificate)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
  (FullRecord logMass largestPrime_prime)
open D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap (ownPrice)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
  (record_ratio_limit coarse_scale_limits shrinking_prime_windows)

-- Bind-only consumed adapter of the existing PUBLIC adjacent separation.
-- No new contraction proof is needed or retained.
private theorem golden_layer_strict_p_contraction {p j : ℕ}
    (hp : p.Prime) (hj : 1 ≤ j) :
    (p : ℝ) * goldenLayerMarginal p (j + 1) < goldenLayerMarginal p j := by
  rw [← beta_nat hp (by omega : 1 ≤ j + 1), ← beta_nat hp hj]
  simpa only [Nat.add_sub_cancel] using
    (ActualHigherLayerQuantitativeBudgetRepair.adjacent_layer_strict
      (j := j + 1) (by omega) (u := (p : ℝ)) (by exact_mod_cast hp.two_le))

/-- Uniform analytic interface. It depends on the original record pair only,
so its eventual quantifier precedes EVERY subsequently chosen prime p. -/
private theorem eventual_exchange_window {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ t, 2 ≤ m t)
    (hmu : ∀ t, 0 < mu t) (hrecord : ∀ t, FullRecord (m t) (mu t))
    (hP : Tendsto (fun t => (largestPrime (m t) : ℝ)) l atTop) :
    ∀ᶠ t in l, ∃ U : Finset ℕ, ∃ E : ℝ,
      U.card = 2 ∧
      layerPrime (m t) 2 < largestPrime (m t) ∧
      (m t).factorization (largestPrime (m t)) = 1 ∧
      (∀ q ∈ U, q.Prime ∧ layerPrime (m t) 2 < q ∧
        q < largestPrime (m t) ∧ (m t).factorization q = 1) ∧
      (∀ q ∈ U,
        |(goldenLayerMarginal q ((m t).factorization q + 1) -
          beta 1 (largestPrime (m t) : ℝ)) * log (q : ℝ)| ≤
          beta 1 (largestPrime (m t) : ℝ) * E) ∧
      3 * log (2 : ℝ) / 4 + 2 * E <
        logMass U - log (largestPrime (m t) : ℝ) ∧
      logMass U - log (largestPrime (m t) : ℝ) < log (3 : ℝ) := by
  classical
  let P : α → ℝ := fun t => largestPrime (m t)
  let Q : α → ℝ := fun t => layerPrime (m t) 2
  let X : α → ℝ := fun t => log (P t)
  let H : α → ℝ := fun t => log (Q t)
  let r : α → ℝ := fun t => Q t ^ 2 / (2 * P t)
  let E : α → ℝ := fun t => |X t * (beta 2 (Q t) / beta 1 (P t) - 1)| +
    512 * (X t / H t ^ 3)
  have hb : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hb3 : log (2 : ℝ) < log (3 : ℝ) :=
    log_lt_log (by norm_num) (by norm_num)
  have hratio := record_ratio_limit m mu hm hmu hrecord 2 (by omega) hP
  obtain ⟨hQ, hHX, hsep⟩ := coarse_scale_limits P Q 2 (by omega)
    (fun t => Nat.cast_nonneg _) hP hratio
  have hX : Tendsto X l atTop := tendsto_log_atTop.comp hP
  have hH : Tendsto H l atTop := tendsto_log_atTop.comp hQ
  have hXH : Tendsto (fun t => X t / H t) l (𝓝 2) := by
    simpa using hHX.inv₀ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
  have hd : Tendsto (fun t => 1 / H t ^ 3) l (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hH).const_div_atTop 1
  have hXd : Tendsto (fun t => X t / H t ^ 3) l (𝓝 0) := by
    have hh := hXH.mul
      (((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hH).const_div_atTop 1)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hH.eventually_gt_atTop 0] with t ht
    dsimp only [Function.comp_def]
    field_simp [ht.ne'] <;> ring
  have hr : Tendsto r l (𝓝 1) := by
    have hh := hratio.div_const 2
    norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
    convert hh using 1
    funext t
    dsimp [r]
    ring
  have hlogr : Tendsto (fun t => log (r t)) l (𝓝 0) := by
    simpa using hr.log (by norm_num : (1 : ℝ) ≠ 0)
  -- Reuse the original weighted_boundary_limit helper.
  have hweighted := ActualRecordElementarySingleTwoTail.weighted_boundary_limit
    m mu hm hmu hrecord hP
  have hE : Tendsto E l (𝓝 0) := by
    simpa only [abs_zero, mul_zero, add_zero] using
      hweighted.abs.add (hXd.const_mul 512)
  -- These bounds do not select U, and do not quantify over an external prime.
  have hlo : Tendsto (fun t => log 2 + log (r t) - 2 * E t) l (𝓝 (log 2)) := by
    simpa only [add_zero, mul_zero, sub_zero] using
      ((tendsto_const_nhds (x := log (2 : ℝ))).add hlogr).sub (hE.const_mul 2)
  have hhi : Tendsto (fun t => log 2 + log (r t) + 2 / H t ^ 3)
      l (𝓝 (log 2)) := by
    have hh := ((tendsto_const_nhds (x := log (2 : ℝ))).add hlogr).add
      (hd.const_mul 2)
    simp only [add_zero, mul_zero] at hh
    convert hh using 1
    funext t
    ring
  have huppersep : Tendsto (fun t => (Q t * (1 + 1 / H t ^ 3)) / P t)
      l (𝓝 0) := by
    have hh := hsep.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hd)
    simp only [zero_mul] at hh
    convert hh using 1
    funext t
    ring
  have hhalflog : Tendsto (fun t => (H t - log 2) / X t)
      l (𝓝 (1 / 2 : ℝ)) := by
    have hh := hHX.sub (hX.const_div_atTop (log 2))
    norm_num only [Nat.cast_ofNat, sub_zero, inv_eq_one_div] at hh
    convert hh using 1
    funext t
    ring
  obtain ⟨Tw, _hTw, hwindows⟩ := shrinking_prime_windows 1 zero_lt_one
  -- One eventual event, formed before U and before any varying prime p.
  filter_upwards [hP.eventually_gt_atTop 4, hQ.eventually_ge_atTop (max Tw 4),
    hH.eventually_ge_atTop 2,
    hratio.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2)),
    huppersep.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hhalflog.eventually (eventually_gt_nhds (by norm_num : (1 / 8 : ℝ) < 1 / 2)),
    hlo.eventually (eventually_gt_nhds
      (show 3 * log (2 : ℝ) / 4 < log 2 by linarith only [hb])),
    hhi.eventually_lt_const hb3]
    with t hp hq hH2 hratio1 hupper hhalf hlo' hhi'
  have hP0 : 0 < P t := by linarith
  have hQ4 : 4 ≤ Q t := (le_max_right Tw 4).trans hq
  have hQ0 : 0 < Q t := by linarith
  have hXp : 0 < X t := log_pos (by linarith)
  have hHp : 0 < H t := by linarith
  have hdelta : 0 ≤ 1 / H t ^ 3 := by positivity
  have hupper' : Q t * (1 + 1 / H t ^ 3) < P t := (div_lt_one hP0).mp hupper
  have hQP : Q t < P t := by
    nlinarith only [hupper', mul_nonneg hQ0.le hdelta]
  have hPQ2 : P t ≤ Q t ^ 2 := by
    have hh := (one_lt_div hP0).mp hratio1
    linarith
  have hloghalf : X t / 8 ≤ log (Q t / 2) := by
    rw [log_div hQ0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hh := (lt_div_iff₀ hXp).mp hhalf
    change X t / 8 ≤ H t - log 2
    linarith
  have hcapacity : 2 ≤ ⌈(1 : ℝ) * log (Q t) ^ 3⌉₊ := by
    have hpow : (2 : ℝ) ≤ H t ^ 3 := by nlinarith [sq_nonneg (H t - 2)]
    have hh := hpow.trans (Nat.le_ceil (H t ^ 3))
    exact_mod_cast (by simpa only [one_mul] using hh :
      (2 : ℝ) ≤ (⌈(1 : ℝ) * log (Q t) ^ 3⌉₊ : ℝ))
  obtain ⟨_Lo, U, _hLo, hUcard, _hLow, hU⟩ :=
    hwindows (Q t) ((le_max_left Tw 4).trans hq) 2 hcapacity
  have hbelow (q : ℕ) (hu : q ∈ U) : (q : ℝ) < P t :=
    (hU q hu).2.2.trans_lt hupper'
  -- Actual valuation 1 uses the original record's support as well as the cutoff.
  have hval (q : ℕ) (hprime : q.Prime) (hbelowP : (q : ℝ) ≤ P t)
      (haboveQ : Q t < (q : ℝ)) : (m t).factorization q = 1 := by
    have hm0 : m t ≠ 0 := by have := hm t; omega
    have hsupport := (price_record_prime_structure (hm t) (hmu t) (hrecord t)).2
    have hmem : q ∈ (m t).primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr
        ⟨by dsimp only [P] at hbelowP; exact_mod_cast hbelowP, hprime⟩
    have hvlo := (hprime.dvd_iff_one_le_factorization hm0).mp
      (Nat.dvd_of_mem_primeFactors hmem)
    have hvhi := valuation_above_layer_prime
      (by have := hm t; omega : 0 < m t) (by omega : 1 ≤ (2 : ℕ)) hprime
      (by dsimp only [Q] at haboveQ; exact_mod_cast haboveQ)
    omega
  have hPprime := largestPrime_prime (hm t)
  have hPval : (m t).factorization (largestPrime (m t)) = 1 :=
    hval _ hPprime le_rfl hQP
  have hUval (q : ℕ) (hu : q ∈ U) : (m t).factorization q = 1 :=
    hval q (hU q hu).1 (hbelow q hu).le (hU q hu).2.1
  -- Reuse the original window_log_mass helper.
  have hlogs := ActualRecordElementarySingleTwoTail.window_log_mass
    (by linarith : 1 < Q t) hUcard (fun q hu => (hU q hu).2)
  have hlogsLo : 2 * H t < logMass U := hlogs.1
  have hlogsHi : logMass U ≤ 2 * H t + 2 / H t ^ 3 := hlogs.2
  have hrlog : log (r t) = 2 * H t - log 2 - X t := by
    dsimp [r, H, X]
    rw [log_div (pow_ne_zero 2 hQ0.ne') (mul_ne_zero (by norm_num) hP0.ne'),
      log_pow, log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne']
    norm_num only [Nat.cast_ofNat]
    ring
  refine ⟨U, E t, hUcard, ?_, hPval, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q, P] at hQP
    exact_mod_cast hQP
  · intro q hu
    refine ⟨(hU q hu).1, ?_, ?_, hUval q hu⟩
    · have hh := (hU q hu).2.1
      dsimp only [Q] at hh
      exact_mod_cast hh
    · have hh := hbelow q hu
      dsimp only [P] at hh
      exact_mod_cast hh
  · intro q hu
    rw [hUval q hu]
    norm_num only [Nat.reduceAdd]
    rw [← beta_nat (hU q hu).1 (by omega : 1 ≤ (2 : ℕ))]
    -- Reuse the original window_fee helper.
    simpa only [E, X, H] using
      (ActualRecordElementarySingleTwoTail.window_fee (by linarith : 2 ≤ P t)
        hQ4 hPQ2 hloghalf (hU q hu).2.1 (hU q hu).2.2 (hbelow q hu).le)
  · change 3 * log (2 : ℝ) / 4 + 2 * E t < logMass U - X t
    linarith only [hlo', hlogsLo, hrlog]
  · change logMass U - X t < log (3 : ℝ)
    linarith only [hhi', hlogsHi, hrlog]

-- The signed certificate is applied at ORIGINAL mu; lam has no record premise.
private theorem finite_odd_prime_floor {m p : ℕ} (hm : 2 ≤ m)
    {mu : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hv : 2 ≤ m.factorization p)
    {U : Finset ℕ} {E : ℝ} (hcard : U.card = 2)
    (hQP : layerPrime m 2 < largestPrime m)
    (hPval : m.factorization (largestPrime m) = 1)
    (hU : ∀ q ∈ U, q.Prime ∧ layerPrime m 2 < q ∧
      q < largestPrime m ∧ m.factorization q = 1)
    (hfee : ∀ q ∈ U,
      |(goldenLayerMarginal q (m.factorization q + 1) -
        beta 1 (largestPrime m : ℝ)) * log (q : ℝ)| ≤
        beta 1 (largestPrime m : ℝ) * E)
    (hthetaLo : 3 * log (2 : ℝ) / 4 + 2 * E <
      logMass U - log (largestPrime m : ℝ))
    (hthetaHi : logMass U - log (largestPrime m : ℝ) < log (3 : ℝ)) :
    3 * beta 1 (largestPrime m : ℝ) * log (2 : ℝ) / 4 <
      goldenLayerMarginal p (m.factorization p) * log (p : ℝ) := by
  classical
  let P : ℕ := largestPrime m
  let lam : ℝ := beta 1 (P : ℝ)
  let D : Finset ℕ := {p, P}
  have hPprime : P.Prime := largestPrime_prime hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hPprime.pos
  have hlam : 0 < lam := beta_pos (by exact_mod_cast hPprime.two_le) (by omega)
  have hpQ : p ≤ layerPrime m 2 := by
    by_contra! hbad
    have hh := valuation_above_layer_prime (by omega : 0 < m)
      (by omega : 1 ≤ (2 : ℕ)) hp hbad
    omega
  have hpP : p ≠ P := ne_of_lt (hpQ.trans_lt hQP)
  have hpdvd : p ∣ m := (hp.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr
    (by omega)
  have hPd : P ∣ m := (hPprime.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr
    (by
      change 1 ≤ m.factorization (largestPrime m)
      exact le_of_eq hPval.symm)
  have hD : ∀ r ∈ D, r.Prime := by
    intro r hr
    simp only [D, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hPprime
  have hDvd : ∀ r ∈ D, r ∣ m := by
    intro r hr
    simp only [D, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hpdvd
    · exact hPd
  have hDU : Disjoint D U := by
    apply disjoint_left.mpr
    intro r hr hu
    have hg := hU r hu
    simp only [D, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact (not_lt_of_ge hpQ) hg.2.1
    · exact (lt_irrefl P) hg.2.2.1
  have hd : (∏ r ∈ D, r) = p * P := by simp [D, hpP]
  have hdlog : log ((∏ r ∈ D, r : ℕ) : ℝ) = log (p : ℝ) + log (P : ℝ) := by
    rw [hd, Nat.cast_mul, log_mul hp0.ne' hP0.ne']
  have hulog : log ((∏ q ∈ U, q : ℕ) : ℝ) = logMass U := by
    simpa only [Nat.cast_prod, logMass] using
      (Real.log_prod (s := U) (f := fun q : ℕ => (q : ℝ))
        (fun q hq => by exact_mod_cast (hU q hq).1.ne_zero))
  have hlogp : log (3 : ℝ) ≤ log (p : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hp3)
  have heta : 0 < log (p : ℝ) + log (P : ℝ) - logMass U := by
    change logMass U - log (P : ℝ) < log (3 : ℝ) at hthetaHi
    linarith only [hthetaHi, hlogp]
  have hprod : (∏ q ∈ U, q) < ∏ r ∈ D, r := by
    have hu0 : (0 : ℝ) < ((∏ q ∈ U, q : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun q hq => (hU q hq).1.pos)
    have hd0 : (0 : ℝ) < ((∏ r ∈ D, r : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun r hr => (hD r hr).pos)
    have hh : log ((∏ q ∈ U, q : ℕ) : ℝ) <
        log ((∏ r ∈ D, r : ℕ) : ℝ) := by
      rw [hulog, hdlog]
      linarith only [heta]
    exact_mod_cast (log_lt_log_iff hu0 hd0).mp hh
  have hcert := signed_exchange_certificate mu (by omega : 0 < m)
    hrecord D U hD (fun q hq => (hU q hq).1) hDvd hDU hprod
  have hcomparison := hcert.2.2
  have hPbeta : goldenLayerMarginal P 1 = lam := (beta_nat hPprime (by omega)).symm
  have hDsum : (∑ r ∈ D, goldenLayerMarginal r (m.factorization r) * log (r : ℝ)) =
      goldenLayerMarginal p (m.factorization p) * log (p : ℝ) + lam * log (P : ℝ) := by
    simp [D, hpP, show m.factorization P = 1 from hPval, hPbeta]
  rw [hDsum, hdlog, hulog] at hcomparison
  have hsum : lam * logMass U - 2 * lam * E ≤
      ∑ q ∈ U, goldenLayerMarginal q (m.factorization q + 1) * log (q : ℝ) := by
    calc
      _ = ∑ q ∈ U, (lam * log (q : ℝ) - lam * E) := by
        simp [sum_sub_distrib, ← mul_sum, logMass, hcard] <;> ring
      _ ≤ _ := by
        apply sum_le_sum
        intro q hq
        have hh := (abs_le.mp (hfee q hq)).1
        change -(lam * E) ≤
          (goldenLayerMarginal q (m.factorization q + 1) - lam) * log (q : ℝ) at hh
        linarith only [hh]
  have hmueta := mul_pos hmu heta
  change 3 * log (2 : ℝ) / 4 + 2 * E < logMass U - log (P : ℝ) at hthetaLo
  have hlow := mul_lt_mul_of_pos_left hthetaLo hlam
  change 3 * lam * log (2 : ℝ) / 4 < _
  linarith only [hcomparison, hsum, hmueta, hlow]

private theorem odd_count_bound {m p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {lam : ℝ} (hlam : 0 < lam) (hc : 0 < ownPrice m)
    (hcprice : ownPrice m ≤ 5 * lam / 4)
    (hfloor : 3 * lam * log (2 : ℝ) / 4 <
      goldenLayerMarginal p (m.factorization p) * log (p : ℝ)) :
    m.factorization p ≤ optimalLayerCount (ownPrice m) p + 1 := by
  let a := optimalLayerCount (ownPrice m) p
  obtain ⟨n, hn, hcounts, hopt, _hleast⟩ := optimal_layer_count_spec hc
  have hnext : goldenLayerMarginal p (a + 1) ≤ ownPrice m := by
    have hh := ((golden_resource_optimal_iff_layer_thresholds hc hn).mp hopt).1 p hp
    simpa only [hcounts p, a] using hh
  by_contra hbad
  have hv : a + 2 ≤ m.factorization p := by change ¬ m.factorization p ≤ a + 1 at hbad; omega
  have hmono : goldenLayerMarginal p (m.factorization p) ≤
      goldenLayerMarginal p (a + 2) := by
    rcases eq_or_lt_of_le hv with heq | hlt
    · rw [heq]
    · exact (golden_layer_strict_decrease hp (by omega) hlt).le
  have hcontract := golden_layer_strict_p_contraction hp (j := a + 1) (by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hscaled : (p : ℝ) * goldenLayerMarginal p (m.factorization p) < ownPrice m :=
    (mul_le_mul_of_nonneg_left hmono hp0.le).trans_lt (hcontract.trans_le hnext)
  have hvupper : goldenLayerMarginal p (m.factorization p) < ownPrice m / (p : ℝ) :=
    (lt_div_iff₀ hp0).mpr (by simpa only [mul_comm] using hscaled)
  have hp3real : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hratio : log (p : ℝ) / p ≤ log (3 : ℝ) / 3 :=
    Real.log_div_self_antitoneOn
      Real.exp_one_lt_three.le (Real.exp_one_lt_three.le.trans hp3real) hp3real
  have hu : goldenLayerMarginal p (m.factorization p) * log (p : ℝ) <
      (5 * lam / 12) * log (3 : ℝ) := by
    calc
      _ < (ownPrice m / (p : ℝ)) * log (p : ℝ) :=
        mul_lt_mul_of_pos_right hvupper hp.log_pos
      _ ≤ ((5 * lam / 4) / (p : ℝ)) * log (p : ℝ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcprice hp0.le) hp.log_pos.le
      _ = (5 * lam / 4) * (log (p : ℝ) / p) := by ring
      _ ≤ (5 * lam / 4) * (log (3 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hgap : 5 * log (3 : ℝ) < 9 * log (2 : ℝ) := by
    have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < (3 : ℝ) ^ 5)
      (by norm_num : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 9)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hgapScaled := mul_lt_mul_of_pos_left hgap hlam
  nlinarith only [hu, hfloor, hgapScaled]

private theorem uniform_odd_prime_threshold :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      ∀ p : ℕ, p.Prime → 3 ≤ p →
        m.factorization p ≤ optimalLayerCount (ownPrice m) p + 1 := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun t => t.1.1
  let mu : S → ℝ := fun t => t.1.2
  let P : S → ℝ := fun t => largestPrime (m t)
  let l : Filter S := comap P atTop
  have hw := eventual_exchange_window (l := l) m mu (fun t => t.2.1)
    (fun t => t.2.2.1) (fun t => t.2.2.2) (show Tendsto P l atTop from tendsto_comap)
  obtain ⟨Tw, hTw⟩ := eventually_atTop.mp (eventually_comap.mp hw)
  obtain ⟨Tc, hTc, hclock⟩ := ActualRecordSingleTwoTail.uniform_price_and_error 0
  refine ⟨max Tw Tc, hTc.trans_le (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrecord hlarge p hp hp3
  by_cases hv : n.factorization p ≤ 1
  · omega
  have hv2 : 2 ≤ n.factorization p := by omega
  let t : S := ⟨(n, nu), hn, hnu, hrecord⟩
  obtain ⟨U, E, hcard, hQP, hPval, hU, hfee, hlo, hhi⟩ :=
    hTw (largestPrime n : ℝ) ((le_max_left Tw Tc).trans hlarge) t rfl
  obtain ⟨hP2, hc, hcprice, _herror⟩ :=
    hclock n hn nu hnu hrecord ((le_max_right Tw Tc).trans hlarge)
  change 0 < ownPrice n at hc
  change ownPrice n ≤ 5 * beta 1 (largestPrime n : ℝ) / 4 at hcprice
  have hfloor := finite_odd_prime_floor hn hnu hrecord hp hp3 hv2 hcard hQP hPval hU hfee hlo hhi
  exact odd_count_bound hp hp3 (beta_pos hP2 (by omega)) hc hcprice hfloor

/-- Uniform single extra layer at the integer's own-clock price.
The natural threshold is chosen before m, original mu, and the varying prime p.
An empty eventual original record tail is allowed. -/
theorem eventual_actual_record_single_prime_tail :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      ∀ p : ℕ, p.Prime →
        m.factorization p ≤ optimalLayerCount (ownPrice m) p + 1 := by
  obtain ⟨T, _hT, hodd⟩ := uniform_odd_prime_threshold
  obtain ⟨M2, htwo⟩ := ActualRecordElementarySingleTwoTail.eventual_actual_record_single_two_tail
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun t => t.1.1
  let mu : S → ℝ := fun t => t.1.2
  let l : Filter S := comap m atTop
  have hnat : Tendsto m l atTop := tendsto_comap
  have hreal : Tendsto (fun t => (m t : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hX : Tendsto (fun t => log (m t : ℝ)) l atTop := tendsto_log_atTop.comp hreal
  -- This PUBLIC API uses the original record_log_envelope. It is defined
  -- in ActualRecordCriticalResidual.lean in the namespace written below.
  have hP := ActualRecordHigherLayerResidual.record_prime_escape m mu
    (fun t => t.2.1) (fun t => t.2.2.1) (fun t => t.2.2.2) hX
  have hall : ∀ᶠ t in l, ∀ p : ℕ, p.Prime → 3 ≤ p →
      (m t).factorization p ≤ optimalLayerCount (ownPrice (m t)) p + 1 := by
    filter_upwards [hP.eventually_ge_atTop T] with t ht
    exact hodd (m t) t.2.1 (mu t) t.2.2.1 t.2.2.2 ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max 2 (max N M2), ?_⟩
  intro n hn nu hnu hrecord p hp
  have hn2 : 2 ≤ n := by omega
  by_cases hp2 : p = 2
  · subst p
    exact htwo n (by omega) nu hnu hrecord
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    let t : S := ⟨(n, nu), hn2, hnu, hrecord⟩
    exact hN n (by omega) t rfl p hp hp3


end D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails
