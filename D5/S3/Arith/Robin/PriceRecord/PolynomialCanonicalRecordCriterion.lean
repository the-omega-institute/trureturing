/- GID: D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial canonical-record samples characterize the actual closed zero strip. -/

import D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
import D5.S3.Arith.Robin.ActualTwoPriceDefect
import D5.S3.Arith.Robin.ActualRobinInterval
import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry
import D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
import D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion
import D5.S3.Weil.Mertens.ZeroAbscissaPower
import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction
import Mathlib.Tactic
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
import D5.S3.Weil.Convention
import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import D5.S3.Weil.Mertens.CriticalThetaTailPeak
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Full-layer sampling on integer meshes and the closed strip of actual zeta zeros. -/
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
open Filter Set Finset MeasureTheory
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D B)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open ActualBalancedCutoff (firstLayerPrice)
open ActualBoundaryPriceLocalization (FullRecord)
open RHSharpOriginalRecordMargin (Pn)
open PolynomialMeshBounds
open Asymptotics
open OriginalRecordLowerBoundCriterion (D_pos fixed_negative_ratio)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zero_real_parts_nonempty)

private def mu (N : ℕ) : ℝ := firstLayerPrice ((N : ℝ) + 1)

private def specified (N : ℕ) : ℕ := strictInteger (mu N)
-- Local proof notation only; no new public pressure-potential alias.

private def S (X : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log X) - 1 / Real.log X -
    pressure (price X)

private def W (alpha X : ℝ) : ℝ := Real.rpow X alpha * Real.log X

private lemma W_pos (alpha : ℝ) {X : ℝ} (hX : 1 < X) : 0 < W alpha X :=
  PolynomialMeshBounds.W_pos alpha hX

private lemma strict_record {q : ℝ} (hq : 0 < q) : FullRecord (strictInteger q) q := by
  obtain ⟨hm, _, hopt, hleast⟩ := strictInteger_spec hq
  intro n hn hnm
  have hle := hopt n (by omega)
  by_contra! hnot
  have heq := le_antisymm hle hnot
  have hnopt : IsGoldenResourceOptimal q n := by
    intro j hj
    rw [heq]
    exact hopt j hj
  exact (Nat.le_of_dvd hn (hleast n (by omega) hnopt)).not_gt hnm

private lemma support_of_active {q : ℝ} (hq : 0 < q) (N : ℕ)
    (hactive : ∀ p : ℕ, p.Prime → (q < goldenLayerMarginal p 1 ↔ p ≤ N)) :
    (strictInteger q).primeFactors = Nat.primesLE N := by
  have hm0 : strictInteger q ≠ 0 := by have := strictInteger_pos hq; omega
  ext p
  constructor
  · intro hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(hactive p hprime).mp
      ((strict_layer_iff hq hprime (by norm_num : 1 ≤ (1 : ℕ))).mp
        ((hprime.dvd_iff_one_le_factorization hm0).mp hdvd)), hprime⟩
  · intro hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime,
      (hprime.dvd_iff_one_le_factorization hm0).mpr
        ((strict_layer_iff hq hprime (by norm_num : 1 ≤ (1 : ℕ))).mpr
          ((hactive p hprime).mpr hpN)), hm0⟩

private lemma size_of_support {q : ℝ} (hq : 0 < q) {N : ℕ} (hN : 3 ≤ N)
    (hs : (strictInteger q).primeFactors = Nat.primesLE N) :
    3 ≤ strictInteger q := by
  have h3 : 3 ∈ (strictInteger q).primeFactors := by
    rw [hs]
    exact Nat.mem_primesLE.mpr ⟨hN, Nat.prime_three⟩
  exact Nat.le_of_dvd (by have := strictInteger_pos hq; omega)
    (Nat.dvd_of_mem_primeFactors h3)

private lemma largest_of_support {m N : ℕ}
    (hs : m.primeFactors = Nat.primesLE N) : largestPrime m = Pn (N : ℝ) := by
  simp only [largestPrime, Pn, Nat.floor_natCast, hs]

private lemma mu_pos {N : ℕ} (hN : 2 ≤ N) : 0 < mu N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold mu firstLayerPrice
  apply div_pos
  · apply Real.log_pos
    have := one_div_pos.mpr (show 0 < (N : ℝ) + 1 by linarith)
    linarith
  · exact Real.log_pos (by linarith)

private lemma specified_data {N : ℕ} (hN : 3 ≤ N) :
    0 < mu N ∧ 3 ≤ specified N ∧ FullRecord (specified N) (mu N) ∧
      (specified N).primeFactors = Nat.primesLE N ∧
      largestPrime (specified N) = Pn (N : ℝ) := by
  have hq := mu_pos (show 2 ≤ N by omega)
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hactive (p : ℕ) (hp : p.Prime) :
      mu N < goldenLayerMarginal p 1 ↔ p ≤ N := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    change firstLayerPrice ((N : ℝ) + 1) < firstLayerPrice (p : ℝ) ↔ p ≤ N
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    constructor
    · intro h
      by_contra hnot
      have hle : (N : ℝ) + 1 ≤ p := by exact_mod_cast (show N + 1 ≤ p by omega)
      exact (not_lt_of_ge (ActualBalancedCutoff.firstLayerPrice_strictAnti.antitoneOn
        (by linarith : 1 < (N : ℝ) + 1) hp1 hle)) h
    · intro h
      apply ActualBalancedCutoff.firstLayerPrice_strictAnti hp1 (by linarith : 1 < (N : ℝ) + 1)
      have : (p : ℝ) ≤ N := by exact_mod_cast h
      linarith
  have hs := support_of_active hq N hactive
  exact ⟨hq, size_of_support hq hN hs, strict_record hq, hs, largest_of_support hs⟩

private lemma exact_pressure_ge_margin {X : ℝ} (hX : 1 < X) {n : ℕ}
    (hn : 1 ≤ n) (hlog : 1 < Real.log (n : ℝ))
    (hopt : IsGoldenResourceOptimal (price X) n) : robinLogMargin n ≤ S X := by
  have htangent : Real.log (Real.log (Real.log (n : ℝ))) - Real.log (Real.log X) ≤
      (Real.log (n : ℝ) - X) * price X := by
    by_cases heq : X = Real.log (n : ℝ)
    · rw [heq]; simp
    · simpa only [ActualRobinClockCovariance.g, price] using
        (RestrictedDivisorStrictInventory.loglog_tangent hX hlog heq).le
  have hpX : price X * X = 1 / Real.log X := by
    unfold price
    field_simp [ne_of_gt (show 0 < X by linarith), (Real.log_pos hX).ne'] <;> ring
  rw [S, pressure_eq_of_optimal hn hopt, golden_resource_sigma_identity _ hn]
  unfold robinLogMargin
  nlinarith only [htangent, hpX]

private lemma exists_price_eq_first_layer_price {t : ℝ} (ht : 12 < t) :
    ∃ x : ℝ, t < x ∧ x < t + 1 / 2 ∧ price x = firstLayerPrice t := by
  have ht1 : 1 < t := by linarith only [ht]
  obtain ⟨u, hu, htu, _, hpu, _⟩ := ActualBalancedCutoff.half_shift_cutoff ht
  obtain ⟨v, hv, _, hshift, hpv, _⟩ := ActualBalancedCutoff.half_shift_cutoff
    (show 12 < t + 1 / 2 by linarith only [ht])
  have hleft : firstLayerPrice t < price t := by
    rw [← hpu]
    exact ActualBalancedCutoff.firstLayerPrice_strictAnti
      (show 1 < u by linarith only [hu]) ht1 (sub_pos.mp htu)
  have hright : price (t + 1 / 2) < firstLayerPrice t := by
    rw [← hpv]
    exact ActualBalancedCutoff.firstLayerPrice_strictAnti ht1
      (show 1 < v by linarith only [hv]) (show t < v by linarith only [hshift])
  have hcont : ContinuousOn price (Set.Icc t (t + 1 / 2)) := by
    have ht0 : 0 < t := by linarith only [ht1]
    have hlog : ContinuousOn Real.log (Set.Icc t (t + 1 / 2)) :=
      continuousOn_id.log (fun y hy => (ht0.trans_le hy.1).ne')
    unfold price
    apply continuousOn_const.div (continuousOn_id.mul hlog)
    intro y hy
    exact mul_ne_zero (ht0.trans_le hy.1).ne' (Real.log_pos (ht1.trans_le hy.1)).ne'
  have hclosed : firstLayerPrice t ∈ Set.Icc (price (t + 1 / 2)) (price t) :=
    ⟨hright.le, hleft.le⟩
  obtain ⟨x, hx, hprice⟩ := intermediate_value_Icc'
    (show t ≤ t + 1 / 2 by linarith) hcont hclosed
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_, hprice⟩
  · intro heq
    exact (ne_of_lt hleft) (hprice.symm.trans (congrArg price heq.symm))
  · intro heq
    exact (ne_of_lt hright) ((congrArg price heq).symm.trans hprice)

private lemma exists_canonical_price_cutoff {N : ℕ} (hN : 12 ≤ N) :
    ∃ x : ℝ, (N : ℝ) + 1 < x ∧ x < (N : ℝ) + 1 + 1 / 2 ∧ price x = mu N := by
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  simpa only [mu] using exists_price_eq_first_layer_price (t := (N : ℝ) + 1)
    (by linarith only [hNr])

/-- The exact-price sample for `N ≥ 12`, extended by the natural cast at small indices. -/
private def canonicalPriceCutoff (N : ℕ) : ℝ :=
  if hN : 12 ≤ N then Classical.choose (exists_canonical_price_cutoff hN) else (N : ℝ)

private lemma canonical_price_cutoff_spec {N : ℕ} (hN : 12 ≤ N) :
    (N : ℝ) + 1 < canonicalPriceCutoff N ∧
      canonicalPriceCutoff N < (N : ℝ) + 1 + 1 / 2 ∧ price (canonicalPriceCutoff N) = mu N := by
  simpa only [canonicalPriceCutoff, dif_pos hN] using
    Classical.choose_spec (exists_canonical_price_cutoff hN)

private lemma le_canonical_price_cutoff (N : ℕ) : (N : ℝ) ≤ canonicalPriceCutoff N := by
  by_cases hN : 12 ≤ N
  · have hleft := (canonical_price_cutoff_spec hN).1
    linarith only [hleft]
  · simp only [canonicalPriceCutoff, dif_neg hN, le_refl]

private lemma canonical_price_cutoff_strictMono : StrictMono canonicalPriceCutoff := by
  intro i j hij
  by_cases hi : 12 ≤ i
  · have hj : 12 ≤ j := by omega
    have hijR : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    have hleft := (canonical_price_cutoff_spec hj).1
    have hright := (canonical_price_cutoff_spec hi).2.1
    linarith only [hijR, hleft, hright]
  · have hi' : canonicalPriceCutoff i = (i : ℝ) := by
      simp only [canonicalPriceCutoff, dif_neg hi]
    rw [hi']
    exact (show (i : ℝ) < j by exact_mod_cast hij).trans_le (le_canonical_price_cutoff j)

private lemma canonical_price_cutoff_gap {N : ℕ → ℕ} (hN : StrictMono N)
    {G eta : ℝ} (hG : 0 ≤ G)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * Real.rpow (N k : ℝ) (1 - eta)) :
    ∀ᶠ k : ℕ in atTop, canonicalPriceCutoff (N (k + 1)) - canonicalPriceCutoff (N k) ≤
      (G + 1 / 2) * Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) := by
  filter_upwards [hgap, hN.tendsto_atTop.eventually (eventually_ge_atTop (12 : ℕ))]
    with k hkGap hk
  have hnext : 12 ≤ N (k + 1) := hk.trans (hN.monotone (Nat.le_succ k))
  have hleft := (canonical_price_cutoff_spec hk).1
  have hright := (canonical_price_cutoff_spec hnext).2.1
  have hN12 : (12 : ℝ) ≤ N k := by exact_mod_cast hk
  have hbase : 1 ≤ (N k : ℝ) := by linarith only [hN12]
  have hle := le_canonical_price_cutoff (N k)
  have hexp : 0 ≤ 1 - min eta 1 := sub_nonneg.mpr (min_le_right _ _)
  have hp : Real.rpow (N k : ℝ) (1 - eta) ≤
      Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) :=
    (Real.rpow_le_rpow_of_exponent_le hbase (sub_le_sub_left (min_le_left eta 1) 1)).trans
      (Real.rpow_le_rpow (zero_le_one.trans hbase) hle hexp)
  have hone : 1 ≤ Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) :=
    Real.one_le_rpow (hbase.trans hle) hexp
  have hhalf : 1 / 2 ≤ (1 / 2) * Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    _ ≤ (N (k + 1) : ℝ) - (N k : ℝ) + 1 / 2 := by linarith only [hleft, hright]
    _ ≤ G * Real.rpow (N k : ℝ) (1 - eta) + 1 / 2 := add_le_add_left hkGap _
    _ ≤ G * Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) +
        (1 / 2) * Real.rpow (canonicalPriceCutoff (N k)) (1 - min eta 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hG) hhalf
    _ = _ := by ring

private lemma canonical_price_cutoff_lower {N : ℕ} (hN : 12 ≤ N) {a M : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hM : 0 ≤ M)
    (hbound : -M ≤ W a (N : ℝ) * robinLogMargin (specified N)) :
    -(4 * M) ≤ W a (canonicalPriceCutoff N) * S (canonicalPriceCutoff N) := by
  obtain ⟨hleft, hright, hprice⟩ := canonical_price_cutoff_spec hN
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 1 < canonicalPriceCutoff N := by linarith only [hNr, hleft]
  obtain ⟨hq, hn, _, _, _⟩ := specified_data (show 3 ≤ N by omega)
  have hstrict := strictInteger_spec hq
  have hopt : IsGoldenResourceOptimal (price (canonicalPriceCutoff N)) (specified N) := by
    rw [hprice]
    exact hstrict.2.2.1
  have hmargin : robinLogMargin (specified N) ≤ S (canonicalPriceCutoff N) :=
    exact_pressure_ge_margin hx hstrict.1 (ActualRobinInterval.log_gt_one hn) hopt
  have hweight : W a (canonicalPriceCutoff N) ≤ 4 * W a (N : ℝ) := by
    exact PolynomialMeshBounds.record_weight ha ha1 hx
      (show (2 : ℝ) ≤ N by linarith only [hNr]) (by linarith only [hNr, hright])
  have hW := (W_pos a hx).le
  exact (PolynomialMeshBounds.rescale_lower hM (show (0 : ℝ) ≤ 4 by norm_num)
    hW hweight hbound).trans (mul_le_mul_of_nonneg_left hmargin hW)

private lemma pressure_le_margin_at_clock {n : ℕ} (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n : ℝ)) : S (Real.log (n : ℝ)) ≤ robinLogMargin n := by
  have hq := price_pos hlog
  have hp : goldenResourceObjective (price (Real.log (n : ℝ))) n ≤
      pressure (price (Real.log (n : ℝ))) :=
    le_csSup (pressure_maximal_spec hq).1 ⟨n, hn, rfl⟩
  rw [golden_resource_sigma_identity _ hn] at hp
  have hid : price (Real.log (n : ℝ)) * Real.log (n : ℝ) =
      1 / Real.log (Real.log (n : ℝ)) := by
    unfold price
    field_simp [ne_of_gt (show 0 < Real.log (n : ℝ) by linarith), (Real.log_pos hlog).ne'] <;> ring
  unfold S robinLogMargin
  linarith only [hp, hid]

private lemma record_theta_le_log {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hu : 0 < u) (hr : FullRecord m u) :
    Chebyshev.theta (largestPrime m : ℝ) ≤ Real.log (m : ℝ) := by
  have hs := (ActualPriceRecordPrimeStructure.price_record_prime_structure hm hu hr).2
  have hsplit := EulerLayerInventoryGrowth.log_factorization_split (show 0 < m by omega)
  have hfirst : (∑ p ∈ m.primeFactors, Real.log p) =
      Chebyshev.theta (largestPrime m : ℝ) := by
    rw [hs, Chebyshev.theta_eq_sum_primesLE_log]
  rw [hfirst] at hsplit
  have hnonneg : 0 ≤ ∑ p ∈ m.primeFactors,
      ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p :=
    sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
  linarith only [hsplit, hnonneg]

private lemma clock_power (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hbeta : (1 / 2 : ℝ) ≤
      D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + epsilon) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      |X - clock X| ≤ C * Real.rpow X
        (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + epsilon) := by
  obtain ⟨C0, hC0, hinventory⟩ := EulerLayerInventoryGrowth.strict_inventory_sqrt_discrepancy
  obtain ⟨C1, hzero⟩ :=
    D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero_abscissa_power_bound epsilon hepsilon
  refine ⟨C0 + max C1 0, by positivity, ?_⟩
  intro X hX
  have hX1 : 1 < X := by linarith
  have hq := price_pos hX1
  have hi := hinventory X hX (integerAt X)
    (by have := strictInteger_pos hq; change 0 < strictInteger (price X); omega)
    (fun p _ => strictInteger_counts hq p)
  have hp := hzero X hX
  have hsqrt : Real.sqrt X ≤ Real.rpow X
      (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + epsilon) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hbeta
  have hi' : |clock X - Chebyshev.psi X| ≤ C0 * Real.rpow X
      (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + epsilon) :=
    hi.trans (mul_le_mul_of_nonneg_left hsqrt hC0.le)
  have hp' : |Chebyshev.psi X - X| ≤ max C1 0 * Real.rpow X
      (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + epsilon) :=
    hp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _))
  have ht := abs_sub_le (clock X) (Chebyshev.psi X) X
  rw [abs_sub_comm X (clock X)]
  nlinarith only [ht, hi', hp']

private lemma all_pressure_to_records (alpha A : ℝ) (halpha : 0 < alpha)
    (halphaHalf : alpha ≤ 1 / 2) (hA : 0 ≤ A)
    (hS : ∃ T : ℝ, ∀ L : ℝ, T ≤ L → -A ≤ W alpha L * S L) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 < u →
      FullRecord m u → T ≤ (largestPrime m : ℝ) →
      -(4 * A) ≤ Real.rpow (largestPrime m : ℝ) alpha *
        Real.log (largestPrime m : ℝ) * robinLogMargin m := by
  obtain ⟨T0, hT0⟩ := hS
  have hpnt := EulerLayerRootCorrection.prime_number_limits.2
  obtain ⟨U, hU⟩ := eventually_atTop.mp
    (hpnt.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  let T : ℝ := max U (max 4 (2 * T0))
  have hT4 : 4 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨T, by linarith, ?_⟩
  intro m hm u hu hrecord hlarge
  let P : ℝ := largestPrime m
  let L : ℝ := Real.log (m : ℝ)
  have hP4 : 4 ≤ P := hT4.trans hlarge
  have hP0 : 0 < P := by linarith
  have hPU : U ≤ P := (le_max_left _ _).trans hlarge
  have htheta : P / 2 ≤ Chebyshev.theta P := by
    have hh := (lt_div_iff₀ hP0).mp (hU P hPU)
    linarith only [hh]
  have hthetaL : Chebyshev.theta P ≤ L := record_theta_le_log hm hu hrecord
  have hL2 : 2 ≤ L := by linarith only [hP4, htheta, hthetaL]
  have hPL : P ≤ 2 * L := by linarith only [htheta, hthetaL]
  have hPT0 : 2 * T0 ≤ P :=
    (le_max_right 4 (2 * T0)).trans ((le_max_right _ _).trans hlarge)
  have hLT0 : T0 ≤ L := by linarith only [hPL, hPT0]
  have hmargin := pressure_le_margin_at_clock (show 1 ≤ m by omega)
    (show 1 < Real.log (m : ℝ) by change 1 < L; linarith)
  have hlower : -A ≤ W alpha L * robinLogMargin m :=
    (hT0 L hLT0).trans (mul_le_mul_of_nonneg_left hmargin
      (W_pos alpha (show 1 < L by linarith)).le)
  exact rescale_lower hA (by norm_num : (0 : ℝ) ≤ 4)
    (W_pos alpha (show 1 < P by linarith)).le
    (record_weight halpha.le (by linarith) (by linarith) hL2 hPL) hlower

private lemma W_eq (alpha : ℝ) {x : ℝ} (hx : 0 < x) :
    W alpha x = Real.rpow x (alpha - 1 / 2) * D x := by
  simpa only [W, D, Real.sqrt_eq_rpow, Real.rpow_eq_pow] using W_factor alpha (1 / 2) hx

private lemma W_ratio_ge (alpha : ℝ) (halpha : alpha ≤ 1 / 2)
    {p x : ℝ} (hp : 1 < p) (hx : 1 < x) (hpx : p ≤ x) :
    D p / D x ≤ W alpha p / W alpha x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxp : 0 < Real.rpow x (alpha - 1 / 2) := Real.rpow_pos_of_pos hx0 _
  have hmono : Real.rpow x (alpha - 1 / 2) ≤ Real.rpow p (alpha - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hp0 hpx (by linarith)
  have hfactor : 1 ≤ Real.rpow p (alpha - 1 / 2) / Real.rpow x (alpha - 1 / 2) :=
    (le_div_iff₀ hxp).mpr (by simpa only [one_mul] using hmono)
  calc
    D p / D x ≤ (D p / D x) *
        (Real.rpow p (alpha - 1 / 2) / Real.rpow x (alpha - 1 / 2)) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hfactor (div_nonneg (D_pos hp).le (D_pos hx).le)
    _ = W alpha p / W alpha x := by
      rw [W_eq alpha hp0, W_eq alpha hx0]
      field_simp [(D_pos hx).ne', hxp.ne']
      <;> ring

private theorem records_to_eventual_WB (alpha : ℝ) (halpha : alpha ≤ 1 / 2)
    (M T : ℝ)
    (hbound : ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      -M ≤ Real.rpow (largestPrime m : ℝ) alpha * Real.log (largestPrime m : ℝ) *
        robinLogMargin m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, -A ≤ W alpha x * B x := by
  let M0 : ℝ := max M 0
  let U0 : ℝ := 2 * Real.sqrt 2 + 1
  let c : ℝ := -(M0 + U0)
  have hMM : M ≤ M0 := le_max_left _ _
  have hM0 : 0 ≤ M0 := le_max_right _ _
  have hU0 : 0 < U0 := by
    dsimp [U0]
    positivity
  have hc : c ≤ 0 := by dsimp [c]; linarith
  obtain ⟨TC, hTC, hC⟩ :=
    RHSharpOriginalRecordMargin.fullC_leading 1 zero_lt_one
  have hratio : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) < D (RHSharpOriginalRecordMargin.Pn x : ℝ) / D x :=
    RHSharpOriginalRecordMargin.normalization.eventually
      (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  refine ⟨-2 * c, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    RHSharpOriginalRecordMargin.Pn_atTop.eventually_ge_atTop (max T TC),
    hratio] with x hx hlarge hr
  obtain ⟨m, lambda, hm, hlambda, hrecord, _hsupport, hP⟩ :=
    RHSharpOriginalRecordMargin.cutoff_record x hx
  have hPT : T ≤ (largestPrime m : ℝ) := by
    rw [hP]
    exact (le_max_left T TC).trans hlarge
  have hPC : TC ≤ (largestPrime m : ℝ) := by
    rw [hP]
    exact (le_max_right T TC).trans hlarge
  have hP2 : (2 : ℝ) ≤ largestPrime m := hTC.trans hPC
  have hP0 : (0 : ℝ) < largestPrime m := by linarith
  have hcorr_abs :
      |D (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m -
        2 * Real.sqrt 2| < 1 := (hC m hm lambda hlambda hrecord hPC).2.2
  have hcorr_upper :
      D (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m ≤ U0 := by
    have hh := (abs_lt.mp hcorr_abs).2
    dsimp [U0]
    linarith
  have hfactor0 : 0 ≤ Real.rpow (largestPrime m : ℝ) (alpha - 1 / 2) :=
    (Real.rpow_pos_of_pos hP0 _).le
  have hfactor1 : Real.rpow (largestPrime m : ℝ) (alpha - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith : (1 : ℝ) ≤ largestPrime m) (by linarith : alpha - 1 / 2 ≤ 0)
  have hpowercorr :
      W alpha (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m ≤
        U0 := by
    calc
      _ = Real.rpow (largestPrime m : ℝ) (alpha - 1 / 2) *
          (D (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m) := by
        rw [W_eq alpha hP0]
        ring
      _ ≤ Real.rpow (largestPrime m : ℝ) (alpha - 1 / 2) * U0 :=
        mul_le_mul_of_nonneg_left hcorr_upper hfactor0
      _ ≤ 1 * U0 := mul_le_mul_of_nonneg_right hfactor1 hU0.le
      _ = U0 := one_mul _
  have hmargin : robinLogMargin m = B (largestPrime m : ℝ) +
      FullArithmeticCorrectionSecondOrder.correction m :=
    RHSharpOriginalRecordMargin.margin_identity hm hlambda hrecord
  have hb := hbound m hm lambda hlambda hrecord hPT
  change -M ≤ W alpha (largestPrime m : ℝ) * robinLogMargin m at hb
  rw [hmargin] at hb
  have hprefix_lower :
      c ≤ W alpha (largestPrime m : ℝ) * B (largestPrime m : ℝ) := by
    dsimp [c]
    nlinarith [hpowercorr, hMM, hb]
  have hPn2 : (2 : ℝ) ≤ RHSharpOriginalRecordMargin.Pn x := by
    simpa only [hP] using hP2
  have hPn_le : RHSharpOriginalRecordMargin.Pn x ≤ ⌊x⌋₊ := by
    unfold RHSharpOriginalRecordMargin.Pn
    apply Finset.sup_le
    intro p hp
    exact (Nat.mem_primesLE.mp hp).1
  have hPnx : (RHSharpOriginalRecordMargin.Pn x : ℝ) ≤ x :=
    (by exact_mod_cast hPn_le : (RHSharpOriginalRecordMargin.Pn x : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith : 0 ≤ x))
  have hpower_ratio : (1 / 2 : ℝ) ≤
      W alpha (RHSharpOriginalRecordMargin.Pn x : ℝ) / W alpha x :=
    hr.le.trans (W_ratio_ge alpha halpha
      (by linarith : 1 < (RHSharpOriginalRecordMargin.Pn x : ℝ))
      (by linarith : 1 < x) hPnx)
  have hDx : W alpha x ≠ 0 := (W_pos alpha (by linarith : 1 < x)).ne'
  have hid :
      (W alpha (RHSharpOriginalRecordMargin.Pn x : ℝ) / W alpha x) *
        (W alpha x * B x) =
        W alpha (largestPrime m : ℝ) * B (largestPrime m : ℝ) := by
    rw [hP, RHSharpOriginalRecordMargin.B_prefix]
    field_simp [hDx]
    <;> ring
  have hnormalized : c ≤
      (W alpha (RHSharpOriginalRecordMargin.Pn x : ℝ) / W alpha x) *
        (W alpha x * B x) := by
    rw [hid]
    exact hprefix_lower
  have hreal := fixed_negative_ratio hc hpower_ratio hnormalized
  linarith

private theorem B_lower_envelope_strip : ∀ (alpha : ℝ), 0 < alpha → alpha ≤ 1 / 2 →
    (∃ C T : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, T ≤ x →
        -C / (Real.rpow x alpha * Real.log x) ≤
          D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x) →
    ∀ rho : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero rho →
      rho.re ≤ 1 - alpha := by
  classical
  intro alpha hα hαhalf hLower
  intro rho hrho
  by_contra hstrip
  have hβbad : 1 - alpha < rho.re := lt_of_not_ge hstrip
  have hβ : (1 / 2 : ℝ) < rho.re := by
    have hα' : 1 / 2 ≤ 1 - alpha := by linarith
    exact lt_of_le_of_lt hα' hβbad
  have hβ1 : rho.re < 1 := hrho.2.2
  have hzero : riemannZeta rho = 0 := by
    simpa only [D5.S3.Weil.Convention.classicalZeta] using hrho.1
  have hrho0 : rho ≠ 0 := by
    intro hz
    have hzre : rho.re = 0 := by simp [hz]
    linarith [hrho.2.1]
  have hrho1 : rho ≠ 1 := by
    intro hz
    have hzre : rho.re = 1 := by simp [hz]
    linarith [hβ1]
  have hden : 0 < ‖rho‖ * ‖rho - 1‖ := by
    exact mul_pos (norm_pos_iff.mpr hrho0)
      (norm_pos_iff.mpr (sub_ne_zero.mpr hrho1))
  let m : ℕ := analyticOrderNatAt riemannZeta rho
  have hpeak_source : 0 < m ∧ rho.im ≠ 0 ∧
      ∀ c : ℝ, 0 ≤ c → c < (m : ℝ) / (‖rho‖ * ‖rho - 1‖) →
        ∀ U : ℝ, ∃ u : ℝ, max U (Real.log 2) < u ∧
          c < u * Real.exp ((1 - rho.re) * u) *
            D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u :=
    D5.S3.Weil.Mertens.CriticalThetaTailPeak.critical_theta_tail_peak
      (ρ := rho) hβ hβ1 hzero
  obtain ⟨hm, _, hpeaks⟩ := hpeak_source
  have hbα : 1 - rho.re < alpha := by linarith only [hβbad]
  have hb1 : 1 - rho.re < 1 := by linarith [hrho.2.1]
  let A : ℝ := (m : ℝ) / (‖rho‖ * ‖rho - 1‖)
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by exact_mod_cast hm) hden
  let c : ℝ := A / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hcA : c < A := by dsimp [c]; linarith
  obtain ⟨C, T, hC, hT⟩ := hLower
  have hF_event : ∀ᶠ x : ℝ in atTop,
      D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x ≤
        C / (Real.rpow x alpha * Real.log x) + 4 / x := by
    have hp :=
      D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.eventually
        (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    filter_upwards [eventually_ge_atTop T, hp,
      eventually_gt_atTop (4 : ℝ)] with x hxT hxratio hx4
    have hx0 : 0 < x := by linarith
    have hx2 : 2 ≤ x := by linarith
    have hx2' : 2 < x := by linarith
    have hxθ : 2 < Chebyshev.theta x := by
      have h := (lt_div_iff₀ hx0).mp hxratio
      linarith
    have hupper :=
      (D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich.actual_theta_reparametrized_sandwich
        hx2' hxθ).2
    have hH : Mertens.E₃ x + Mertens.E₂p x ≤ 4 / x := by
      exact (le_abs_self _).trans
        (D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.finite_cancellation hx2)
    have hBupper :
        D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x ≤
          -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x + 4 / x := by
      linarith only [hupper, hH]
    have hB : -(C / (Real.rpow x alpha * Real.log x)) ≤
        D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x := by
      simpa only [neg_div] using hT x hxT
    linarith
  have hF_u : ∀ᶠ u : ℝ in atTop,
      D5.S3.Weil.Mertens.ActualThetaTailLaplace.F (Real.exp u) ≤
        C / (Real.rpow (Real.exp u) alpha * Real.log (Real.exp u)) +
          4 / Real.exp u :=
    Real.tendsto_exp_atTop.eventually hF_event
  have hsub : ∀ u : ℝ,
      D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u =
        D5.S3.Weil.Mertens.ActualThetaTailLaplace.F (Real.exp u) :=
    D5.S3.Weil.Mertens.ActualThetaTailLaplace.actual_theta_tail_laplace_ode.2.2.2.1
  have hscaled_event : ∀ᶠ u : ℝ in atTop,
      u * Real.exp ((1 - rho.re) * u) *
          D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u ≤
        C * Real.exp ((1 - rho.re - alpha) * u) +
          4 * u * Real.exp ((1 - rho.re - 1) * u) := by
    filter_upwards [hF_u, eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have hu_exp : 0 < u * Real.exp ((1 - rho.re) * u) :=
      mul_pos hu0 (Real.exp_pos _)
    have hfu :
        D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u ≤
          C / (Real.rpow (Real.exp u) alpha * Real.log (Real.exp u)) +
            4 / Real.exp u := by
      rw [hsub u]
      exact hu
    have hpow : Real.rpow (Real.exp u) alpha = Real.exp (alpha * u) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
      congr 1
      ring
    have hratioα :
        Real.exp ((1 - rho.re) * u) / Real.exp (alpha * u) =
          Real.exp ((1 - rho.re - alpha) * u) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hratio1 :
        Real.exp ((1 - rho.re) * u) / Real.exp u =
          Real.exp ((1 - rho.re - 1) * u) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hmul := mul_le_mul_of_nonneg_left hfu hu_exp.le
    rw [Real.log_exp, hpow] at hmul
    calc
      u * Real.exp ((1 - rho.re) * u) *
          D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u ≤
        u * Real.exp ((1 - rho.re) * u) *
          (C / (Real.exp (alpha * u) * u) + 4 / Real.exp u) := hmul
      _ = C * Real.exp ((1 - rho.re - alpha) * u) +
          4 * u * Real.exp ((1 - rho.re - 1) * u) := by
        calc
          _ = C * (Real.exp ((1 - rho.re) * u) /
                Real.exp (alpha * u)) +
              4 * u * (Real.exp ((1 - rho.re) * u) / Real.exp u) := by
            field_simp [hu0.ne', (Real.exp_pos (alpha * u)).ne',
              (Real.exp_pos u).ne'] <;> ring
          _ = _ := by rw [hratioα, hratio1]
  have hlimα : Tendsto (fun u : ℝ =>
      C * Real.exp ((1 - rho.re - alpha) * u)) atTop (𝓝 0) := by
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0 : ℝ) (alpha - (1 - rho.re)) (by linarith only [hbα])
    have hbase' : Tendsto (fun u : ℝ =>
        Real.exp ((1 - rho.re - alpha) * u)) atTop (𝓝 0) := by
      simpa only [Real.rpow_zero, one_mul,
        show -(alpha - (1 - rho.re)) = 1 - rho.re - alpha by ring] using hbase
    simpa only [mul_zero] using hbase'.const_mul C
  have hlim1 : Tendsto (fun u : ℝ =>
      4 * u * Real.exp ((1 - rho.re - 1) * u)) atTop (𝓝 0) := by
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (1 - (1 - rho.re)) (by linarith only [hb1])
    have hbase' : Tendsto (fun u : ℝ =>
        u * Real.exp ((1 - rho.re - 1) * u)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one,
        show -(1 - (1 - rho.re)) = 1 - rho.re - 1 by ring] using hbase
    simpa only [mul_zero, mul_assoc] using hbase'.const_mul 4
  have hsmall : ∀ᶠ u : ℝ in atTop,
      C * Real.exp ((1 - rho.re - alpha) * u) +
          4 * u * Real.exp ((1 - rho.re - 1) * u) < c := by
    have hsum : Tendsto (fun u : ℝ =>
        C * Real.exp ((1 - rho.re - alpha) * u) +
          4 * u * Real.exp ((1 - rho.re - 1) * u)) atTop (𝓝 0) := by
      simpa only [zero_add] using hlimα.add hlim1
    exact hsum.eventually (Iio_mem_nhds hc)
  have hupper_event : ∀ᶠ u : ℝ in atTop,
      u * Real.exp ((1 - rho.re) * u) *
          D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u < c := by
    filter_upwards [hscaled_event, hsmall] with u hu hs
    exact lt_of_le_of_lt hu hs
  obtain ⟨U, hU⟩ := eventually_atTop.mp hupper_event
  obtain ⟨u, hu, hpeak⟩ := hpeaks c (le_of_lt hc) hcA U
  have huU : U ≤ u :=
    (le_max_left U (Real.log 2)).trans (le_of_lt hu)
  have hupper := hU u huU
  linarith

/-- At weights `0 < alpha ≤ 1 / 2`, the strict record at the literal
first-layer price of `N k + 1` detects the closed zero strip along any
strictly increasing natural mesh with a power-saving gap. -/
theorem result_of_power_saving_gaps {N : ℕ → ℕ} (hN : StrictMono N)
    {G eta : ℝ} (hG : 0 ≤ G) (heta : 0 < eta)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * Real.rpow (N k : ℝ) (1 - eta))
    (alpha : ℝ) (halpha : 0 < alpha) (hhalf : alpha ≤ 1 / 2) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ k : ℕ in atTop,
      -M ≤ Real.rpow (N k : ℝ) alpha * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))) ↔
      (∀ rho : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha) := by
  classical
  constructor
  · rintro ⟨M, hM, hsample⟩
    by_contra hnotstrip
    push Not at hnotstrip
    obtain ⟨rho, hrho, hbad⟩ := hnotstrip
    let Theta : ℝ := D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa
    have hThetaBad : 1 - alpha < Theta := hbad.trans_le
      (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zero_re_le_abscissa hrho)
    have hThetaHalf : 1 / 2 < Theta := by linarith only [hThetaBad, hhalf]
    have hThetaOne : Theta ≤ 1 := by
      change sSup (Complex.re '' {z : ℂ | IsNontrivialZero z}) ≤ 1
      apply csSup_le zero_real_parts_nonempty
      rintro x ⟨z, hz, rfl⟩
      exact hz.2.2.le
    let eta' : ℝ := min eta 1
    have heta' : 0 < eta' := lt_min heta (by norm_num)
    have hmax : max (1 - alpha) (Theta - eta') < Theta :=
      max_lt_iff.mpr ⟨hThetaBad, sub_lt_self _ heta'⟩
    obtain ⟨sigma, hsigmaLower, hsigmaTheta⟩ := exists_between hmax
    have hsigmaAlpha : 1 - alpha < sigma :=
      (le_max_left _ _).trans_lt hsigmaLower
    have hsigmaGap : Theta - eta' < sigma :=
      (le_max_right _ _).trans_lt hsigmaLower
    -- This strict inequality also holds when the supremum Theta is 1.
    have hsigmaOne : sigma < 1 := hsigmaTheta.trans_le hThetaOne
    let a : ℝ := 1 - sigma
    let epsilon : ℝ := (sigma + eta' - Theta) / 2
    let beta : ℝ := Theta + epsilon
    have ha : 0 < a := by dsimp only [a]; linarith only [hsigmaOne]
    have haAlpha : a < alpha := by dsimp only [a]; linarith only [hsigmaAlpha]
    have haHalf : a ≤ 1 / 2 := haAlpha.le.trans hhalf
    have hepsilon : 0 < epsilon := by dsimp only [epsilon]; linarith only [hsigmaGap]
    have hbetaHalf : 1 / 2 < beta := by
      dsimp only [beta]
      linarith only [hThetaHalf, hepsilon]
    have hbalance : a + beta - eta' ≤ 1 := by
      dsimp only [a, beta, epsilon]
      linarith only [hsigmaGap]
    have haOne : a ≤ 1 := by linarith only [haHalf]
    have hsamplePressure : ∀ᶠ k : ℕ in atTop,
        -(4 * M) ≤ W a (canonicalPriceCutoff (N k)) * S (canonicalPriceCutoff (N k)) := by
      have hlarge := hN.tendsto_atTop.eventually (eventually_ge_atTop (12 : ℕ))
      filter_upwards [hsample, hlarge] with k hb hk
      have hX : 1 < (N k : ℝ) := by exact_mod_cast (show 1 < N k by omega)
      exact canonical_price_cutoff_lower hk ha.le haOne hM
        (sample_exponent_lower hM haAlpha.le hX hb)
    have hcutoffTop : Tendsto (fun k => canonicalPriceCutoff (N k)) atTop atTop :=
      tendsto_atTop_mono (fun k => le_canonical_price_cutoff (N k)) (mesh_atTop hN)
    obtain ⟨C, hC, hclock⟩ := clock_power epsilon hepsilon hbetaHalf.le
    obtain ⟨A, hA, hpressure⟩ := pressure_mesh_samples_to_all
      (mesh := fun k => canonicalPriceCutoff (N k))
      (canonical_price_cutoff_strictMono.comp hN) hcutoffTop
      (G := G + 1 / 2) (eta := eta') (alpha := a) (beta := beta) (A := 4 * M)
      (by linarith only [hG]) heta' ha.le haOne (by linarith only [hbetaHalf]) hC
      (by positivity) hbalance (canonical_price_cutoff_gap hN hG hgap) hclock hsamplePressure
    obtain ⟨T, _hT, hrecords⟩ := all_pressure_to_records a A ha haHalf hA hpressure
    obtain ⟨C0, hC0, hWB⟩ := records_to_eventual_WB a haHalf (4 * A) T hrecords
    obtain ⟨T0, hT0⟩ := eventually_atTop.mp hWB
    have hBlower : ∃ C T : ℝ, 0 ≤ C ∧ ∀ x : ℝ, T ≤ x →
        -C / (Real.rpow x a * Real.log x) ≤ B x := by
      refine ⟨C0, max T0 2, hC0, ?_⟩
      intro x hx
      have hx2 : 2 ≤ x := (le_max_right T0 2).trans hx
      have hWx : 0 < W a x := W_pos a (by linarith)
      apply (div_le_iff₀ hWx).mpr
      have hh := hT0 x ((le_max_left T0 2).trans hx)
      change -C0 ≤ B x * W a x
      nlinarith only [hh]
    have hstrip := B_lower_envelope_strip a ha haHalf hBlower
    have hsup : Theta ≤ sigma := by
      change sSup (Complex.re '' {z : ℂ | IsNontrivialZero z}) ≤ sigma
      apply csSup_le zero_real_parts_nonempty
      rintro x ⟨z, hz, rfl⟩
      have hh := hstrip z hz
      dsimp only [a] at hh
      linarith only [hh]
    exact (not_le_of_gt hsigmaTheta) hsup
  · intro hstrip
    obtain ⟨C, TB, hC, _hTB, hB⟩ :=
      D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.actual_B_critical_strip_envelope
        alpha halpha hhalf hstrip
    obtain ⟨TC, hTC, hcorr⟩ := RHSharpOriginalRecordMargin.fullC_leading 1 zero_lt_one
    have hlargeN := (mesh_atTop hN).eventually (eventually_ge_atTop TB)
    have hlargeP := (RHSharpOriginalRecordMargin.Pn_atTop.comp
      (mesh_atTop hN)).eventually (eventually_ge_atTop TC)
    have hlargeNat := hN.tendsto_atTop.eventually (eventually_ge_atTop (3 : ℕ))
    refine ⟨C, hC, ?_⟩
    filter_upwards [hlargeN, hlargeP, hlargeNat] with k hNlarge hPlarge hk
    have hX : 1 < (N k : ℝ) := by exact_mod_cast (show 1 < N k by omega)
    obtain ⟨hu, hm, hmr, _, hmP⟩ := specified_data hk
    have hPC : TC ≤ (largestPrime (specified (N k)) : ℝ) := by
      simpa only [hmP, Function.comp_def] using hPlarge
    have hP2 : (2 : ℝ) ≤ largestPrime (specified (N k)) := hTC.trans hPC
    have hD : 0 < D (largestPrime (specified (N k)) : ℝ) := D_pos (by linarith)
    have hcorrAbs := (hcorr _ (by omega) _ hu hmr hPC).2.2
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    have hcorrScaled : 0 ≤ D (largestPrime (specified (N k)) : ℝ) *
        FullArithmeticCorrectionSecondOrder.correction (specified (N k)) := by
      have hh := (abs_lt.mp hcorrAbs).1
      nlinarith only [hh, hsqrt]
    have hcorr0 : 0 ≤ FullArithmeticCorrectionSecondOrder.correction (specified (N k)) :=
      (mul_nonneg_iff_of_pos_left hD).mp hcorrScaled
    have hmargin : B (N k : ℝ) ≤ robinLogMargin (specified (N k)) := by
      rw [RHSharpOriginalRecordMargin.margin_identity (by omega) hu hmr,
        hmP, RHSharpOriginalRecordMargin.B_prefix]
      exact le_add_of_nonneg_right hcorr0
    have hWx : 0 < W alpha (N k : ℝ) := W_pos alpha hX
    have hb : -C / W alpha (N k : ℝ) ≤ B (N k : ℝ) := by
      simpa only [W, neg_div] using (abs_le.mp (hB _ hNlarge)).1
    have hBscaled : -C ≤ W alpha (N k : ℝ) * B (N k : ℝ) := by
      have hh := (div_le_iff₀ hWx).mp hb
      nlinarith only [hh]
    exact hBscaled.trans (mul_le_mul_of_nonneg_left hmargin hWx.le)

theorem result (r : ℕ) (hr : 2 ≤ r) (alpha : ℝ)
    (halpha : 0 < alpha) (hhalf : alpha ≤ 1 / 2) :
    (∃ M : ℝ, 0 ≤ M ∧ ∃ k0 : ℕ, 2 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k →
      -M ≤ Real.rpow (((k ^ r : ℕ) : ℝ)) alpha * Real.log (((k ^ r : ℕ) : ℝ)) *
        robinLogMargin
          (strictInteger (firstLayerPrice ((((k ^ r : ℕ) : ℝ)) + 1)))) ↔
      (∀ rho : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hmesh := result_of_power_saving_gaps (power_strictMono r hr)
    (G := (r : ℝ) * (2 : ℝ) ^ (r - 1)) (eta := 1 / (r : ℝ))
    (by positivity) (one_div_pos.mpr hr0) (polynomial_gap r hr) alpha halpha hhalf
  constructor
  · rintro ⟨M, hM, K, _, hK⟩
    exact hmesh.mp ⟨M, hM, eventually_atTop.mpr ⟨K, hK⟩⟩
  · intro hstrip
    obtain ⟨M, hM, hbound⟩ := hmesh.mpr hstrip
    obtain ⟨K, hK⟩ := eventually_atTop.mp hbound
    refine ⟨M, hM, max K 2, le_max_right _ _, ?_⟩
    intro k hk
    exact hK k ((le_max_left K 2).trans hk)

end D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
