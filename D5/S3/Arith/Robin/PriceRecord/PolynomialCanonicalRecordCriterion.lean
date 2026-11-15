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
/-! Full-layer polynomial sampling and the closed strip of actual zeta zeros. -/
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

private lemma W_le_D {alpha X : ℝ} (halpha : alpha ≤ 1 / 2) (hX : 1 < X) :
    W alpha X ≤ D X := by
  have hp : Real.rpow X alpha ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX.le halpha
  exact mul_le_mul_of_nonneg_right hp (Real.log_pos hX).le

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

private lemma exact_support {N : ℕ} (hN : 12 < N) (hcomposite : ¬N.Prime) :
    (strictInteger (price (N : ℝ))).primeFactors = Nat.primesLE N := by
  have hNr : (12 : ℝ) < N := by exact_mod_cast hN
  have hq := price_pos (show 1 < (N : ℝ) by linarith)
  obtain ⟨rho, hrho, hbelow, hhalf, hprice, _⟩ :=
    ActualBalancedCutoff.half_shift_cutoff hNr
  apply support_of_active hq N
  intro p hp
  rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
  change price (N : ℝ) < firstLayerPrice (p : ℝ) ↔ p ≤ N
  rw [← hprice]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hrho1 : 1 < rho := by linarith
  have hcut : firstLayerPrice rho < firstLayerPrice (p : ℝ) ↔ (p : ℝ) < rho := by
    constructor
    · intro h
      by_contra hn
      have hh := ActualBalancedCutoff.firstLayerPrice_strictAnti.antitoneOn
        hrho1 hp1 (le_of_not_gt hn)
      exact (not_lt_of_ge hh) h
    · exact ActualBalancedCutoff.firstLayerPrice_strictAnti hp1 hrho1
  rw [hcut]
  constructor
  · intro h
    have hpN : (p : ℝ) < N := by linarith
    have : p < N := by exact_mod_cast hpN
    omega
  · intro hpN
    have hpne : p ≠ N := by intro he; exact hcomposite (he ▸ hp)
    have hpNm : p + 1 ≤ N := by omega
    have hh : (p : ℝ) + 1 ≤ N := by exact_mod_cast hpNm
    linarith

private lemma same_prime_margin :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
      ∀ u v : ℝ, 0 < u → 0 < v → FullRecord m u → FullRecord n v →
      largestPrime m = largestPrime n → T ≤ (largestPrime m : ℝ) →
      -(1 / 2 : ℝ) ≤ D (largestPrime m : ℝ) * (robinLogMargin n - robinLogMargin m) := by
  obtain ⟨T, hT, hlead⟩ := RHSharpOriginalRecordMargin.fullC_leading (1 / 4) (by norm_num)
  refine ⟨T, hT, ?_⟩
  intro m n hm hn u v hu hv hmr hnr hsame hlarge
  have hmC := (hlead m hm u hu hmr hlarge).2.2
  have hnlarge : T ≤ (largestPrime n : ℝ) := by simpa only [hsame] using hlarge
  have hnC := (hlead n hn v hv hnr hnlarge).2.2
  rw [← hsame] at hnC
  rw [RHSharpOriginalRecordMargin.margin_identity hm hu hmr,
    RHSharpOriginalRecordMargin.margin_identity hn hv hnr, ← hsame]
  have hl := (abs_lt.mp hnC).1
  have hh := (abs_lt.mp hmC).2
  nlinarith only [hl, hh]

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

private lemma exact_data (r : ℕ) (hr : 2 ≤ r) {k : ℕ} (hk : 4 ≤ k) :
    0 < price ((k ^ r : ℕ) : ℝ) ∧
    3 ≤ strictInteger (price ((k ^ r : ℕ) : ℝ)) ∧
    FullRecord (strictInteger (price ((k ^ r : ℕ) : ℝ)))
      (price ((k ^ r : ℕ) : ℝ)) ∧
    largestPrime (strictInteger (price ((k ^ r : ℕ) : ℝ))) = Pn ((k ^ r : ℕ) : ℝ) := by
  have hN := power_large r hr hk
  have hX : 1 < ((k ^ r : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < k ^ r by omega)
  have hq := price_pos hX
  have hs := exact_support (show 12 < k ^ r by omega)
    (Nat.Prime.not_prime_pow (x := k) hr)
  exact ⟨hq, size_of_support hq (by omega) hs, strict_record hq, largest_of_support hs⟩

private lemma sample_margin_transfer (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ k : ℕ in atTop,
      -1 ≤ D ((k ^ r : ℕ) : ℝ) *
        (robinLogMargin (strictInteger (price ((k ^ r : ℕ) : ℝ))) -
          robinLogMargin (specified (k ^ r))) := by
  obtain ⟨T, _, hT⟩ := same_prime_margin
  have hlarge := (RHSharpOriginalRecordMargin.Pn_atTop.comp (power_atTop r hr)).eventually
    (eventually_ge_atTop T)
  have hratio := (RHSharpOriginalRecordMargin.normalization.comp (power_atTop r hr)).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hlarge, hratio] with k hk hP hratio
  have hN := power_large r hr hk
  obtain ⟨hu, hm, hmr, _, hmP⟩ := specified_data (show 3 ≤ k ^ r by omega)
  obtain ⟨hv, hn, hnr, hnP⟩ := exact_data r hr hk
  have hsame : largestPrime (specified (k ^ r)) =
      largestPrime (strictInteger (price ((k ^ r : ℕ) : ℝ))) := hmP.trans hnP.symm
  have hbase := hT _ _ (by omega) (by omega) _ _ hu hv hmr hnr hsame
    (by simpa only [hmP, Function.comp_def] using hP)
  rw [hmP] at hbase
  have hDN : 0 < D ((k ^ r : ℕ) : ℝ) := D_pos (by
    exact_mod_cast (show 1 < k ^ r by omega))
  have hid : D (Pn ((k ^ r : ℕ) : ℝ) : ℝ) *
      (robinLogMargin (strictInteger (price ((k ^ r : ℕ) : ℝ))) -
        robinLogMargin (specified (k ^ r))) =
      (D (Pn ((k ^ r : ℕ) : ℝ) : ℝ) / D ((k ^ r : ℕ) : ℝ)) *
      (D ((k ^ r : ℕ) : ℝ) *
        (robinLogMargin (strictInteger (price ((k ^ r : ℕ) : ℝ))) -
          robinLogMargin (specified (k ^ r)))) := by
    field_simp [hDN.ne'] <;> ring
  rw [hid] at hbase
  have hh := fixed_negative_ratio (by norm_num : -(1 / 2 : ℝ) ≤ 0) hratio.le hbase
  calc
    -1 = 2 * (-(1 / 2 : ℝ)) := by norm_num
    _ ≤ _ := hh

private lemma sampled_to_pressure (r : ℕ) (hr : 2 ≤ r)
    (a : ℝ) (haHalf : a ≤ 1 / 2) {M : ℝ} {k0 : ℕ}
    (hbound : ∀ k : ℕ, k0 ≤ k →
      -M ≤ W a ((k ^ r : ℕ) : ℝ) * robinLogMargin (specified (k ^ r))) :
    ∀ᶠ k : ℕ in atTop,
      -(M + 1) ≤ W a ((k ^ r : ℕ) : ℝ) * S ((k ^ r : ℕ) : ℝ) := by
  filter_upwards [sample_margin_transfer r hr, eventually_ge_atTop k0,
    eventually_ge_atTop (4 : ℕ)] with k htransfer hk0 hk
  obtain ⟨hq, hn, _, _⟩ := exact_data r hr hk
  have hN := power_large r hr hk
  have hX : 1 < ((k ^ r : ℕ) : ℝ) := by exact_mod_cast (show 1 < k ^ r by omega)
  have htransferW : -1 ≤ W a ((k ^ r : ℕ) : ℝ) *
      (robinLogMargin (strictInteger (price ((k ^ r : ℕ) : ℝ))) -
        robinLogMargin (specified (k ^ r))) := by
    have hh := rescale_lower (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) (W_pos a hX).le
      (by simpa only [one_mul] using W_le_D haHalf hX) htransfer
    simpa only [one_mul] using hh
  have hS := mul_le_mul_of_nonneg_left
    (exact_pressure_ge_margin hX (by omega) (ActualRobinInterval.log_gt_one hn)
      (strictInteger_spec hq).2.2.1) (W_pos a hX).le
  have hm := hbound k hk0
  nlinarith only [htransferW, hS, hm]

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

theorem result (r : ℕ) (hr : 2 ≤ r) (alpha : ℝ)
    (halpha : 0 < alpha) (hhalf : alpha ≤ 1 / 2) :
    (∃ M : ℝ, 0 ≤ M ∧ ∃ k0 : ℕ, 2 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k →
      -M ≤ Real.rpow (((k ^ r : ℕ) : ℝ)) alpha * Real.log (((k ^ r : ℕ) : ℝ)) *
        robinLogMargin
          (strictInteger (firstLayerPrice ((((k ^ r : ℕ) : ℝ)) + 1)))) ↔
      (∀ rho : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha) := by
  classical
  constructor
  · rintro ⟨M, hM, k0, hk0, hsample⟩
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
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hmax : max (1 - alpha) (Theta - 1 / (r : ℝ)) < Theta := by
      apply max_lt_iff.mpr
      exact ⟨hThetaBad, sub_lt_self _ (one_div_pos.mpr hr0)⟩
    obtain ⟨sigma, hsigmaLower, hsigmaTheta⟩ := exists_between hmax
    have hsigmaAlpha : 1 - alpha < sigma :=
      (le_max_left _ _).trans_lt hsigmaLower
    have hsigmaHalf : 1 / 2 < sigma := by linarith only [hsigmaAlpha, hhalf]
    have hsigmaGap : Theta - 1 / (r : ℝ) < sigma :=
      (le_max_right _ _).trans_lt hsigmaLower
    have hsigmaOne : sigma < 1 := hsigmaTheta.trans_le hThetaOne
    let a : ℝ := 1 - sigma
    let epsilon : ℝ := (sigma + 1 / (r : ℝ) - Theta) / 2
    let beta : ℝ := Theta + epsilon
    have ha : 0 < a := by dsimp only [a]; linarith only [hsigmaOne]
    have haAlpha : a < alpha := by dsimp only [a]; linarith only [hsigmaAlpha]
    have haHalf : a ≤ 1 / 2 := haAlpha.le.trans hhalf
    have hepsilon : 0 < epsilon := by dsimp only [epsilon]; linarith only [hsigmaGap]
    have hbetaHalf : 1 / 2 < beta := by
      dsimp only [beta]
      linarith only [hThetaHalf, hepsilon]
    have hmesh : a + beta - 1 - 1 / (r : ℝ) = -epsilon := by
      dsimp only [a, beta, epsilon]
      ring
    have hgap : beta - 1 / (r : ℝ) < sigma := by
      dsimp only [a] at hmesh
      linarith only [hmesh, hepsilon]
    have hsampleA : ∀ k : ℕ, k0 ≤ k →
        -M ≤ W a ((k ^ r : ℕ) : ℝ) * robinLogMargin (specified (k ^ r)) := by
      intro k hk
      have hk2 : 2 ≤ k := hk0.trans hk
      have hkr : k ≤ k ^ r := by
        calc
          k = k ^ 1 := by simp
          _ ≤ k ^ r := pow_le_pow_right₀ (by omega : 1 ≤ k) (by omega : 1 ≤ r)
      have hN : 1 < ((k ^ r : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < k ^ r by omega)
      have hb : -M ≤ W alpha ((k ^ r : ℕ) : ℝ) *
          robinLogMargin (specified (k ^ r)) := hsample k hk
      exact sample_exponent_lower hM haAlpha.le hN hb
    obtain ⟨C, hC, hclock⟩ := clock_power epsilon hepsilon hbetaHalf.le
    obtain ⟨A, hA, hpressure⟩ := pressure_samples_to_all r hr beta sigma C (M + 1)
      hC (by linarith) hsigmaHalf hsigmaOne (by linarith only [hbetaHalf]) hgap
      hclock (sampled_to_pressure r hr a haHalf hsampleA)
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
    have hlargeN := (power_atTop r hr).eventually (eventually_ge_atTop TB)
    have hlargeP := (RHSharpOriginalRecordMargin.Pn_atTop.comp
      (power_atTop r hr)).eventually (eventually_ge_atTop TC)
    have hbound : ∀ᶠ k : ℕ in atTop,
        -C ≤ W alpha ((k ^ r : ℕ) : ℝ) * robinLogMargin (specified (k ^ r)) := by
      filter_upwards [hlargeN, hlargeP, eventually_ge_atTop (4 : ℕ)]
        with k hNlarge hPlarge hk
      have hN := power_large r hr hk
      have hX : 1 < ((k ^ r : ℕ) : ℝ) := by exact_mod_cast (show 1 < k ^ r by omega)
      obtain ⟨hu, hm, hmr, _, hmP⟩ := specified_data (show 3 ≤ k ^ r by omega)
      have hPC : TC ≤ (largestPrime (specified (k ^ r)) : ℝ) := by
        simpa only [hmP, Function.comp_def] using hPlarge
      have hP2 : (2 : ℝ) ≤ largestPrime (specified (k ^ r)) := hTC.trans hPC
      have hD : 0 < D (largestPrime (specified (k ^ r)) : ℝ) := D_pos (by linarith)
      have hcorrAbs := (hcorr _ (by omega) _ hu hmr hPC).2.2
      have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
      have hcorrScaled : 0 ≤ D (largestPrime (specified (k ^ r)) : ℝ) *
          FullArithmeticCorrectionSecondOrder.correction (specified (k ^ r)) := by
        have hh := (abs_lt.mp hcorrAbs).1
        nlinarith only [hh, hsqrt]
      have hcorr0 : 0 ≤ FullArithmeticCorrectionSecondOrder.correction (specified (k ^ r)) :=
        (mul_nonneg_iff_of_pos_left hD).mp hcorrScaled
      have hmargin : B ((k ^ r : ℕ) : ℝ) ≤ robinLogMargin (specified (k ^ r)) := by
        rw [RHSharpOriginalRecordMargin.margin_identity (by omega) hu hmr,
          hmP, RHSharpOriginalRecordMargin.B_prefix]
        exact le_add_of_nonneg_right hcorr0
      have hWx : 0 < W alpha ((k ^ r : ℕ) : ℝ) := W_pos alpha hX
      have hb : -C / W alpha ((k ^ r : ℕ) : ℝ) ≤ B ((k ^ r : ℕ) : ℝ) := by
        simpa only [W, neg_div] using (abs_le.mp (hB _ hNlarge)).1
      have hBscaled : -C ≤ W alpha ((k ^ r : ℕ) : ℝ) * B ((k ^ r : ℕ) : ℝ) := by
        have hh := (div_le_iff₀ hWx).mp hb
        nlinarith only [hh]
      exact hBscaled.trans (mul_le_mul_of_nonneg_left hmargin hWx.le)
    obtain ⟨K, hK⟩ := eventually_atTop.mp hbound
    refine ⟨C, hC, max K 2, le_max_right _ _, ?_⟩
    intro k hk
    exact hK k ((le_max_left K 2).trans hk)
end D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
