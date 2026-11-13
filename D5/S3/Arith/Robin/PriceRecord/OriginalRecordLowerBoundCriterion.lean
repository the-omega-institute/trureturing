/- GID: D5/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OriginalRecordLowerBoundCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual one-sided normalized lower bounds for original strict records characterize RH. -/

import D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.Mertens.WeightedTailInverse
import D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
import D5.S3.Weil.Mertens.IntegratedExplicit.TrivialZeroLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
The complete logarithmic weighted-tail inverse transfers the original record
bound to an upper bound on the literal arithmetic kernel. The arbitrary affine
tail criterion then supplies the converse. The conclusion is an equivalence
about original strict integer records; it does not establish RH or a finite
closure of the integer Robin inequalities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D B)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel Q U)
open D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open D5.S3.Weil.Mertens.IntegratedExplicit (trivialT trivialT_le_mass)

namespace D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion

private lemma D_pos {x : ℝ} (hx : 1 < x) : 0 < D x := by
  exact mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos hx)

/-- Division by the positive ratio is safe because the constant is fixed and
nonpositive.  No bound on the absolute value of the variable is used. -/
private lemma fixed_negative_ratio {c r b : ℝ} (hc : c ≤ 0)
    (hr : (1 / 2 : ℝ) ≤ r) (hb : c ≤ r * b) : 2 * c ≤ b := by
  have hr0 : 0 < r := by linarith
  have hcr : r * c ≤ (1 / 2 : ℝ) * c :=
    mul_le_mul_of_nonpos_right hr hc
  calc
    2 * c ≤ c / r := (le_div_iff₀ hr0).mpr (by nlinarith [hcr])
    _ ≤ b := (div_le_iff₀ hr0).mpr (by nlinarith [hb])

/-- The least global optimizer with the prescribed prime prefix is an actual
original record.  Its full correction is bounded unconditionally. -/
private theorem records_to_eventual_DB (M T : ℝ)
    (hbound : ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      -M ≤ D (largestPrime m : ℝ) * robinLogMargin m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, -A ≤ D x * B x := by
  let M0 : ℝ := max M 0
  let U0 : ℝ := 2 * Real.sqrt 2 + 1
  let c : ℝ := -(M0 + U0)
  have hMM : M ≤ M0 := le_max_left _ _
  have hM0 : 0 ≤ M0 := le_max_right _ _
  have hU0 : 0 < U0 := by
    dsimp [U0]
    positivity
  have hc : c ≤ 0 := by dsimp [c]; linarith
  obtain ⟨TC, _hTC, hC⟩ :=
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
  have hcorr := hC m hm lambda hlambda hrecord hPC
  have hcorr_abs :
      |D (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m -
        2 * Real.sqrt 2| < 1 := hcorr.2.2
  have hcorr_upper :
      D (largestPrime m : ℝ) * FullArithmeticCorrectionSecondOrder.correction m ≤ U0 := by
    have hh := (abs_lt.mp hcorr_abs).2
    dsimp [U0]
    linarith
  have hmargin : robinLogMargin m = B (largestPrime m : ℝ) +
      FullArithmeticCorrectionSecondOrder.correction m :=
    RHSharpOriginalRecordMargin.margin_identity hm hlambda hrecord
  have hb := hbound m hm lambda hlambda hrecord hPT
  rw [hmargin] at hb
  have hprefix_lower : c ≤ D (largestPrime m : ℝ) * B (largestPrime m : ℝ) := by
    dsimp [c]
    nlinarith [hcorr_upper, hMM, hb]
  have hDx : D x ≠ 0 := (D_pos (by linarith : 1 < x)).ne'
  have hid :
      (D (RHSharpOriginalRecordMargin.Pn x : ℝ) / D x) * (D x * B x) =
        D (largestPrime m : ℝ) * B (largestPrime m : ℝ) := by
    rw [hP, RHSharpOriginalRecordMargin.B_prefix]
    field_simp [hDx]
    <;> ring
  have hnormalized : c ≤
      (D (RHSharpOriginalRecordMargin.Pn x : ℝ) / D x) * (D x * B x) := by
    rw [hid]
    exact hprefix_lower
  have hreal := fixed_negative_ratio hc hr.le hnormalized
  linarith

/-- The unconditional PNT alone pays the domain of log-log tangency. -/
private lemma eventually_theta_gt_one :
    ∀ᶠ x : ℝ in atTop, 1 < Chebyshev.theta x := by
  have htheta := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    htheta.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with x hx ht
  have hh := (lt_div_iff₀ (by linarith : 0 < x)).mp ht
  linarith

/-- The existing strict log-log tangent theorem proves the genuine concavity
estimate on `(1, infinity)`; equality of the arguments is handled separately.
Its slope is the literal derivative `1 / (x * log x)`. -/
private lemma loglog_tangent_le {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    Real.log (Real.log y) - Real.log (Real.log x) ≤
      (y - x) / (x * Real.log x) := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hh := RestrictedDivisorStrictInventory.loglog_tangent hx hy hxy
    simpa only [D5.S3.Arith.Robin.ActualRobinClockCovariance.g, mul_one_div] using hh.le

/-- All three terms are the actual arithmetic ones.  In particular E3 is
prime-only, whereas the complete ledger retains all Mangoldt prime powers. -/
private lemma B_le_weightedTail {x : ℝ} (hx : 2 ≤ x)
    (htheta : 1 < Chebyshev.theta x) :
    B x ≤ weightedTail psiErrorKernel x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hden : 0 < x * Real.log x := mul_pos hx0 (Real.log_pos hx1)
  have htangent := loglog_tangent_le hx1 htheta
  have htheta_psi :
      (Chebyshev.theta x - x) / (x * Real.log x) ≤
        (Chebyshev.psi x - x) / (x * Real.log x) :=
    div_le_div_of_nonneg_right (sub_le_sub_right (Chebyshev.theta_le_psi x) x) hden.le
  have hledger := (CompleteMertensPeak.complete_mertens_ledger hx).2.2
  have hprime_compare := CompleteMertensPeak.complete_mangoldt_le_neg_E3 hx
  dsimp only [B]
  linarith

private theorem DB_to_eventual_weightedTail (A : ℝ)
    (hDB : ∀ᶠ x : ℝ in atTop, -A ≤ D x * B x) :
    ∀ᶠ x : ℝ in atTop,
      -A / (Real.sqrt x * Real.log x) ≤ weightedTail psiErrorKernel x := by
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_theta_gt_one, hDB]
    with x hx htheta hb
  have hD := D_pos (by linarith : 1 < x)
  have hdivide : -A / (Real.sqrt x * Real.log x) ≤ B x := by
    apply (div_le_iff₀ hD).mpr
    change -A ≤ B x * D x
    nlinarith [hb]
  exact hdivide.trans (B_le_weightedTail hx htheta)

/-- Exact public complete-tail identity followed by the defining algebra of U. -/
private lemma Q_eq_neg_U_div {x : ℝ} (hx : 2 ≤ x) : Q x = -U x / x := by
  have htail :=
    D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  change Q x = _ at htail
  rw [htail]
  dsimp only [U]
  field_simp [show x ≠ 0 by linarith]
  <;> ring

/-- The closed-tail premise of the inverse is obtained from a single eventual
threshold.  k-L1 comes from the public ledger, with no boundary moment or v-L1. -/
private theorem weightedTail_to_eventual_U (A : ℝ) (hA : 0 ≤ A)
    (hweighted : ∀ᶠ x : ℝ in atTop,
      -A / (Real.sqrt x * Real.log x) ≤ weightedTail psiErrorKernel x) :
    ∀ᶠ x : ℝ in atTop, U x ≤ 3 * A * Real.sqrt x := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hweighted
  filter_upwards [eventually_ge_atTop (max (max T 2) (Real.exp 1))] with x hx
  have hTx : T ≤ x := (le_max_left T 2).trans ((le_max_left _ _).trans hx)
  have hx2 : 2 ≤ x := (le_max_right T 2).trans ((le_max_left _ _).trans hx)
  have hxE : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hk : IntegrableOn psiErrorKernel (Ioi x) :=
    (CompleteMertensPeak.complete_mertens_ledger hx2).1
  have hclosed : ∀ t : ℝ, x ≤ t →
      -A / (Real.sqrt t * Real.log t) ≤ weightedTail psiErrorKernel t := by
    intro t ht
    exact hT t (hTx.trans ht)
  have hQ : -3 * A / Real.sqrt x ≤ Q x := by
    simpa only [tail, Q] using
      D5.S3.Weil.Mertens.WeightedTailInverse.tail_lower_bound hxE hA hk hclosed
  have hscaled := (div_le_iff₀ hs).mp hQ
  have hneg : -(Q x * Real.sqrt x) ≤ 3 * A := by linarith
  have hu := mul_le_mul_of_nonneg_right hneg hs.le
  have hid : -(Q x * Real.sqrt x) * Real.sqrt x = U x := by
    calc
      _ = -Q x * (Real.sqrt x * Real.sqrt x) := by ring
      _ = -Q x * x := by rw [Real.mul_self_sqrt hx0.le]
      _ = U x := by
        rw [Q_eq_neg_U_div hx2]
        field_simp [hx0.ne']
        <;> ring
  rwa [hid] at hu

/-- The literal full-spectrum kernel is bounded above on a real tail.
The constant/trivial-zero correction is retained with its correct sign. -/
private theorem U_to_eventual_K (A : ℝ)
    (hU : ∀ᶠ x : ℝ in atTop, U x ≤ 3 * A * Real.sqrt x) :
    ∀ᶠ y : ℝ in atTop,
      D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K y ≤ 3 * A + 1 := by
  have hUexp : ∀ᶠ y : ℝ in atTop,
      U (Real.exp y) ≤ 3 * A * Real.sqrt (Real.exp y) :=
    Real.tendsto_exp_atTop.eventually hU
  filter_upwards [eventually_ge_atTop (0 : ℝ), hUexp] with y hy hu
  have hsqrt : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hexpsqrt : Real.exp (-y / 2) * Real.sqrt (Real.exp y) = 1 := by
    rw [hsqrt, ← Real.exp_add, show -y / 2 + y / 2 = 0 by ring, Real.exp_zero]
  have hu_scaled : Real.exp (-y / 2) * U (Real.exp y) ≤ 3 * A := by
    calc
      _ ≤ Real.exp (-y / 2) * (3 * A * Real.sqrt (Real.exp y)) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
      _ = (3 * A) * (Real.exp (-y / 2) * Real.sqrt (Real.exp y)) := by ring
      _ = 3 * A := by rw [hexpsqrt, mul_one]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpi : 0 < Real.log (2 * Real.pi) :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have hcorr : trivialT y - Real.log (2 * Real.pi) ≤ 1 := by
    linarith [trivialT_le_mass hy]
  have hexp_le : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcorr_scaled :
      Real.exp (-y / 2) * (trivialT y - Real.log (2 * Real.pi)) ≤ 1 := by
    calc
      _ ≤ Real.exp (-y / 2) * 1 := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
      _ ≤ 1 := by simpa only [mul_one] using hexp_le
  rw [D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K,
    abs_of_nonneg hy]
  nlinarith [hu_scaled, hcorr_scaled]

/-- An eventual one-sided normalized lower bound for original integer records
at every positive price is equivalent to RH. -/
theorem original_record_lower_bound_iff_rh :
    (∃ M T : ℝ, 2 ≤ T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      -M ≤ D (largestPrime m : ℝ) * robinLogMargin m) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨M, T, _hT, hbound⟩
    obtain ⟨A, hA, hDB⟩ := records_to_eventual_DB M T hbound
    have hweighted := DB_to_eventual_weightedTail A hDB
    have hU := weightedTail_to_eventual_U A hA hweighted
    obtain ⟨Ty, hTy⟩ := eventually_atTop.mp (U_to_eventual_K A hU)
    apply D5.S3.Weil.Mertens.IntegratedExplicit.actual_kernel_affine_tail_implies_rh
      (max Ty 1) 0 (3 * A + 1) (by have hh := le_max_right Ty (1 : ℝ); linarith)
    intro y hy
    simpa only [zero_mul, zero_add] using hTy y ((le_max_left Ty 1).trans hy)
  · intro hRH
    obtain ⟨T, hT, hendpoint⟩ :=
      (RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint hRH).1 1 zero_lt_one
    refine ⟨max 0 (1 - RHSharpOriginalRecordMargin.K), T, hT, ?_⟩
    intro m hm lambda hlambda hrecord hlarge
    have hh := hendpoint m hm lambda hlambda hrecord hlarge
    have hmax : 1 - RHSharpOriginalRecordMargin.K ≤ max 0 (1 - RHSharpOriginalRecordMargin.K) :=
      le_max_right _ _
    linarith

#print axioms original_record_lower_bound_iff_rh

end D5.S3.Arith.Robin.PriceRecord.OriginalRecordLowerBoundCriterion
