/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicHilbertHolomorphy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicHilbertHolomorphy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular vector series extend the original normalized TT and UT coefficients through zero on the full disk norm z less than beta b. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticLaurentBridge
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Asymptotics.Defs

/-!
UNCOMPILED proof candidate. No native/kernel acceptance is asserted.

The coefficients below are the literal coefficients of cubicTTSeries and
cubicUTSeries. The imported double-contour theorem identifies them with
the actual annular contour coefficients. No inverse operator is used to
define either extension.

For s = n+1, d = s+k+delta, the normalized monomial is
  z^(1+2*delta) * (coefficient / sqrt(s)) * z^(n+2*k).
Here delta=1 for TT and delta=0 for UT. The two fixed contour radii can
be chosen once on ANY strict closed disk of the ORIGINAL z domain:
  R < r < beta,  r*R < eta < r*beta.
Then R^2 < eta and both geometric ratios r*R/eta, R^2/eta are < 1.
This proves normal convergence even for the FACTORED series p/z^3, q/z.
All square roots of indices remain positive real square roots.

The parameter b and either external root are fixed in this file. Joint
holomorphy as b varies along a local root graph is a separate endpoint.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Metric Set

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicHilbertHolomorphy

open OriginalGaussianCubicKernel OriginalGaussianCubicAnalytic
open OriginalGaussianCubicAnalyticLaurentBridge OriginalGaussianResolvent

private def offset (same : Bool) : ℕ := if same then 1 else 0

private def coefficient (same : Bool) (b root : ℂ) (s d : ℕ) : ℂ :=
  if same then negativeCoefficient (cubicTTSeries b root) s d
  else negativeCoefficient (cubicUTSeries b root) s d

private lemma coefficient_support {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (s d : ℕ) (hd : d < s + offset same) :
    coefficient same b root s d = 0 := by
  cases same with
  | false =>
      exact cubic_ut_pole_bound b root hb s d (by simpa [offset] using hd)
  | true =>
      apply cubic_tt_pole_bound b root hb s d
      have hlt : d < s + 1 := by simpa [offset] using hd
      omega

private lemma sqrt_norm_ge_one (n : ℕ) :
    1 ≤ ‖(Real.sqrt (n + 1 : ℝ) : ℂ)‖ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using
    (Real.one_le_sqrt.mpr (by positivity : (1 : ℝ) ≤ n + 1))

private lemma sqrt_ne_zero (n : ℕ) :
    (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (sqrt_norm_ge_one n))

/-- Each term is a genuine vector in the original lp carrier. The two
indices range over all modes and all remaining modulus degrees. -/
def regularTerm (same : Bool) (b root : ℂ) (nk : ℕ × ℕ) (z : ℂ) :
    OriginalGaussianResolvent.H :=
  lp.single 2 nk.1
    (coefficient same b root (nk.1 + 1) (nk.1 + 1 + nk.2 + offset same) /
      (Real.sqrt (nk.1 + 1 : ℝ) : ℂ) * z ^ (nk.1 + 2 * nk.2))

/-- The factored series; it is defined by the actual cubic coefficients. -/
def regularSeries (same : Bool) (b root z : ℂ) : OriginalGaussianResolvent.H :=
  ∑' nk : ℕ × ℕ, regularTerm same b root nk z

/-- The original p extension, with its cubic factor explicit. -/
def pSeries (b root z : ℂ) : OriginalGaussianResolvent.H :=
  z ^ 3 • regularSeries true b root z

/-- The original q extension, with its linear factor explicit. -/
def qSeries (b root z : ℂ) : OriginalGaussianResolvent.H :=
  z • regularSeries false b root z

private lemma fixed_radii {b : ℂ} {R : ℝ} (hR : 0 ≤ R) (hRb : R < beta b) :
    ∃ r eta : ℝ, 0 < r ∧ r < beta b ∧ 0 < eta ∧ eta < r * beta b ∧
      r * R < eta ∧ R ^ 2 < eta := by
  obtain ⟨r, hRr, hrb⟩ := exists_between hRb
  have hr : 0 < r := hR.trans_lt hRr
  obtain ⟨eta, hre, heb⟩ := exists_between (mul_lt_mul_of_pos_left hRb hr)
  refine ⟨r, eta, hr, hrb, ?_, heb, hre, ?_⟩
  · exact (mul_nonneg hr.le hR).trans_lt hre
  · have hsq : R ^ 2 ≤ r * R := by nlinarith
    exact hsq.trans_lt hre

private lemma coefficient_majorant {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ same : Bool, ∀ s d : ℕ,
      ‖coefficient same b root s d‖ ≤ M * r ^ (s + 1) / eta ^ d := by
  obtain ⟨⟨M, hM, hbound⟩, _, _⟩ :=
    original_formal_coefficients_bounds (x := 0) hb root 0 hr hrb heta hetab
      (by simpa using heta)
  refine ⟨M, hM, ?_⟩
  intro same s d
  cases same with
  | false => exact (hbound s d).2
  | true => exact (hbound s d).1

private lemma term_bound {b root : ℂ} (same : Bool) {r eta R M : ℝ}
    (hr : 0 ≤ r) (heta : 0 < eta) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hc : ∀ s d : ℕ, ‖coefficient same b root s d‖ ≤
      M * r ^ (s + 1) / eta ^ d) (z : ℂ) (hz : ‖z‖ ≤ R) (nk : ℕ × ℕ) :
    ‖regularTerm same b root nk z‖ ≤
      (M * r ^ 2 / eta ^ (1 + offset same)) *
        ((r * R / eta) ^ nk.1 * (R ^ 2 / eta) ^ nk.2) := by
  rw [regularTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_mul, norm_div, norm_pow]
  calc
    _ ≤ ‖coefficient same b root (nk.1 + 1)
          (nk.1 + 1 + nk.2 + offset same)‖ * R ^ (nk.1 + 2 * nk.2) := by
      apply mul_le_mul
      · exact div_le_self (norm_nonneg _) (sqrt_norm_ge_one nk.1)
      · exact pow_le_pow_left₀ (norm_nonneg z) hz _
      · positivity
      · positivity
    _ ≤ (M * r ^ (nk.1 + 1 + 1) / eta ^
          (nk.1 + 1 + nk.2 + offset same)) * R ^ (nk.1 + 2 * nk.2) := by
      exact mul_le_mul_of_nonneg_right (hc _ _) (pow_nonneg hR _)
    _ = _ := by
      simp only [pow_add, pow_mul, mul_pow, div_pow, div_eq_mul_inv, mul_inv_rev]
      ring

/-- An actual summable H-norm majorant, uniform on every strict closed
disk in norm z < beta(b), including disks containing zero. -/
theorem regular_normal_convergence {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) {R : ℝ} (hR : 0 ≤ R) (hRb : R < beta b) :
    ∃ u : ℕ × ℕ → ℝ, Summable u ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ nk : ℕ × ℕ,
      ‖regularTerm same b root nk z‖ ≤ u nk := by
  obtain ⟨r, eta, hr, hrb, heta, hetab, hrRe, hR2e⟩ := fixed_radii hR hRb
  obtain ⟨M, hM, hc⟩ := coefficient_majorant hb root hr hrb heta hetab
  let a := r * R / eta
  let v := R ^ 2 / eta
  have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hr.le hR) heta.le
  have ha1 : a < 1 := (div_lt_one heta).mpr hrRe
  have hv0 : 0 ≤ v := div_nonneg (sq_nonneg R) heta.le
  have hv1 : v < 1 := (div_lt_one heta).mpr hR2e
  let C := M * r ^ 2 / eta ^ (1 + offset same)
  refine ⟨fun nk => C * (a ^ nk.1 * v ^ nk.2), ?_, ?_⟩
  · exact ((summable_geometric_of_lt_one ha0 ha1).mul_of_nonneg
      (summable_geometric_of_lt_one hv0 hv1)
      (fun n => pow_nonneg ha0 n) (fun k => pow_nonneg hv0 k)).mul_left C
  · intro z hz nk
    exact term_bound same hr.le heta hR hM (hc same) z hz nk

private lemma regular_summable {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) :
    Summable (fun nk : ℕ × ℕ => regularTerm same b root nk z) := by
  obtain ⟨u, hu, hbound⟩ := regular_normal_convergence hb root same (norm_nonneg z) hz
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun nk => hbound z le_rfl nk) hu).of_norm

private lemma term_differentiable (same : Bool) (b root : ℂ) (nk : ℕ × ℕ)
    (S : Set ℂ) : DifferentiableOn ℂ (regularTerm same b root nk) S := by
  intro z _
  have hc : DifferentiableAt ℂ (fun w : ℂ =>
      coefficient same b root (nk.1 + 1) (nk.1 + 1 + nk.2 + offset same) /
        (Real.sqrt (nk.1 + 1 : ℝ) : ℂ) * w ^ (nk.1 + 2 * nk.2)) z := by
    fun_prop
  exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 nk.1).differentiableAt.comp
    z hc).differentiableWithinAt

/-- Both holomorphy and exchange with the infinite derivative series
follow from the same normal majorant; no derivative summability premise
is assumed. -/
theorem regular_holomorphy_and_derivative {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) :
    AnalyticAt ℂ (regularSeries same b root) z ∧
      HasSum (fun nk : ℕ × ℕ => deriv (regularTerm same b root nk) z)
        (deriv (regularSeries same b root) z) := by
  obtain ⟨R, hzR, hRb⟩ := exists_between hz
  have hR : 0 < R := (norm_nonneg z).trans_lt hzR
  obtain ⟨u, hu, hbound⟩ := regular_normal_convergence hb root same hR.le hRb
  have ht := fun nk => term_differentiable same b root nk (ball 0 R)
  have hle : ∀ nk : ℕ × ℕ, ∀ w : ℂ, w ∈ ball (0 : ℂ) R →
      ‖regularTerm same b root nk w‖ ≤ u nk := by
    intro nk w hw
    exact hbound w (le_of_lt (by simpa using hw)) nk
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu ht isOpen_ball hle
  have hzmem : z ∈ ball (0 : ℂ) R := by simpa using hzR
  exact ⟨hd.analyticAt (isOpen_ball.mem_nhds hzmem),
    Complex.hasSum_deriv_of_summable_norm hu ht isOpen_ball hle hzmem⟩

/-- The full Hilbert series is the uniform limit of its finite sums on
each closed disk. The radius and the contour constants are fixed. -/
theorem regular_uniform_limit {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) {R : ℝ} (hR : 0 ≤ R) (hRb : R < beta b) :
    TendstoUniformlyOn
      (fun F : Finset (ℕ × ℕ) => fun z : ℂ => ∑ nk ∈ F, regularTerm same b root nk z)
      (regularSeries same b root) atTop (closedBall (0 : ℂ) R) := by
  obtain ⟨u, hu, hbound⟩ := regular_normal_convergence hb root same hR hRb
  exact tendstoUniformlyOn_tsum hu (fun nk z hz => hbound z (by simpa using hz) nk)

private lemma regular_coordinate {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) (n : ℕ) :
    regularSeries same b root z n = ∑' k : ℕ,
      coefficient same b root (n + 1) (n + 1 + k + offset same) /
        (Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 2 * k) := by
  classical
  let E := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n
  have hs := regular_summable hb root same hz
  change E (∑' nk : ℕ × ℕ, regularTerm same b root nk z) = _
  rw [E.map_tsum hs]
  have he : Summable (fun nk : ℕ × ℕ => E (regularTerm same b root nk z)) :=
    E.summable hs
  rw [he.tsum_prod]
  calc
    _ = ∑' k : ℕ, E (regularTerm same b root (n, k) z) := by
      apply tsum_eq_single n
      intro m hm
      apply tsum_eq_zero
      intro k
      change (regularTerm same b root (m, k) z) n = 0
      exact lp.single_apply_ne 2 m _ (Ne.symm hm)
    _ = _ := by
      apply tsum_congr
      intro k
      exact lp.single_apply_self 2 n _

private lemma normalized_monomial (z c : ℂ) (hz : z ≠ 0) (n k delta : ℕ) :
    z ^ (1 + 2 * delta) *
        (c / (Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 2 * k)) =
      c * (z ^ 2) ^ (k + (n + 1 + delta)) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1)) := by
  have hden := mul_ne_zero (sqrt_ne_zero n) (pow_ne_zero _ hz)
  apply (eq_div_iff hden).mpr
  have hpow : z ^ (1 + 2 * delta) * z ^ (n + 2 * k) * z ^ (n + 1) =
      (z ^ 2) ^ (k + (n + 1 + delta)) := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    congr 1
    omega
  calc
    _ = c * (z ^ (1 + 2 * delta) * z ^ (n + 2 * k) * z ^ (n + 1)) := by
      field_simp [sqrt_ne_zero n]
      <;> ring
    _ = _ := by rw [hpow]

private lemma actual_hasSum {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) (s : ℕ) :
    HasSum (fun d : ℕ => coefficient same b root s d * (z ^ 2) ^ d)
      (if same then Tcoeff b root s (z ^ 2) else Ucoeff b root s (z ^ 2)) := by
  have hbeta : 0 < beta b := lt_min (by norm_num) (norm_pos_iff.mpr hb)
  have hx : ‖z ^ 2‖ < beta b ^ 2 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have h := original_formal_coefficients_hasSum_disk hb root s hx
  cases same with
  | false => exact h.2
  | true => exact h.1

private lemma actual_tail_hasSum {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) (s : ℕ) :
    HasSum (fun k : ℕ => coefficient same b root s (k + (s + offset same)) *
        (z ^ 2) ^ (k + (s + offset same)))
      (if same then Tcoeff b root s (z ^ 2) else Ucoeff b root s (z ^ 2)) := by
  have hzero : (∑ d ∈ Finset.range (s + offset same),
      coefficient same b root s d * (z ^ 2) ^ d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [coefficient_support hb root same s d (Finset.mem_range.mp hd), zero_mul]
  have h := (hasSum_nat_add_iff' (s + offset same)).mpr (actual_hasSum hb root same hz s)
  simpa only [hzero, sub_zero] using h

/-- Coordinate agreement is obtained by a supported convergent Taylor
tail of the ACTUAL annular coefficient. Division is used only for z != 0. -/
private lemma extension_coordinate {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) (hz : ‖z‖ < beta b) (hz0 : z ≠ 0) (n : ℕ) :
    (z ^ (1 + 2 * offset same) • regularSeries same b root z) n =
      (if same then pValue b root z n else qValue b root z n) := by
  have htail := (actual_tail_hasSum hb root same hz (n + 1)).div_const
    ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))
  have hterm (k : ℕ) :
      z ^ (1 + 2 * offset same) *
        (coefficient same b root (n + 1) (n + 1 + k + offset same) /
          (Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 2 * k)) =
      coefficient same b root (n + 1) (k + (n + 1 + offset same)) *
        (z ^ 2) ^ (k + (n + 1 + offset same)) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1)) := by
    rw [show n + 1 + k + offset same = k + (n + 1 + offset same) by omega]
    exact normalized_monomial z
      (coefficient same b root (n + 1) (k + (n + 1 + offset same)))
      hz0 n k (offset same)
  change z ^ (1 + 2 * offset same) * regularSeries same b root z n = _
  rw [regular_coordinate hb root same hz n, ← tsum_mul_left]
  simp_rw [hterm]
  have he := htail.tsum_eq
  cases same with
  | false => simpa [qValue] using he
  | true => simpa [pValue] using he

theorem pSeries_zero (b root : ℂ) : pSeries b root 0 = 0 := by
  simp [pSeries]

theorem qSeries_zero (b root : ℂ) : qSeries b root 0 = 0 := by
  simp [qSeries]

/-- Coordinatewise equality on the whole original disk, also at zero.
The assigned zero is the value of the convergent H-valued extension. -/
theorem original_coordinates {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hz : ‖z‖ < beta b) :
    (∀ n : ℕ, pSeries b root z n = pValue b root z n) ∧
      (∀ n : ℕ, qSeries b root z n = qValue b root z n) := by
  by_cases hz0 : z = 0
  · subst z
    simp [pSeries_zero, qSeries_zero, pValue, qValue]
  · constructor
    · intro n
      simpa [pSeries, offset] using extension_coordinate hb root true hz hz0 n
    · intro n
      simpa [qSeries, offset] using extension_coordinate hb root false hz hz0 n

/-- H-valued analytic extensions throughout the FULL original z disk.
No recurrence, continuity, analyticity, or correspondence is a premise. -/
theorem original_hilbert_analytic {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hz : ‖z‖ < beta b) :
    AnalyticAt ℂ (pSeries b root) z ∧ AnalyticAt ℂ (qSeries b root) z ∧
      AnalyticAt ℂ (eSeries b root) z := by
  have hdP : DifferentiableOn ℂ (pSeries b root) (ball 0 (beta b)) := by
    intro w hw
    have hreg := (regular_holomorphy_and_derivative hb root true (by simpa using hw)).1
    exact ((differentiableAt_id.pow 3).smul hreg.differentiableAt).differentiableWithinAt
  have hdQ : DifferentiableOn ℂ (qSeries b root) (ball 0 (beta b)) := by
    intro w hw
    have hreg := (regular_holomorphy_and_derivative hb root false (by simpa using hw)).1
    exact (differentiableAt_id.smul hreg.differentiableAt).differentiableWithinAt
  have hzmem : z ∈ ball (0 : ℂ) (beta b) := by simpa using hz
  exact ⟨hdP.analyticAt (isOpen_ball.mem_nhds hzmem),
    hdQ.analyticAt (isOpen_ball.mem_nhds hzmem), (external_row_analytic root hz).1⟩

private lemma factored_norm_bound {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    (same : Bool) {R : ℝ} (hR : 0 ≤ R) (hRb : R < beta b) :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖z ^ (1 + 2 * offset same) • regularSeries same b root z‖ ≤
        C * ‖z ^ (1 + 2 * offset same)‖ := by
  obtain ⟨u, hu, hbound⟩ := regular_normal_convergence hb root same hR hRb
  refine ⟨∑' nk : ℕ × ℕ, u nk, ?_⟩
  intro z hz
  have hs : ‖regularSeries same b root z‖ ≤ ∑' nk : ℕ × ℕ, u nk :=
    tsum_of_norm_bounded hu.hasSum (fun nk => hbound z hz nk)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)

/-- Genuine H-norm orders at zero, with constants from the normally
convergent double series, rather than coordinatewise O estimates. -/
theorem original_vanishing_orders {b : ℂ} (hb : b ≠ 0) (root : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (pSeries b root) (fun z : ℂ => z ^ 3) ∧
      Asymptotics.IsBigO (𝓝 (0 : ℂ)) (qSeries b root) (fun z : ℂ => z) ∧
      Asymptotics.IsBigO (𝓝 (0 : ℂ)) (eSeries b root) (fun z : ℂ => z) := by
  have hbeta : 0 < beta b := lt_min (by norm_num) (norm_pos_iff.mpr hb)
  obtain ⟨R, hR, hRb⟩ := exists_between hbeta
  obtain ⟨CP, hP⟩ := factored_norm_bound hb root true hR.le hRb
  obtain ⟨CQ, hQ⟩ := factored_norm_bound hb root false hR.le hRb
  have hball : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ≤ R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
    exact le_of_lt (by simpa using hz)
  refine ⟨Asymptotics.IsBigO.of_bound CP ?_, Asymptotics.IsBigO.of_bound CQ ?_,
    eSeries_first_order hb root⟩
  · filter_upwards [hball] with z hz
    simpa [pSeries, offset] using hP z hz
  · filter_upwards [hball] with z hz
    simpa [qSeries, offset] using hQ z hz

/-- Normal convergence and actual HasSum values for ALL THREE original
vector functions, uniformly on any strict closed disk. In particular,
the p/q sums here are the normalized supported coefficient expansions,
with their scalar factors restored, rather than resolvent definitions. -/
theorem original_normal_convergence {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hRb : R < beta b) :
    ∃ uP uQ : ℕ × ℕ → ℝ, ∃ uE : ℕ → ℝ,
      Summable uP ∧ Summable uQ ∧ Summable uE ∧
      (∀ z : ℂ, ‖z‖ ≤ R →
        (∀ nk : ℕ × ℕ, ‖z ^ 3 • regularTerm true b root nk z‖ ≤ uP nk) ∧
        (∀ nk : ℕ × ℕ, ‖z • regularTerm false b root nk z‖ ≤ uQ nk) ∧
        (∀ n : ℕ, ‖(lp.single 2 n (eValue b root z n) :
          OriginalGaussianResolvent.H)‖ ≤ uE n) ∧
        HasSum (fun nk : ℕ × ℕ => z ^ 3 • regularTerm true b root nk z)
          (pSeries b root z) ∧
        HasSum (fun nk : ℕ × ℕ => z • regularTerm false b root nk z)
          (qSeries b root z) ∧
        HasSum (fun n : ℕ => (lp.single 2 n (eValue b root z n) :
          OriginalGaussianResolvent.H)) (eSeries b root z)) := by
  obtain ⟨uP, hP, hPb⟩ := regular_normal_convergence hb root true hR hRb
  obtain ⟨uQ, hQ, hQb⟩ := regular_normal_convergence hb root false hR hRb
  obtain ⟨uE, hE, hEb⟩ := external_normal_convergence root hR hRb
  refine ⟨fun nk => R ^ 3 * uP nk, fun nk => R * uQ nk, uE,
    hP.mul_left (R ^ 3), hQ.mul_left R, hE, ?_⟩
  intro z hz
  have hzb : ‖z‖ < beta b := hz.trans_lt hRb
  have he : Summable (fun n : ℕ => (lp.single 2 n (eValue b root z n) :
      OriginalGaussianResolvent.H)) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hEb z hz n) hE).of_norm
  refine ⟨?_, ?_, hEb z hz, ?_, ?_, he.hasSum⟩
  · intro nk
    rw [norm_smul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz 3)
      (hPb z hz nk) (norm_nonneg _) (pow_nonneg hR 3)
  · intro nk
    rw [norm_smul]
    exact mul_le_mul hz (hQb z hz nk) (norm_nonneg _) hR
  · exact (regular_summable hb root true hzb).hasSum.const_smul (z ^ 3)
  · exact (regular_summable hb root false hzb).hasSum.const_smul z

/-- The already evaluated signed sewing bridge is applied to the actual
series only AFTER coordinate equality has been established. At zero the
maps act on the actual zero vector. mixedOperator retains its -I term. -/
theorem original_extensions_correspondence {b z : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hroot : (1 + b) * root ^ 2 = 1) (hz : ‖z‖ < beta b) :
    pSeries b root z = selfOperator z (eSeries b root z) ∧
      qSeries b root z = mixedOperator z (eSeries b root z) := by
  by_cases hz0 : z = 0
  · subst z
    simp only [pSeries_zero, qSeries_zero, eSeries_zero, map_zero, and_self]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let p : OriginalGaussianResolvent.H :=
      ⟨pValue b root z, (normalized_coefficients_mem root hpos hz).2.2.1⟩
    let q : OriginalGaussianResolvent.H :=
      ⟨qValue b root z, (normalized_coefficients_mem root hpos hz).2.2.2⟩
    have hp : pSeries b root z = p := by
      ext n
      exact (original_coordinates hb root hz).1 n
    have hq : qSeries b root z = q := by
      ext n
      exact (original_coordinates hb root hz).2 n
    have he : eSeries b root z = eVector b root z hz := by
      ext n
      exact (external_row_analytic root hz).2 n
    rw [hp, hq, he]
    exact original_hilbert_correspondence root hroot hpos hz

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicHilbertHolomorphy
