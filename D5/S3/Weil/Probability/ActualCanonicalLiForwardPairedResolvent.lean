/- GID: D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual zero pairs give the canonical Li coefficients and their quadratic envelope. -/

import D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import D5.S3.Weil.ZeroData.LiZeroSumConvergence
import D5.S3.Weil.Probability.CanonicalLiDiskEquivalence
import D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
import D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! The multiplicity-weighted positive-zero pairs give the derivative-normalized
Li coefficients under right-half-plane nonvanishing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent

open Complex Filter
open scoped Topology BigOperators NNReal ENNReal ComplexConjugate
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Weil.ZeroData.LiZeroSumConvergence
open D5.S3.Weil.Probability.CanonicalLiDiskEquivalence
open D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse
open D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
open D5.S3.Weil.Probability.AnalyticLogarithmicContinuation

private abbrev Z := zetaZeroData
private abbrev rho (i : ℕ) : ℂ := Z.zero i
private abbrev mass (i : ℕ) : ℝ := Z.multiplicity i
private abbrev gamma (i : ℕ) : ℂ := Z.gamma i

/-- Actual Cayley ratio of each genuine nontrivial zero. -/
def zeroRatio (i : ℕ) : ℂ := 1 - 1 / rho i

/-- Whole actual positive-indexed pair contribution, with the exact analytic
multiplicity. Negative ordinates are zero in this paired presentation. -/
def pairCoefficient (n i : ℕ) : ℝ :=
  if 0 < (gamma i).re then 2 * mass i * (1 - ((zeroRatio i)^n).re) else 0

private theorem zero_nonzero (i : ℕ) : rho i ≠ 0 := by
  intro h
  have hpos := (zetaZeroData_isNontrivial i).2.1
  change 0 < (rho i).re at hpos
  rw [h] at hpos
  simp at hpos

private theorem zero_ne_one (i : ℕ) : rho i ≠ 1 := by
  intro h
  have hlt := (zetaZeroData_isNontrivial i).2.2
  change (rho i).re < 1 at hlt
  rw [h] at hlt
  simp at hlt

private theorem zero_on_line (hRH : RiemannHypothesis) (i : ℕ) :
    (rho i).re = (1 : ℝ)/2 :=
  rh_iff_nontrivial_zeros_on_line.mp hRH _ (zetaZeroData_isNontrivial i)

private theorem zeroRatio_unit (hRH : RiemannHypothesis) (i : ℕ) :
    ‖zeroRatio i‖ = 1 :=
  rh_iff_nontrivial_zero_cayley_norm.mp hRH _ (zetaZeroData_isNontrivial i)

private theorem zero_conj_eq (hRH : RiemannHypothesis) (i : ℕ) :
    conj (rho i) = 1 - rho i := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
    linarith [zero_on_line hRH i]
  · simp

private theorem norm_one_sub_pow_sq (a : ℂ) (ha : ‖a‖ = 1) (n : ℕ) :
    ‖1 - a^n‖^2 = 2 * (1 - (a^n).re) := by
  have hp : Complex.normSq (a^n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, ha, one_pow, one_pow]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im] at hp ⊢
  nlinarith

private theorem norm_one_sub_pow_le (a : ℂ) (ha : ‖a‖ = 1) (n : ℕ) :
    ‖1-a^n‖ ≤ (n : ℝ) * ‖1-a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : 1-a^(n+1) = (1-a^n)+a^n*(1-a) := by rw [pow_succ]; ring
    rw [heq]
    calc
      _ ≤ ‖1-a^n‖ + ‖a^n*(1-a)‖ := norm_add_le _ _
      _ ≤ (n : ℝ)*‖1-a‖+‖1-a‖ := by
        rw [norm_mul, norm_pow, ha, one_pow, one_mul]
        exact add_le_add_left ih _
      _ = ((n+1 : ℕ) : ℝ)*‖1-a‖ := by push_cast; ring

private theorem pairCoefficient_summable (n : ℕ) :
    Summable (pairCoefficient n) := by
  classical
  have hs := ((li_zero_real_summable Z n).mul_left 2).indicator {i : ℕ | 0 < (gamma i).re}
  apply hs.congr
  intro i
  by_cases hi : 0 < (gamma i).re
  · simp [pairCoefficient, zeroRatio, Set.indicator, hi, mul_assoc]
  · simp [pairCoefficient, Set.indicator, hi]

/-- The actual pair contributions are absolutely summable for every degree. -/
theorem pairCoefficient_abs_summable (n : ℕ) :
    Summable (fun i : ℕ => |pairCoefficient n i|) :=
  (pairCoefficient_summable n).abs

private theorem pairCoefficient_nonneg_and_bound (hRH : RiemannHypothesis) (n i : ℕ) :
    0 ≤ pairCoefficient n i ∧
      pairCoefficient n i ≤ (n : ℝ)^2 * pairCoefficient 1 i := by
  classical
  by_cases hi : 0 < (gamma i).re
  · have hm : 0 ≤ mass i := Nat.cast_nonneg _
    have hunit := zeroRatio_unit hRH i
    have hrepr (k : ℕ) : pairCoefficient k i = mass i * ‖1-(zeroRatio i)^k‖^2 := by
      rw [pairCoefficient, ite_eq_left hi, norm_one_sub_pow_sq _ hunit]
      ring
    rw [hrepr n, hrepr 1, pow_one]
    constructor
    · positivity
    · have hnorm := norm_one_sub_pow_le (zeroRatio i) hunit n
      have hs : ‖1-(zeroRatio i)^n‖^2 ≤ ((n : ℝ)*‖1-zeroRatio i‖)^2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      calc
        _ ≤ mass i * ((n : ℝ)*‖1-zeroRatio i‖)^2 := mul_le_mul_of_nonneg_left hs hm
        _ = _ := by ring
  · simp [pairCoefficient, hi]

/-- Coefficients of the actual positive-pair expansion. -/
def pairSum (n : ℕ) : ℝ := ∑' i : ℕ, pairCoefficient n i

private theorem pairSum_nonneg_and_bound (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ pairSum n ∧ pairSum n ≤ (n : ℝ)^2 * pairSum 1 := by
  constructor
  · exact tsum_nonneg fun i => (pairCoefficient_nonneg_and_bound hRH n i).1
  · unfold pairSum
    rw [← tsum_mul_left]
    exact (pairCoefficient_abs_summable n).of_abs.tsum_le_tsum
      (fun i => (pairCoefficient_nonneg_and_bound hRH n i).2)
      ((pairCoefficient_summable 1).mul_left _)

private theorem xi_center_ne : xiReading (1/2 : ℂ) ≠ 0 := by
  have hp := D5.S3.Analytic.Fourier.XiThetaTransform.source_theta_normalized.2.1
  intro hz
  have hr := congrArg Complex.re hz
  simp only [Complex.zero_re] at hr
  linarith

/-- Paired logarithmic derivative from the already proved actual square resolvent. -/
private theorem actual_pair_logDeriv_hasSum
    (halfFree : ∀ s : ℂ, (1 : ℝ)/2 < s.re → xiReading s ≠ 0)
    (hRH : RiemannHypothesis) (s : ℂ) (hs : (1 : ℝ)/2 < s.re) :
    HasSum (fun i : ℕ => if 0 < (gamma i).re then
      (Z.multiplicity i : ℂ) * (1/(s-rho i)+1/(s-conj (rho i))) else 0)
      (logDeriv xiReading s) := by
  classical
  let w : ℂ := -Complex.I*(s-1/2)
  have hw0 : w ≠ 0 := by
    intro he
    have hsz : s-(1/2 : ℂ) ≠ 0 := by
      intro he'; have h := congrArg Complex.re (sub_eq_zero.mp he')
      norm_num at h; linarith
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hsz he
  have hcoord : (1/2 : ℂ)+Complex.I*w=s := by
    dsimp [w]
    ring_nf
    norm_num [Complex.I_sq]
  have hF : xiSquareSource (w^2) ≠ 0 := by
    rw [xi_square_source_entire_and_composition.2, hcoord]
    exact div_ne_zero (halfFree s hs) xi_center_ne
  have ha := (actual_positive_square_resolvent_hasSum Z w hw0 hF).mul_left (-2*(s-1/2))
  have hv : -2*(s-1/2)*logDeriv xiSquareSource (w^2)=logDeriv xiReading s := by
    have hc := xi_square_logDeriv_composition w
    rw [hcoord] at hc
    calc
      _ = -Complex.I * (logDeriv xiSquareSource (w^2) * (2*w)) := by
        have hwfactor : -Complex.I*(2*w) = -2*(s-1/2) := by
          dsimp [w]
          ring_nf
          norm_num [Complex.I_sq]
          ring
        rw [show -Complex.I*(logDeriv xiSquareSource (w^2)*(2*w)) =
          (-Complex.I*(2*w))*logDeriv xiSquareSource (w^2) by ring, hwfactor]
      _ = _ := by rw [hc]; ring_nf; norm_num [Complex.I_sq]
  rw [hv] at ha
  apply ha.congr_fun
  intro i
  by_cases hi : 0 < (gamma i).re
  · simp only [positiveSquareResolvent, ite_eq_left hi]
    have hp0 : s-rho i ≠ 0 := by
      intro h; have hr := congrArg Complex.re (sub_eq_zero.mp h)
      linarith [zero_on_line hRH i]
    have hm0 : s-conj (rho i) ≠ 0 := by
      intro h; have hr := congrArg Complex.re (sub_eq_zero.mp h)
      simp only [Complex.conj_re] at hr
      linarith [zero_on_line hRH i]
    have hzero : rho i=(1/2 : ℂ)+Complex.I*gamma i := by
      simpa [D5.S3.Weil.Convention.criticalAbscissa] using Z.zero_eq_critical_add_I_mul_gamma i
    have hden : w^2-(gamma i)^2=-(s-rho i)*(s-conj (rho i)) := by
      rw [zero_conj_eq hRH i, hzero]
      dsimp [w]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    have hden0 : w^2-(gamma i)^2 ≠ 0 := by
      rw [hden]
      exact mul_ne_zero (neg_ne_zero.mpr hp0) hm0
    rw [hden]
    field_simp [hp0, hm0]
    rw [zero_conj_eq hRH i]
    ring
  · simp [positiveSquareResolvent, hi]

private theorem one_sub_ne_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1-z ≠ 0 := by
  intro h
  have he : z=1 := (sub_eq_zero.mp h).symm
  simp [he] at hz

/-- Literal geometric generating kernel of each actual positive zero pair. -/
private def pairKernel (z : ℂ) (i : ℕ) : ℂ :=
  if 0 < (gamma i).re then
    (Z.multiplicity i : ℂ) * (2*(1-z)⁻¹-
      zeroRatio i*(1-zeroRatio i*z)⁻¹-
      conj (zeroRatio i)*(1-conj (zeroRatio i)*z)⁻¹) else 0

private theorem single_resolvent_rational (r b z : ℂ)
    (hb : (1 - r) * (1 - b) = 1) (hr : 1 - r ≠ 0)
    (hz : 1 - z ≠ 0) (hd : 1 - b * z ≠ 0) :
    (1 - z)⁻¹ ^ 2 * (1 / ((1 - z)⁻¹ - r)) =
      (1 - z)⁻¹ - b * (1 - b * z)⁻¹ := by
  have he : (1 - z)⁻¹ - r = (1 - r) * (1 - b * z) / (1 - z) := by
    apply (eq_div_iff hz).mpr
    rw [sub_mul, inv_mul_cancel₀ hz]
    linear_combination -z * hb
  have hri : (1 - r)⁻¹ = 1 - b := by
    apply (mul_right_injective₀ hr)
    change (1 - r) * (1 - r)⁻¹ = (1 - r) * (1 - b)
    rw [mul_inv_cancel₀ hr, hb]
  rw [he, one_div, inv_div, div_eq_mul_inv, mul_inv_rev, hri]
  have hd' : 1 - z * b ≠ 0 := by simpa [mul_comm] using hd
  field_simp [hz, hd, hd'] <;> ring

private theorem single_pair_rational
    (hRH : RiemannHypothesis) (i : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z)⁻¹ ^ 2 * (1 / ((1 - z)⁻¹ - rho i) + 1 / ((1 - z)⁻¹ - conj (rho i))) =
      2 * (1 - z)⁻¹ - zeroRatio i * (1 - zeroRatio i * z)⁻¹ -
        conj (zeroRatio i) * (1 - conj (zeroRatio i) * z)⁻¹ := by
  have hunit := zeroRatio_unit hRH i
  have h0 := one_sub_ne_of_norm_lt_one hz
  have ha : ‖zeroRatio i * z‖ < 1 := by rwa [norm_mul, hunit, one_mul]
  have hb : ‖conj (zeroRatio i) * z‖ < 1 := by rwa [norm_mul, norm_conj, hunit, one_mul]
  have hconj : conj (zeroRatio i) = 1 - 1 / (1 - rho i) := by
    rw [zeroRatio, map_sub, map_one, map_div₀, map_one, zero_conj_eq hRH i]
  have hr : 1 - rho i ≠ 0 := sub_ne_zero.mpr (zero_ne_one i).symm
  have hc : 1 - conj (rho i) = rho i := by rw [zero_conj_eq hRH i]; ring
  have hA : (1 - conj (rho i)) * (1 - zeroRatio i) = 1 := by
    rw [hc, zeroRatio, sub_sub_cancel, div_eq_mul_inv, one_mul, mul_inv_cancel₀ (zero_nonzero i)]
  have hB : (1 - rho i) * (1 - conj (zeroRatio i)) = 1 := by
    rw [hconj, sub_sub_cancel, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hr]
  have hrc : 1 - conj (rho i) ≠ 0 := by rw [hc]; exact zero_nonzero i
  rw [mul_add, single_resolvent_rational _ _ _ hA hrc h0
      (one_sub_ne_of_norm_lt_one ha),
    single_resolvent_rational _ _ _ hB hr h0 (one_sub_ne_of_norm_lt_one hb)]
  ring

private theorem actual_pairKernel_hasSum
    (halfFree : ∀ s : ℂ, (1 : ℝ)/2 < s.re → xiReading s ≠ 0)
    (hRH : RiemannHypothesis) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (pairKernel z) (liGenerator z) := by
  classical
  have hhalf := disk_mobius_re_half z (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have h := (actual_pair_logDeriv_hasSum halfFree hRH ((1-z)⁻¹) hhalf).mul_left ((1-z)⁻¹^2)
  apply h.congr_fun
  intro i
  by_cases hi : 0 < (gamma i).re
  · simp only [ite_eq_left hi, pairKernel]
    rw [show (1-z)⁻¹^2*((Z.multiplicity i : ℂ)*(1/((1-z)⁻¹-rho i)+
          1/((1-z)⁻¹-conj (rho i)))) =
        (Z.multiplicity i : ℂ)*((1-z)⁻¹^2*(1/((1-z)⁻¹-rho i)+
          1/((1-z)⁻¹-conj (rho i)))) by ring, single_pair_rational hRH i z hz]
  · simp [pairKernel, hi]

private theorem pairCoefficient_cast (n i : ℕ) (hi : 0 < (gamma i).re) :
    (pairCoefficient n i : ℂ) = (Z.multiplicity i : ℂ) *
      (2-(zeroRatio i)^n-(conj (zeroRatio i))^n) := by
  rw [pairCoefficient, ite_eq_left hi]
  rw [← map_pow (starRingEnd ℂ)]
  apply Complex.ext <;>
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat,
      Complex.ofReal_one, Complex.ofReal_natCast, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im] <;> norm_num
  ring

private theorem pairKernel_geometric_hasSum (hRH : RiemannHypothesis)
    (z : ℂ) (hz : ‖z‖ < 1) (i : ℕ) :
    HasSum (fun n : ℕ => (pairCoefficient (n+1) i : ℂ)*z^n) (pairKernel z i) := by
  classical
  by_cases hi : 0 < (gamma i).re
  · have hunit := zeroRatio_unit hRH i
    have ha : ‖zeroRatio i*z‖<1 := by rwa [norm_mul,hunit,one_mul]
    have hb : ‖conj (zeroRatio i)*z‖<1 := by rwa [norm_mul,norm_conj,hunit,one_mul]
    have h0 := (hasSum_geometric_of_norm_lt_one hz).mul_left (2 : ℂ)
    have hA := (hasSum_geometric_of_norm_lt_one ha).mul_left (zeroRatio i)
    have hB := (hasSum_geometric_of_norm_lt_one hb).mul_left (conj (zeroRatio i))
    rw [pairKernel, ite_eq_left hi]
    apply (((h0.sub hA).sub hB).mul_left (Z.multiplicity i : ℂ)).congr_fun
    intro n
    simp only [pairCoefficient_cast _ _ hi, pow_succ, mul_pow]
    ring
  · simp [pairKernel, pairCoefficient, hi]

/-- Absolute product convergence of the actual pair/degree family. -/
private theorem pairDegree_product_summable (hRH : RiemannHypothesis)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖(pairCoefficient (p.2 + 1) p.1 : ℂ) * z ^ p.2‖) := by
  let g : ℕ → ℝ := fun n => ((n : ℝ)+1)^2 * ‖z‖^n
  have hr : ‖(‖z‖ : ℝ)‖<1 := by simpa using hz
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hg : Summable g := by
    apply ((h2.add (h1.mul_left 2)).add h0).congr
    intro n
    simp only [g, pow_one]
    ring
  have hn (i : ℕ) : 0 ≤ pairCoefficient 1 i :=
    (pairCoefficient_nonneg_and_bound hRH 1 i).1
  have hg0 (n : ℕ) : 0 ≤ g n := by dsimp [g]; positivity
  have hmajor := (pairCoefficient_summable 1).mul_of_nonneg hg hn hg0
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmajor
  intro p
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pairCoefficient_nonneg_and_bound hRH (p.2+1) p.1).1]
  calc
    _ ≤ ((p.2+1 : ℕ) : ℝ)^2 * pairCoefficient 1 p.1 * ‖z‖^p.2 :=
      mul_le_mul_of_nonneg_right
        (pairCoefficient_nonneg_and_bound hRH (p.2 + 1) p.1).2 (by positivity)
    _ = _ := by dsimp [g]; push_cast; ring

/-- Complete paired Taylor expansion on the entire actual unit disk. -/
private theorem actual_pairSum_global_expansion
    (halfFree : ∀ s : ℂ, (1 : ℝ)/2 < s.re → xiReading s ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (pairSum (n+1) : ℂ)*z^n) (liGenerator z) := by
  have hRH := rh_iff_xi_right_half_plane.mpr halfFree
  let f : ℕ×ℕ → ℂ := fun p => (pairCoefficient (p.2+1) p.1 : ℂ)*z^p.2
  have habs : Summable f := (pairDegree_product_summable hRH z hz).of_norm
  have hsum : (∑' i : ℕ, ∑' n : ℕ, f (i,n)) = liGenerator z := by
    calc
      _ = ∑' i : ℕ, pairKernel z i := by
        apply tsum_congr
        intro i
        exact (pairKernel_geometric_hasSum hRH z hz i).tsum_eq
      _ = _ := (actual_pairKernel_hasSum halfFree hRH z hz).tsum_eq
  have hswap : (∑' n : ℕ, ∑' i : ℕ, f (i,n)) = liGenerator z :=
    habs.tsum_comm.trans hsum
  have hs : Summable (fun n : ℕ => ∑' i : ℕ, f (i,n)) := habs.prod_symm.prod
  have hh := hs.hasSum
  rw [hswap] at hh
  apply hh.congr_fun
  intro n
  dsimp [f, pairSum]
  rw [tsum_mul_right, Complex.ofReal_tsum]

/-! Scalar formal-series coefficient uniqueness at the origin. -/
private theorem scalar_expansion_coefficients_unique
    (a b : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => a n*z^n) (F z))
    (hb : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => b n*z^n) (F z)) :
    a=b := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  let q : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ b
  let r : ℝ≥0 := 1/2
  have hr : ‖((r:ℝ):ℂ)‖<1 := by norm_num [r, Complex.norm_real]
  have hpRad : (r:ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable
    have hs := (ha ((r:ℝ):ℂ) hr).summable.norm
    simpa [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq] using hs
  have hqRad : (r:ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_summable
    have hs := (hb ((r:ℝ):ℂ) hr).summable.norm
    simpa [q, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq] using hs
  have hrpos : 0 < (r:ℝ≥0∞) := by norm_num [r]
  have hp := (p.hasFPowerSeriesOnBall (hrpos.trans_le hpRad)).hasFPowerSeriesAt
  have hq := (q.hasFPowerSeriesOnBall (hrpos.trans_le hqRad)).hasFPowerSeriesAt
  have he : ∀ᶠ z : ℂ in 𝓝 0, p.sum z = q.sum z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ)<1)] with z hz
    have hn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    simp only [p, q, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    exact (ha z hn).tsum_eq.trans (hb z hn).tsum_eq.symm
  have hpq := hp.eq_formalMultilinearSeries_of_eventually hq he
  funext n
  simpa [p, q, FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun t : FormalMultilinearSeries ℂ ℂ ℂ => t.coeff n) hpq

/-- The derivative-normalized coefficient equals the actual pair sum on the
zero-free half-plane hypothesis. The zeroth coefficient agrees unconditionally. -/
theorem canonicalLiCoefficient_eq_actual_pairSum (n : ℕ)
    (h : n = 0 ∨ ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0) :
    canonicalLiCoefficient n = pairSum n := by
  cases n with
  | zero => simp [canonicalLiCoefficient, pairSum, pairCoefficient]
  | succ n =>
    have halfFree := h.resolve_left (Nat.succ_ne_zero n)
    have hRH := rh_iff_xi_right_half_plane.mpr halfFree
    have hcoeff := scalar_expansion_coefficients_unique
      (fun k => (canonicalLiCoefficient (k + 1) : ℂ))
      (fun k => (pairSum (k + 1) : ℂ)) liGenerator
      (fun z hz => rh_canonical_li_global_expansion hRH z
        (by simpa [Metric.mem_ball, dist_zero_right] using hz))
      (fun z hz => actual_pairSum_global_expansion halfFree z hz)
    exact_mod_cast congrFun hcoeff n

/-- The canonical coefficient lies in the closed interval with endpoints
zero and the fixed first coefficient times the square of the index. -/
theorem canonical_li_forward_fixed_quadratic (n : ℕ)
    (h : n = 0 ∨ ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0) :
    canonicalLiCoefficient n ∈ Set.Icc 0 (canonicalLiCoefficient 1 * (n : ℝ) ^ 2) := by
  rcases h with hzero | halfFree
  · subst n
    simp [canonical_li_zero]
  · rw [Set.mem_Icc, canonicalLiCoefficient_eq_actual_pairSum n (.inr halfFree),
      canonicalLiCoefficient_eq_actual_pairSum 1 (.inr halfFree)]
    simpa [mul_comm] using pairSum_nonneg_and_bound (rh_iff_xi_right_half_plane.mpr halfFree) n

private theorem rh_canonical_li_nonnegative_and_fixed_quadratic
    (hRH : RiemannHypothesis) (n : ℕ) :
    canonicalLiCoefficient n ∈ Set.Icc 0 (canonicalLiCoefficient 1 * (n : ℝ) ^ 2) :=
  canonical_li_forward_fixed_quadratic n (.inr (rh_iff_xi_right_half_plane.mp hRH))

/-- Nonnegativity of all derivative-normalized canonical Li coefficients is equivalent to RH. -/
theorem rh_iff_canonical_li_nonnegative :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ canonicalLiCoefficient n :=
  ⟨fun hRH n => (rh_canonical_li_nonnegative_and_fixed_quadratic hRH n).1,
    fun h => canonical_li_nonnegative_implies_rh fun n _ => h n⟩

/-- The nonnegative canonical Li envelope with fixed first coefficient is equivalent to RH. -/
theorem rh_iff_canonical_li_fixed_quadratic :
    RiemannHypothesis ↔ ∀ n : ℕ,
      canonicalLiCoefficient n ∈ Set.Icc 0 (canonicalLiCoefficient 1 * (n : ℝ) ^ 2) :=
  ⟨rh_canonical_li_nonnegative_and_fixed_quadratic, canonical_li_probability_envelope_implies_rh⟩

#print axioms pairCoefficient_abs_summable
#print axioms actual_pair_logDeriv_hasSum
#print axioms actual_pairSum_global_expansion
#print axioms canonicalLiCoefficient_eq_actual_pairSum
#print axioms canonical_li_forward_fixed_quadratic
#print axioms rh_iff_canonical_li_nonnegative
#print axioms rh_iff_canonical_li_fixed_quadratic

end D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
