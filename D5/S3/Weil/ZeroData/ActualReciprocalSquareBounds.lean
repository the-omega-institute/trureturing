/- GID: D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds
   generality: I
   mirror-B: none(waiver:source-only-implementation-not-frozen)
   mirror-E: none(waiver:source-only-implementation-not-frozen)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten; premises=D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_lt_one,D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_lt_third,D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.gamma_upper_r6,D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.log_pi_lower_r6,D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.sixQ_upper,D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.sixDefect_upper
   digest: Prove unconditional height ten and sharpen the complete actual reciprocal-square mass from the xi resolvent. -/

import D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
import D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Mathlib.Basic.Denumerable
import Mathlib.Basic.Countable.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Real
import D5.S3.Weil.ZetaExplicit.XiLogDeriv
import D5.S3.Weil.ZetaExplicit.GammaRBracket
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
import D5.S3.Arith.GoldenResource.HarmonicGammaTail
import D5.S3.Arith.GoldenResource.RobinRationalBasis

/-!
Every actual nontrivial zeta zero is included, with both imaginary signs and
its exact analytic multiplicity. The normalized rational summand is summed
before taking real parts. Distinct conjugate indices bootstrap the inverse
ordinate estimates. The exact multiplicity-occurrence equivalence transports
the infinite mass to natural indices.

The first normalized xi resolvent at six gives a positive rational kernel.
An ordinate of absolute value at most ten would force its defect above the
upper bound obtained from the actual xi logarithmic derivative, the harmonic
bound for Euler's constant, logarithm estimates, and the complete von Mangoldt
series with an integrable tail. No height, mass, or final analytic bound is
an input to the height theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Weil.Convention
open scoped BigOperators ComplexConjugate

/-- The existing exhaustive distinct-zero source, with analytic multiplicity. -/
abbrev actualData : D5.S3.Weil.ZeroSum.ZeroData := zetaZeroData

/-- The real part of the normalized rational summand at `s = 1`. -/
def pairWeight (rho : ℂ) : ℝ := (1 / (rho * (1 - rho))).re

/-- Twice the actual first Li endpoint. -/
def firstLiMass : ℝ :=
  2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.sqrt Real.pi)

private theorem strip_product_bounds {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    0 < rho.re * (1 - rho.re) ∧ rho.re * (1 - rho.re) ≤ 1 / 4 := by
  constructor
  · exact mul_pos h0 (sub_pos.mpr h1)
  · nlinarith [sq_nonneg (rho.re - 1 / 2)]

private theorem pairWeight_formula (rho : ℂ) :
    pairWeight rho =
      (rho.im ^ 2 + rho.re * (1 - rho.re)) /
        ((rho.im ^ 2 + rho.re * (1 - rho.re)) ^ 2 +
          (rho.im * (1 - 2 * rho.re)) ^ 2) := by
  have hre : (rho * (1 - rho)).re = rho.im ^ 2 + rho.re * (1 - rho.re) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have him : (rho * (1 - rho)).im = rho.im * (1 - 2 * rho.re) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [pairWeight, one_div, Complex.inv_re, Complex.normSq_apply, hre, him]
  simp only [pow_two]

private theorem pairWeight_strip {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    0 < pairWeight rho ∧ 1 / (rho.im ^ 2 + 1) ≤ pairWeight rho := by
  obtain ⟨hp, hp4⟩ := strip_product_bounds h0 h1
  let p := rho.re * (1 - rho.re)
  let u := rho.im ^ 2
  let a := u + p
  let d := a ^ 2 + (rho.im * (1 - 2 * rho.re)) ^ 2
  change 0 < p at hp
  change p ≤ 1 / 4 at hp4
  have hu : 0 ≤ u := sq_nonneg _
  have ha : 0 < a := by dsimp [a]; change 0 < u + p; linarith
  have hd : 0 < d := by
    dsimp [d]
    nlinarith [sq_pos_of_pos ha, sq_nonneg (rho.im * (1 - 2 * rho.re))]
  have he : pairWeight rho = a / d := pairWeight_formula rho
  constructor
  · rw [he]
    exact div_pos ha hd
  · rw [he]
    change 1 / (u + 1) ≤ a / d
    apply (div_le_div_iff₀ (by linarith : 0 < u + 1) hd).2
    have hid : a * (u + 1) - d = p * (3 * u + 1 - p) := by
      dsimp [a, d, p, u]
      ring
    have hfac : 0 ≤ 3 * u + 1 - p := by linarith
    have hgap : 0 ≤ p * (3 * u + 1 - p) := mul_nonneg hp.le hfac
    nlinarith only [hid, hgap]

private theorem pairWeight_conj (rho : ℂ) : pairWeight (conj rho) = pairWeight rho := by
  have hc : conj (1 / (rho * (1 - rho))) =
      1 / (conj rho * (1 - conj rho)) := by simp
  unfold pairWeight
  rw [← hc, Complex.conj_re]

private theorem firstLiMass_pos : 0 < firstLiMass := by
  have h := first_li_coefficient_pos
  unfold firstLiMass
  linarith

theorem firstLiMass_lt_one : firstLiMass < 1 := by
  have hg : Real.eulerMascheroniConstant < 1 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hroot : 3 < 2 * Real.sqrt Real.pi := by
    by_contra h
    have hle : 2 * Real.sqrt Real.pi ≤ 3 := le_of_not_gt h
    have hprod : 0 ≤ (3 / 2 - Real.sqrt Real.pi) * (3 / 2 + Real.sqrt Real.pi) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.pi_gt_three]
  have hlog : 1 < Real.log (2 * Real.sqrt Real.pi) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 (Real.exp_one_lt_three.trans hroot)
  unfold firstLiMass
  linarith

/-- The exact multiplicity-weighted complex mass from the actual xi resolvent.
This is the shared source for the real mass and the complete occurrence package. -/
theorem actual_complex_pairWeight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (actualData.zero n * (1 - actualData.zero n))))
      (firstLiMass : ℂ) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have href : logDeriv xiReading 0 = -logDeriv xiReading 1 := by
    simpa only [sub_self] using
      xi_logDeriv_reflection (1 : ℂ)
  have hend : logDeriv xiReading 1 =
      ((1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    change deriv xiReading 1 / xiReading 1 = _
    exact first_li_coefficient_normalization.1
  convert h using 1
  · funext n
    have hs := (actualData.zero_isNontrivial n).2
    have h0 : actualData.zero n ≠ 0 := by
      intro he; have := hs.1; simpa only [he, Complex.zero_re, lt_self_iff_false] using this
    have h1 : actualData.zero n ≠ 1 := by
      intro he; have := hs.2; simpa only [he, Complex.one_re, lt_self_iff_false] using this
    field_simp [h0, sub_ne_zero.mpr h1.symm]
    <;> ring
  · rw [href, hend]
    unfold firstLiMass
    push_cast
    ring

/-- The exact real sum is obtained from the existing actual xi resolvent. -/
theorem actual_pairWeight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      pairWeight (actualData.zero n)) firstLiMass := by
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.ofReal_re, pairWeight] using Complex.hasSum_re actual_complex_pairWeight_hasSum

private theorem actual_weight_nonneg (n : ℕ) :
    0 ≤ (actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  exact mul_nonneg (Nat.cast_nonneg _) (pairWeight_strip hs.1 hs.2).1.le

private theorem actual_im_ne_zero (n : ℕ) : (actualData.zero n).im ≠ 0 := by
  intro ht
  have hs := (actualData.zero_isNontrivial n).2
  obtain ⟨hp, hp4⟩ := strip_product_bounds hs.1 hs.2
  have hf4 : 4 ≤ pairWeight (actualData.zero n) := by
    have he : pairWeight (actualData.zero n) =
        1 / ((actualData.zero n).re * (1 - (actualData.zero n).re)) := by
      rw [pairWeight_formula, ht]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_mul, add_zero]
      field_simp [hp.ne']
      <;> ring
    rw [he, le_div_iff₀ hp]
    linarith
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hmf : pairWeight (actualData.zero n) ≤
      (actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ pairWeight (actualData.zero n) by linarith)]
  have hb := le_hasSum actual_pairWeight_hasSum n (fun j _ => actual_weight_nonneg j)
  linarith [firstLiMass_lt_one]

private theorem actual_conjugation_ne (n : ℕ) : actualData.conjugation n ≠ n := by
  intro he
  have hi := congrArg Complex.im (actualData.zero_conjugation n)
  rw [he] at hi
  simp only [Complex.conj_im] at hi
  exact actual_im_ne_zero n (by linarith)

private theorem actual_pair_contribution_le (n : ℕ) :
    2 * ((actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n)) ≤
      firstLiMass := by
  classical
  have h := sum_le_hasSum ({n, actualData.conjugation n} : Finset ℕ)
    (fun j _ => actual_weight_nonneg j) actual_pairWeight_hasSum
  rw [Finset.sum_pair (actual_conjugation_ne n).symm,
    actualData.multiplicity_conjugation, actualData.zero_conjugation,
    pairWeight_conj] at h
  linarith

/-- The distinct actual conjugate pair forces a weak height gap, without height ten. -/
theorem actual_ordinate_sq_gt_one (n : ℕ) : 1 < (actualData.zero n).im ^ 2 := by
  have hs := (actualData.zero_isNontrivial n).2
  obtain ⟨hf, hlower⟩ := pairWeight_strip hs.1 hs.2
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hm2 : 0 < 2 * (actualData.multiplicity n : ℝ) := by linarith
  have hquot : pairWeight (actualData.zero n) ≤
      firstLiMass / (2 * (actualData.multiplicity n : ℝ)) := by
    apply (le_div_iff₀ hm2).2
    nlinarith [actual_pair_contribution_le n]
  have hquot_le : firstLiMass / (2 * (actualData.multiplicity n : ℝ)) ≤
      firstLiMass / 2 := by
    apply (div_le_div_iff₀ hm2 (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [mul_nonneg firstLiMass_pos.le (sub_nonneg.mpr hm)]
  have hhalf : pairWeight (actualData.zero n) < 1 / 2 := by
    exact (hquot.trans hquot_le).trans_lt (by linarith [firstLiMass_lt_one])
  have hden : 0 < (actualData.zero n).im ^ 2 + 1 := by positivity
  have hlt : 1 / ((actualData.zero n).im ^ 2 + 1) < 1 / 2 := hlower.trans_lt hhalf
  have hx := (div_lt_iff₀ hden).1 hlt
  nlinarith

private theorem actual_inverse_square_le (n : ℕ) :
    ((actualData.zero n).im)⁻¹ ^ 2 ≤ 2 * pairWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  have hlower := (pairWeight_strip hs.1 hs.2).2
  have hu := actual_ordinate_sq_gt_one n
  have hpos : 0 < (actualData.zero n).im ^ 2 := by linarith
  calc
    ((actualData.zero n).im)⁻¹ ^ 2 = 1 / ((actualData.zero n).im ^ 2) := by
      simp only [inv_pow, one_div]
    _ ≤ 2 * (1 / ((actualData.zero n).im ^ 2 + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
      linarith
    _ ≤ 2 * pairWeight (actualData.zero n) := mul_le_mul_of_nonneg_left hlower (by norm_num)

/-- All distinct actual zeros, with their exact analytic multiplicities, are summable. -/
theorem actual_weighted_inverse_square_summable :
    Summable (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => ?_) (actual_pairWeight_hasSum.summable.mul_left 2)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left (actual_inverse_square_le n)
      (Nat.cast_nonneg (actualData.multiplicity n))


/-- Each exact analytic multiplicity is retained as a finite occurrence fiber. -/
abbrev ActualZeroOccurrence := Σ n : ℕ, Fin (actualData.multiplicity n)

private instance actualOccurrence_infinite : Infinite ActualZeroOccurrence := by
  apply Infinite.of_injective
    (fun n : ℕ => (⟨n, ⟨0, actualData.multiplicity_pos n⟩⟩ : ActualZeroOccurrence))
  intro n m h
  exact congrArg Sigma.fst h

/-- A genuine equivalence, using countability and the positive fibers over every natural index. -/
def actualOccurrenceEquiv : ℕ ≃ ActualZeroOccurrence :=
  Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := ActualZeroOccurrence))

/-- All actual nontrivial zeros, with repetitions exactly equal to analytic order. -/
def actualZero (k : ℕ) : ℂ := actualData.zero (actualOccurrenceEquiv k).1


theorem actual_sigma_inverse_square_summable :
    Summable (fun p : ActualZeroOccurrence => ((actualData.zero p.1).im)⁻¹ ^ 2) := by
  apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
  constructor
  · intro n
    exact Summable.of_finite
  · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using actual_weighted_inverse_square_summable

/-- Exact transport of the infinite mass through both the natural equivalence and finite fibers. -/
theorem actual_inverse_square_tsum_transport :
    (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) =
      ∑' n : ℕ, (actualData.multiplicity n : ℝ) * ((actualData.zero n).im)⁻¹ ^ 2 := by
  calc
    _ = ∑' p : ActualZeroOccurrence, ((actualData.zero p.1).im)⁻¹ ^ 2 :=
      actualOccurrenceEquiv.tsum_eq _
    _ = ∑' n : ℕ, (actualData.multiplicity n : ℝ) * ((actualData.zero n).im)⁻¹ ^ 2 := by
      rw [actual_sigma_inverse_square_summable.tsum_sigma]
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]


/-! ## First-resolvent height exclusion

All indices below still refer to `actualData`, on the whole open strip.
No numerical bound or analytic identity is a parameter of the final result.
The numerical helpers are private. The endpoint and mass normalization also
supply the integrated explicit formula.
-/

/-- The first Li mass normalization used by the height and formula arguments. -/
theorem firstLiMass_split : firstLiMass =
    2 + Real.eulerMascheroniConstant - 2 * Real.log 2 - Real.log Real.pi := by
  rw [firstLiMass, Real.log_mul (by norm_num)
    (Real.sqrt_pos.2 Real.pi_pos).ne', Real.log_sqrt Real.pi_pos.le]
  ring

private theorem firstLiMass_lt_third : firstLiMass < 1 / 3 := by
  have h2 : (2 / 3 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have h3 : (1 : ℝ) < Real.log 3 :=
    lt_trans (by norm_num) Real.log_three_gt_d9
  have hp : Real.log 3 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_three
  rw [firstLiMass_split]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

private theorem actual_ordinate_sq_gt_five (n : ℕ) :
    5 < (actualData.zero n).im ^ 2 := by
  have hs := (actualData.zero_isNontrivial n).2
  obtain ⟨hw, hl⟩ := pairWeight_strip hs.1 hs.2
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hwm : pairWeight (actualData.zero n) ≤
      (actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hw.le]
  have hb := actual_pair_contribution_le n
  have hsmall : 1 / ((actualData.zero n).im ^ 2 + 1) < 1 / 6 := by
    linarith [firstLiMass_lt_third]
  have hx := (div_lt_iff₀ (by positivity :
    0 < (actualData.zero n).im ^ 2 + 1)).1 hsmall
  nlinarith

private theorem gamma_upper_r6 :
    Real.eulerMascheroniConstant < 5787 / 10000 := by
  have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 512
  have hlog : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hfinite : (harmonic 512 : ℝ) -
      9 * (6931471803 / 10000000000 : ℝ) < 5787 / 10000 := by
    -- Exact rational finite sum, intended for ordinary kernel checking.
    -- No floating computation or native_decide supplies this inequality.
    set_option maxRecDepth 8192 in
      norm_num [harmonic, Finset.sum_range_succ]
  simp only [Real.eulerMascheroniSeq', show (512 : ℕ) ≠ 0 by norm_num,
    ite_false] at hg
  norm_num only [Nat.cast_ofNat] at hg
  rw [hlog] at hg
  linarith [Real.log_two_gt_d9]

private theorem log_pi_lower_r6 : 11447 / 10000 < Real.log Real.pi := by
  -- Use the existing positive atanh series with one term at a rational point.
  -- 2*x = 2*(p-3)/(p+3), p = 3.141592, already suffices.
  let p : ℝ := 392699 / 125000
  let x : ℝ := (p - 3) / (p + 3)
  have hx0 : 0 ≤ x := by norm_num [x, p]
  have hx1 : x < 1 := by norm_num [x, p]
  have hl := Real.sum_range_le_log_div hx0 hx1 1
  have he : (1 + x) / (1 - x) = p / 3 := by norm_num [x, p]
  rw [he] at hl
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, mul_zero,
    zero_add, pow_one, div_one] at hl
  have hlog : Real.log (p / 3) = Real.log p - Real.log 3 := by
    exact Real.log_div (by norm_num [p]) (by norm_num)
  rw [hlog] at hl
  have hp : p < Real.pi := by
    dsimp [p]
    convert Real.pi_gt_d6 using 1 <;> norm_num
  have hmono : Real.log p < Real.log Real.pi :=
    Real.log_lt_log (by norm_num [p]) hp
  have hrat : (11447 / 10000 : ℝ) <
      10986122885 / 10000000000 + 2 * x := by norm_num [x, p]
  linarith [Real.log_three_gt_d9]

/-- The R(6) positive kernel on one actual zero (not a high-zero restriction). -/
def sixWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 30))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
def sixDefect : ℝ := 11 / 2 * firstLiMass - (logDeriv xiReading 6).re

private theorem actual_six_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    6 - actualData.zero n ≠ 0 ∧ 5 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_six_ne_zero : xiReading (6 : ℂ) ≠ 0 := by
  have hz : riemannZeta (6 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (6 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (6 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

/-- The zero endpoint used by the reflected resolvents and the formula argument. -/
theorem zero_endpoint_logDeriv :
    logDeriv xiReading 0 = -(firstLiMass / 2 : ℝ) := by
  have hr := xi_logDeriv_reflection (1 : ℂ)
  have he := first_li_coefficient_normalization.1
  change logDeriv xiReading 1 =
    ((1 + Real.eulerMascheroniConstant / 2 -
      Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) at he
  rw [sub_self, he] at hr
  calc
    logDeriv xiReading 0 =
        -((1 + Real.eulerMascheroniConstant / 2 -
          Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := hr
    _ = -(firstLiMass / 2 : ℝ) := by
      unfold firstLiMass
      push_cast
      ring

private theorem one_endpoint_logDeriv :
    logDeriv xiReading 1 = (firstLiMass / 2 : ℝ) := by
  have hr := xi_logDeriv_reflection (1 : ℂ)
  rw [sub_self, zero_endpoint_logDeriv] at hr
  push_cast at hr ⊢
  linear_combination hr

private theorem reflected_six_identity (n : ℕ) :
    6 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (6 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (6 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      165 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 30))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_six_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 30 =
      (6 - actualData.zero n) * (5 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 30 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 6 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_six_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 30))))
      ((((11 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 6) / 165) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 6 xi_six_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (6 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 6 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (6 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 165 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_six_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 165) *
      reflected_six_identity n
  · rw [one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_six_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      sixWeight (actualData.zero n)) (sixDefect / 165) := by
  simpa [sixWeight, sixDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_six_hasSum

private theorem sixWeight_formula (rho : ℂ) :
    sixWeight rho =
      (((rho.im ^ 2 + rho.re * (1 - rho.re)) *
          (rho.im ^ 2 + rho.re * (1 - rho.re) + 30) -
            (rho.im * (1 - 2 * rho.re)) ^ 2) /
        (((rho.im ^ 2 + rho.re * (1 - rho.re)) ^ 2 +
            (rho.im * (1 - 2 * rho.re)) ^ 2) *
          ((rho.im ^ 2 + rho.re * (1 - rho.re) + 30) ^ 2 +
            (rho.im * (1 - 2 * rho.re)) ^ 2))) := by
  have hre : (rho * (1 - rho)).re = rho.im ^ 2 + rho.re * (1 - rho.re) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have him : (rho * (1 - rho)).im = rho.im * (1 - 2 * rho.re) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [sixWeight, one_div, Complex.inv_re, Complex.normSq_mul, Complex.mul_re]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.re_ofNat, Complex.im_ofNat, hre, him, add_zero, pow_two]

private theorem six_kernel_lower (u p b : ℝ) (hu : 5 < u)
    (hp : 0 < p) (hp4 : p ≤ 1 / 4) (hb : b ^ 2 = u * (1 - 4 * p)) :
    9 / (10 * (u + 1) * (u + 31)) ≤
      ((u + p) * (u + p + 30) - b ^ 2) /
        (((u + p) ^ 2 + b ^ 2) * ((u + p + 30) ^ 2 + b ^ 2)) := by
  let d := (u + p) ^ 2 + b ^ 2
  let e := (u + p + 30) ^ 2 + b ^ 2
  let v := (u + p) * (u + p + 30) - b ^ 2
  have hu0 : 0 < u := by linarith
  have hd0 : 0 < d := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith : 0 < u + p))
      (sq_nonneg b)
  have he0 : 0 < e := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith : 0 < u + p + 30))
      (sq_nonneg b)
  have hd : d ≤ u * (u + 1) := by
    have hprod := mul_nonneg hp.le (show 0 ≤ 2 * u - p by linarith)
    dsimp [d]
    nlinarith [hb]
  have he : e ≤ (u + 31) ^ 2 := by
    have hid : e = d + 60 * (u + p) + 900 := by dsimp [e, d]; ring
    nlinarith
  have hv : u * (u + 29) ≤ v := by
    have hup := mul_nonneg hu0.le hp.le
    dsimp [v]
    nlinarith [hb, sq_nonneg p]
  have hde : d * e ≤ u * (u + 1) * (u + 31) ^ 2 :=
    mul_le_mul hd he he0.le (by positivity)
  have hquot : u * (u + 29) / (u * (u + 1) * (u + 31) ^ 2) ≤
      v / (d * e) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hd0 he0)).2
    exact (mul_le_mul_of_nonneg_left hde (by positivity)).trans
      (mul_le_mul_of_nonneg_right hv (by positivity))
  have hcancel : u * (u + 29) / (u * (u + 1) * (u + 31) ^ 2) =
      (u + 29) / ((u + 1) * (u + 31) ^ 2) := by
    field_simp [hu0.ne', show u + 1 ≠ 0 by linarith,
      show u + 31 ≠ 0 by linarith]
    <;> ring
  rw [hcancel] at hquot
  apply le_trans ?_ hquot
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hlin : (9 : ℝ) * (u + 31) ≤ 10 * (u + 29) := by linarith
  convert mul_le_mul_of_nonneg_right hlin
    (show 0 ≤ (u + 1) * (u + 31) by positivity) using 1 <;> ring

private theorem actual_sixWeight_lower (n : ℕ) :
    9 / (10 * ((actualData.zero n).im ^ 2 + 1) *
      ((actualData.zero n).im ^ 2 + 31)) ≤ sixWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  obtain ⟨hp, hp4⟩ := strip_product_bounds hs.1 hs.2
  rw [sixWeight_formula]
  apply six_kernel_lower _ _ _ (actual_ordinate_sq_gt_five n) hp hp4
  ring

private theorem actual_sixWeight_pos (n : ℕ) : 0 < sixWeight (actualData.zero n) := by
  exact lt_of_lt_of_le (by positivity) (actual_sixWeight_lower n)

private theorem sixWeight_conj (rho : ℂ) : sixWeight (conj rho) = sixWeight rho := by
  have he : conj (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 30))) =
      1 / ((conj rho * (1 - conj rho)) * (conj rho * (1 - conj rho) + 30)) := by
    simp only [map_div₀, map_one, map_mul, map_sub, map_add, map_ofNat]
  unfold sixWeight
  rw [← he, Complex.conj_re]

private theorem actual_six_pair_le (n : ℕ) :
    2 * ((actualData.multiplicity n : ℝ) * sixWeight (actualData.zero n)) ≤
      sixDefect / 165 := by
  classical
  have hs := sum_le_hasSum ({n, actualData.conjugation n} : Finset ℕ)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (actual_sixWeight_pos j).le)
    actual_six_hasSum
  rw [Finset.sum_pair (actual_conjugation_ne n).symm,
    actualData.multiplicity_conjugation, actualData.zero_conjugation,
    sixWeight_conj] at hs
  linarith

private theorem actual_low_zero_forces_defect (n : ℕ)
    (hu : (actualData.zero n).im ^ 2 ≤ 100) : 297 / 13231 ≤ sixDefect := by
  have hl := actual_sixWeight_lower n
  have hden : 10 * ((actualData.zero n).im ^ 2 + 1) *
      ((actualData.zero n).im ^ 2 + 31) ≤ 10 * 101 * 131 := by
    have h0 := sq_nonneg (actualData.zero n).im
    nlinarith [mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ (actualData.zero n).im ^ 2 + 132 by positivity)]
  have hw : (9 / (10 * 101 * 131) : ℝ) ≤ sixWeight (actualData.zero n) := by
    apply le_trans ?_ hl
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hwm : sixWeight (actualData.zero n) ≤
      (actualData.multiplicity n : ℝ) * sixWeight (actualData.zero n) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (actual_sixWeight_pos n).le]
  linarith [actual_six_pair_le n]

/-! The analytic side is evaluated only at 6. We never differentiate a zero sum. -/

private theorem xi_six_logDeriv :
    logDeriv xiReading (6 : ℂ) =
      ((67 / 60 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 6 / riemannZeta 6 := by
  have hz : riemannZeta (6 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (6 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (6 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (6 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (6 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (6 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (6 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 6 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (3 : ℂ) =
      ((3 / 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 2
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (6 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (6 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (6 : ℂ) / 2 = 3 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
def sixQ : ℝ := (-deriv riemannZeta (6 : ℂ) / riemannZeta 6).re

private theorem sixDefect_evaluation : sixDefect =
    593 / 60 + 6 * Real.eulerMascheroniConstant - 11 * Real.log 2 -
      5 * Real.log Real.pi + sixQ := by
  rw [sixDefect, firstLiMass_split, xi_six_logDeriv]
  unfold sixQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

private def sixQTerm (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 6

private theorem actual_sixQ_hasSum : HasSum sixQTerm sixQ := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (6 : ℂ)) (by norm_num)
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (6 : ℂ)) (by norm_num)
  have ht (n : ℕ) : LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) 6 n =
        ((sixQTerm n : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero' (by norm_num)]
    simp only [Complex.cpow_ofNat, sixQTerm, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]
  have hc : HasSum (fun n : ℕ => ((sixQTerm n : ℝ) : ℂ))
      (-deriv riemannZeta (6 : ℂ) / riemannZeta 6) := by
    rw [← he]
    exact hs.hasSum.congr_fun (fun n => (ht n).symm)
  simpa only [sixQ, Complex.ofReal_re] using Complex.hasSum_re hc

private theorem log_le_half (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hx.ne' (by norm_num)] at h
  linarith [Real.log_two_lt_d9]

private def sixTail (x : ℝ) : ℝ := x ^ (-5 : ℝ) / 2

private theorem sixTail_antitone : AntitoneOn sixTail (Set.Ici (3 : ℝ)) := by
  intro a ha b hb hab
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp ha]) hab (by norm_num))
    (by norm_num)

private theorem sixTail_integrable :
    MeasureTheory.IntegrableOn sixTail (Set.Ioi (3 : ℝ)) := by
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 3)).div_const 2

private theorem sixTail_integral :
    (∫ x in Set.Ioi (3 : ℝ), sixTail x) = 1 / 648 := by
  change (∫ x in Set.Ioi (3 : ℝ), x ^ (-5 : ℝ) / 2) = 1 / 648
  rw [MeasureTheory.integral_div,
    integral_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 3)]
  norm_num [Real.rpow_neg_natCast]

private theorem sixTail_nonneg (x : ℝ) (hx : x ∈ Set.Ioi (3 : ℝ)) :
    0 ≤ sixTail x := by
  unfold sixTail
  exact div_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _) (by norm_num)

private theorem sixQTerm_le_tail (n : ℕ) (hn : 4 ≤ n) :
    sixQTerm n ≤ sixTail n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) / 2 :=
    ArithmeticFunction.vonMangoldt_le_log.trans (log_le_half n hn0)
  calc
    sixQTerm n ≤ ((n : ℝ) / 2) / (n : ℝ) ^ 6 :=
      div_le_div_of_nonneg_right hl (by positivity)
    _ = sixTail n := by
      unfold sixTail
      rw [show (-5 : ℝ) = -(5 : ℝ) by norm_num, Real.rpow_neg hn0.le,
        show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp [hn0.ne']
      <;> ring

private theorem sixQ_upper : sixQ < 7 / 500 := by
  have hseries := actual_sixQ_hasSum.summable
  have htail := (summable_nat_add_iff 4).mpr hseries
  have hgfull : Summable (fun n : ℕ => sixTail n) :=
    sixTail_antitone.summable_of_integrableOn_Ioi sixTail_integrable sixTail_nonneg
  have hgtail := (summable_nat_add_iff 4).mpr hgfull
  have htail_le : (∑' n : ℕ, sixQTerm (n + 4)) ≤
      ∑' n : ℕ, sixTail (n + 4 : ℕ) := by
    exact htail.tsum_le_tsum (fun n => sixQTerm_le_tail (n + 4) (by omega)) hgtail
  have htint : (∑' n : ℕ, sixTail (n + 4 : ℕ)) ≤ 1 / 648 := by
    have h := sixTail_antitone.tsum_comp_add_le_integral 3
      sixTail_integrable sixTail_nonneg
    norm_num only [Nat.cast_ofNat] at h
    rw [sixTail_integral] at h
    simpa only [← Nat.add_assoc, show (3 + 1 : ℕ) = 4 by norm_num] using h
  have hz : sixQTerm 0 = 0 := by simp [sixQTerm]
  have ho : sixQTerm 1 = 0 := by simp [sixQTerm]
  have h2 : sixQTerm 2 ≤ Real.log 2 / 64 := by
    have h := div_le_div_of_nonneg_right
      (ArithmeticFunction.vonMangoldt_le_log (n := 2))
      (by norm_num : (0 : ℝ) ≤ 64)
    simpa only [sixQTerm, Nat.cast_ofNat, show (2 : ℝ) ^ 6 = 64 by norm_num] using h
  have h3 : sixQTerm 3 ≤ Real.log 3 / 729 := by
    have h := div_le_div_of_nonneg_right
      (ArithmeticFunction.vonMangoldt_le_log (n := 3))
      (by norm_num : (0 : ℝ) ≤ 729)
    simpa only [sixQTerm, Nat.cast_ofNat, show (3 : ℝ) ^ 6 = 729 by norm_num] using h
  have hfinite : (∑ n ∈ Finset.range 4, sixQTerm n) ≤
      Real.log 2 / 64 + Real.log 3 / 729 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, hz, ho,
      zero_add, add_zero] using add_le_add h2 h3
  have hsplit := hseries.sum_add_tsum_nat_add 4
  rw [actual_sixQ_hasSum.tsum_eq] at hsplit
  have hbound : sixQ ≤ Real.log 2 / 64 + Real.log 3 / 729 + 1 / 648 := by
    linarith
  have hlog2 : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlog3 : Real.log 3 < 11 / 10 :=
    Real.log_three_lt_d9.trans (by norm_num)
  have hrat : (7 / 10 : ℝ) / 64 + (11 / 10) / 729 + 1 / 648 < 7 / 500 := by
    norm_num
  linarith

private theorem sixDefect_upper : sixDefect < 329 / 15000 := by
  rw [sixDefect_evaluation]
  have h2 : (6931 / 10000 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  linarith [gamma_upper_r6, log_pi_lower_r6, sixQ_upper]

private theorem actual_ordinate_sq_gt_hundred (n : ℕ) :
    100 < (actualData.zero n).im ^ 2 := by
  by_contra h
  have hl := actual_low_zero_forces_defect n (le_of_not_gt h)
  have hu := sixDefect_upper
  linarith

/-- Every actual nontrivial zeta zero has absolute imaginary part greater than ten.
No additional analytic, numerical, mass, or height premise is required. -/
theorem actual_height_gt_ten (rho : ℂ) (hrho : IsNontrivialZero rho) :
    10 < |rho.im| := by
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hrho
  have hu := actual_ordinate_sq_gt_hundred n
  rw [hn] at hu
  by_contra h
  have hle : |rho.im| ≤ 10 := le_of_not_gt h
  have hp := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ 10 + |rho.im| by positivity)
  nlinarith [sq_abs rho.im]


/-! ## Height-derived refinement of the complete inverse-square mass

The height theorem gives `1 + 1/10^2 = 101/100` on the complete
occurrence family. The pointwise refinement is consumed by the weighted
series bound, which is transported to the public natural-index mass result.
-/

private theorem actual_inverse_square_le_height (n : ℕ) :
    ((actualData.zero n).im)⁻¹ ^ 2 ≤
      (101 / 100 : ℝ) * pairWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  have hlower := (pairWeight_strip hs.1 hs.2).2
  have ht := actual_height_gt_ten (actualData.zero n)
    (actualData.zero_isNontrivial n)
  have hu : (100 : ℝ) < (actualData.zero n).im ^ 2 := by
    have hp : 0 < (|(actualData.zero n).im| - 10) *
        (|(actualData.zero n).im| + 10) :=
      mul_pos (sub_pos.mpr ht) (by linarith)
    nlinarith only [hp, sq_abs ((actualData.zero n).im)]
  have hpos : 0 < (actualData.zero n).im ^ 2 := by linarith
  calc
    ((actualData.zero n).im)⁻¹ ^ 2 = 1 / ((actualData.zero n).im ^ 2) := by
      simp only [inv_pow, one_div]
    _ ≤ (101 / 100 : ℝ) * (1 / ((actualData.zero n).im ^ 2 + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
      linarith
    _ ≤ (101 / 100 : ℝ) * pairWeight (actualData.zero n) :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)

private theorem actual_weighted_inverse_square_mass_le_height :
    (∑' n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2) ≤ (101 / 100 : ℝ) * firstLiMass := by
  have hc := actual_pairWeight_hasSum.mul_left (101 / 100 : ℝ)
  have hdom : ∀ n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2 ≤
        (101 / 100 : ℝ) *
          ((actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n)) := by
    intro n
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (actual_inverse_square_le_height n)
        (Nat.cast_nonneg (actualData.multiplicity n))
  simpa only [hc.tsum_eq] using
    actual_weighted_inverse_square_summable.tsum_le_tsum hdom hc.summable

/-- The full natural-index inverse-square mass is bounded by the height-derived
factor `101/100` times the exact first Li mass. Both signs and every analytic
multiplicity remain in the occurrence family. -/
theorem actual_inverse_square_mass_le_height :
    (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) ≤ (101 / 100 : ℝ) * firstLiMass := by
  rw [actual_inverse_square_tsum_transport]
  exact actual_weighted_inverse_square_mass_le_height


#print axioms actual_height_gt_ten
#print axioms actual_inverse_square_mass_le_height

end D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds



/-! Additive source-only height-fourteen implementation.
The complete preceding H12 candidate is retained verbatim. This block uses
only the original height-ten result, never H12 or H13, as the zero-height
bootstrap. Apply this block alone after the native owner repairs its baseline.
All mathematical bodies below are candidates; none has been compiled here.
-/
namespace D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Weil.Convention
open scoped BigOperators ComplexConjugate Topology

/-- The actual reflected-resolvent kernel. -/
private def h14EightWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 56))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14EightDefect : ℝ := 15 / 2 * firstLiMass - (logDeriv xiReading 8).re

private theorem actual_h14Eight_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    8 - actualData.zero n ≠ 0 ∧ 7 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Eight_ne_zero : xiReading (8 : ℂ) ≠ 0 := by
  have hz : riemannZeta (8 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (8 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (8 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Eight_identity (n : ℕ) :
    8 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (8 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (8 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      420 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 56))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Eight_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 56 =
      (8 - actualData.zero n) * (7 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 56 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 8 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Eight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 56))))
      ((((15 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 8) / 420) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 8 xi_h14Eight_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (8 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 8 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (8 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 420 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Eight_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 420) *
      reflected_h14Eight_identity n
  · rw [one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Eight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14EightWeight (actualData.zero n)) (h14EightDefect / 420) := by
  simpa [h14EightWeight, h14EightDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Eight_hasSum

private theorem xi_h14Eight_logDeriv :
    logDeriv xiReading (8 : ℂ) =
      ((199 / 168 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 8 / riemannZeta 8 := by
  have hz : riemannZeta (8 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (8 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (8 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (8 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (8 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (8 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (8 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 8 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (4 : ℂ) =
      ((11 / 6 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 3
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (8 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (8 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (8 : ℂ) / 2 = 4 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14EightQ : ℝ := (-deriv riemannZeta (8 : ℂ) / riemannZeta 8).re

private theorem h14EightDefect_evaluation : h14EightDefect =
    2321 / 168 + 8 * Real.eulerMascheroniConstant - 15 * Real.log 2 -
      7 * Real.log Real.pi + h14EightQ := by
  rw [h14EightDefect, firstLiMass_split, xi_h14Eight_logDeriv]
  unfold h14EightQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14TenWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 90))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14TenDefect : ℝ := 19 / 2 * firstLiMass - (logDeriv xiReading 10).re

private theorem actual_h14Ten_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    10 - actualData.zero n ≠ 0 ∧ 9 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Ten_ne_zero : xiReading (10 : ℂ) ≠ 0 := by
  have hz : riemannZeta (10 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (10 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (10 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Ten_identity (n : ℕ) :
    10 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (10 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (10 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      855 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 90))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Ten_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 90 =
      (10 - actualData.zero n) * (9 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 90 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 10 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Ten_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 90))))
      ((((19 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 10) / 855) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 10 xi_h14Ten_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (10 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 10 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (10 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 855 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Ten_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 855) *
      reflected_h14Ten_identity n
  · rw [one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Ten_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14TenWeight (actualData.zero n)) (h14TenDefect / 855) := by
  simpa [h14TenWeight, h14TenDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Ten_hasSum

private theorem xi_h14Ten_logDeriv :
    logDeriv xiReading (10 : ℂ) =
      ((451 / 360 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 10 / riemannZeta 10 := by
  have hz : riemannZeta (10 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (10 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (10 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (10 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (10 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (10 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (10 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 10 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (5 : ℂ) =
      ((25 / 12 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 4
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (10 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (10 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (10 : ℂ) / 2 = 5 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14TenQ : ℝ := (-deriv riemannZeta (10 : ℂ) / riemannZeta 10).re

private theorem h14TenDefect_evaluation : h14TenDefect =
    6389 / 360 + 10 * Real.eulerMascheroniConstant - 19 * Real.log 2 -
      9 * Real.log Real.pi + h14TenQ := by
  rw [h14TenDefect, firstLiMass_split, xi_h14Ten_logDeriv]
  unfold h14TenQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14TwelveWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 132))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14TwelveDefect : ℝ := 23 / 2 * firstLiMass - (logDeriv xiReading 12).re

private theorem actual_h14Twelve_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    12 - actualData.zero n ≠ 0 ∧ 11 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Twelve_ne_zero : xiReading (12 : ℂ) ≠ 0 := by
  have hz : riemannZeta (12 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (12 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (12 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Twelve_identity (n : ℕ) :
    12 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (12 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (12 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      1518 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 132))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Twelve_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 132 =
      (12 - actualData.zero n) * (11 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 132 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 12 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Twelve_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 132))))
      ((((23 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 12) / 1518) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 12 xi_h14Twelve_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (12 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 12 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (12 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 1518 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Twelve_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 1518) *
      reflected_h14Twelve_identity n
  · rw [one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Twelve_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14TwelveWeight (actualData.zero n)) (h14TwelveDefect / 1518) := by
  simpa [h14TwelveWeight, h14TwelveDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Twelve_hasSum

private theorem xi_h14Twelve_logDeriv :
    logDeriv xiReading (12 : ℂ) =
      ((579 / 440 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 12 / riemannZeta 12 := by
  have hz : riemannZeta (12 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (12 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (12 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (12 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (12 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (12 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (12 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 12 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (6 : ℂ) =
      ((137 / 60 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 5
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (12 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (12 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (12 : ℂ) / 2 = 6 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14TwelveQ : ℝ := (-deriv riemannZeta (12 : ℂ) / riemannZeta 12).re

private theorem h14TwelveDefect_evaluation : h14TwelveDefect =
    9541 / 440 + 12 * Real.eulerMascheroniConstant - 23 * Real.log 2 -
      11 * Real.log Real.pi + h14TwelveQ := by
  rw [h14TwelveDefect, firstLiMass_split, xi_h14Twelve_logDeriv]
  unfold h14TwelveQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14FourteenWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 182))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14FourteenDefect : ℝ := 27 / 2 * firstLiMass - (logDeriv xiReading 14).re

private theorem actual_h14Fourteen_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    14 - actualData.zero n ≠ 0 ∧ 13 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Fourteen_ne_zero : xiReading (14 : ℂ) ≠ 0 := by
  have hz : riemannZeta (14 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (14 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (14 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Fourteen_identity (n : ℕ) :
    14 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (14 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (14 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      2457 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 182))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Fourteen_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 182 =
      (14 - actualData.zero n) * (13 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 182 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 14 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Fourteen_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 182))))
      ((((27 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 14) / 2457) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 14 xi_h14Fourteen_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (14 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 14 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (14 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 2457 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Fourteen_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 2457) *
      reflected_h14Fourteen_identity n
  · rw [one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Fourteen_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14FourteenWeight (actualData.zero n)) (h14FourteenDefect / 2457) := by
  simpa [h14FourteenWeight, h14FourteenDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Fourteen_hasSum

private theorem xi_h14Fourteen_logDeriv :
    logDeriv xiReading (14 : ℂ) =
      ((4999 / 3640 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 14 / riemannZeta 14 := by
  have hz : riemannZeta (14 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (14 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (14 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (14 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (14 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (14 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (14 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 14 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (7 : ℂ) =
      ((49 / 20 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 6
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (14 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (14 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (14 : ℂ) / 2 = 7 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14FourteenQ : ℝ := (-deriv riemannZeta (14 : ℂ) / riemannZeta 14).re

private theorem h14FourteenDefect_evaluation : h14FourteenDefect =
    93281 / 3640 + 14 * Real.eulerMascheroniConstant - 27 * Real.log 2 -
      13 * Real.log Real.pi + h14FourteenQ := by
  rw [h14FourteenDefect, firstLiMass_split, xi_h14Fourteen_logDeriv]
  unfold h14FourteenQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

private def h14QTerm (s n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s

private def h14Q (s : ℕ) : ℝ :=
  (-deriv riemannZeta (s : ℂ) / riemannZeta s).re

private theorem h14Q_hasSum (s : ℕ) (hs : 2 ≤ s) :
    HasSum (h14QTerm s) (h14Q s) := by
  have hre : 1 < (s : ℂ).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (show 1 < s by omega)
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (s : ℂ)) hre
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s : ℂ)) hre
  have ht (n : ℕ) : LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) n =
        ((h14QTerm s n : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero' (by exact_mod_cast (show s ≠ 0 by omega))]
    simp only [Complex.cpow_natCast, h14QTerm, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]
  have hc : HasSum (fun n : ℕ => ((h14QTerm s n : ℝ) : ℂ))
      (-deriv riemannZeta (s : ℂ) / riemannZeta s) := by
    rw [← he]
    exact hsum.hasSum.congr_fun (fun n => (ht n).symm)
  simpa only [h14Q, Complex.ofReal_re] using Complex.hasSum_re hc

private theorem h14Log2 :
    (138629436111989 / 200000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (346573590279973 / 500000000000000 : ℝ) := by
  have hl := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) 24
  have hu := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) 24
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith only [hl, hu]

private theorem h14Log3 :
    (1098612288668109 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288668111 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (3 / 2 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (3 / 2 : ℝ) = Real.log 3 - 1 * Real.log 2 := by
    rw [show (3 / 2 : ℝ) = 3 / (2 : ℝ) ^ (1 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log5 :
    (1609437912434099 / 1000000000000000 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (804718956217051 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (5 / 4 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (5 / 4 : ℝ) = Real.log 5 - 2 * Real.log 2 := by
    rw [show (5 / 4 : ℝ) = 5 / (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log7 :
    (121619384315957 / 62500000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (389182029811063 / 200000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (7 / 4 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (7 / 4 : ℝ) = Real.log 7 - 2 * Real.log 2 := by
    rw [show (7 / 4 : ℝ) = 7 / (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log11 :
    (2397895272798369 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895272798373 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (11 / 8 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (11 / 8 : ℝ) = Real.log 11 - 3 * Real.log 2 := by
    rw [show (11 / 8 : ℝ) = 11 / (2 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log13 :
    (512989871492307 / 200000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (2564949357461539 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (13 / 8 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (13 / 8 : ℝ) = Real.log 13 - 3 * Real.log 2 := by
    rw [show (13 / 8 : ℝ) = 13 / (2 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log17 :
    (1416606672028107 / 500000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344056219 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (17 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (17 / 16 : ℝ) = Real.log 17 - 4 * Real.log 2 := by
    rw [show (17 / 16 : ℝ) = 17 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log19 :
    (2944438979166439 / 1000000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (736109744791611 / 250000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (19 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (19 / 16 : ℝ) = Real.log 19 - 4 * Real.log 2 := by
    rw [show (19 / 16 : ℝ) = 19 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log23 :
    (783873553982287 / 250000000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (3135494215929153 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (23 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (23 / 16 : ℝ) = Real.log 23 - 4 * Real.log 2 := by
    rw [show (23 / 16 : ℝ) = 23 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log29 :
    (420911978748309 / 125000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295829986477 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (29 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (29 / 16 : ℝ) = Real.log 29 - 4 * Real.log 2 := by
    rw [show (29 / 16 : ℝ) = 29 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log31 :
    (686797440897029 / 200000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (68679744089703 / 20000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (31 / 16 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (31 / 16 : ℝ) = Real.log 31 - 4 * Real.log 2 := by
    rw [show (31 / 16 : ℝ) = 31 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log37 :
    (1805458956322111 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (902729478161057 / 250000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (37 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (37 / 32 : ℝ) = Real.log 37 - 5 * Real.log 2 := by
    rw [show (37 / 32 : ℝ) = 37 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log41 :
    (1856786033352153 / 500000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (464196508338039 / 125000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (41 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (41 / 32 : ℝ) = Real.log 41 - 5 * Real.log 2 := by
    rw [show (41 / 32 : ℝ) = 41 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log43 :
    (94030002892339 / 25000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600057846783 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (43 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (43 / 32 : ℝ) = Real.log 43 - 5 * Real.log 2 := by
    rw [show (43 / 32 : ℝ) = 43 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log47 :
    (3850147601710057 / 1000000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (3850147601710063 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (47 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (47 / 32 : ℝ) = Real.log 47 - 5 * Real.log 2 := by
    rw [show (47 / 32 : ℝ) = 47 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log53 :
    (99257297838803 / 25000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145956776063 / 500000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (53 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (53 / 32 : ℝ) = Real.log 53 - 5 * Real.log 2 := by
    rw [show (53 / 32 : ℝ) = 53 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log59 :
    (4077537443905717 / 1000000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537443905723 / 1000000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (59 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (59 / 32 : ℝ) = Real.log 59 - 5 * Real.log 2 := by
    rw [show (59 / 32 : ℝ) = 59 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Log61 :
    (4110873864173309 / 1000000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (822174772834663 / 200000000000000 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := (61 / 32 : ℝ)) (by norm_num) (by norm_num) 20
  have he : Real.log (61 / 32 : ℝ) = Real.log 61 - 5 * Real.log 2 := by
    rw [show (61 / 32 : ℝ) = 61 / (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter,
    Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2, h14Log2.1, h14Log2.2]

private theorem h14Gamma : Real.eulerMascheroniConstant < 5772157 / 10000000 := by
  exact lt_trans
    D5.S3.Arith.GoldenResource.HarmonicGammaTail.eulerMascheroni_upper_128
    (by norm_num)

private theorem h14LogPi : 2289459771 / 2000000000 < Real.log Real.pi := by
  let p : ℝ := 314159265358979323846 / 100000000000000000000
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_expansion_remainder_bound
    (y := p / 2) (by norm_num [p]) (by norm_num [p]) 12
  have he : Real.log (p / 2) = Real.log p - Real.log 2 :=
    Real.log_div (by norm_num [p]) (by norm_num)
  dsimp [D5.S3.Arith.GoldenResource.RobinRationalBasis.logRemainder] at h
  rw [he] at h
  have hr : (2289459771 / 2000000000 : ℝ) <
      6931471803 / 10000000000 +
        D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial
          (D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter (p / 2)) 12 := by
    norm_num [p, D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter, Finset.sum_range_succ]
  have hp : p < Real.pi := by
    dsimp [p]
    convert Real.pi_gt_d20 using 1 <;> norm_num
  have hm := Real.log_lt_log (by norm_num [p] : 0 < p) hp
  have hlogp : 6931471803 / 10000000000 +
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial
        (D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhParameter (p / 2)) 12 <
      Real.log p := by
    linarith only [h.1, Real.log_two_gt_d9]
  exact lt_trans hr (lt_trans hlogp hm)

private def h14Finite (s : ℕ) : ℝ :=
  Real.log 2 / (2 : ℝ) ^ s +
    Real.log 3 / (3 : ℝ) ^ s +
    Real.log 2 / (4 : ℝ) ^ s +
    Real.log 5 / (5 : ℝ) ^ s +
    Real.log 7 / (7 : ℝ) ^ s +
    Real.log 2 / (8 : ℝ) ^ s +
    Real.log 3 / (9 : ℝ) ^ s +
    Real.log 11 / (11 : ℝ) ^ s +
    Real.log 13 / (13 : ℝ) ^ s +
    Real.log 2 / (16 : ℝ) ^ s +
    Real.log 17 / (17 : ℝ) ^ s +
    Real.log 19 / (19 : ℝ) ^ s +
    Real.log 23 / (23 : ℝ) ^ s +
    Real.log 5 / (25 : ℝ) ^ s +
    Real.log 3 / (27 : ℝ) ^ s +
    Real.log 29 / (29 : ℝ) ^ s +
    Real.log 31 / (31 : ℝ) ^ s +
    Real.log 2 / (32 : ℝ) ^ s +
    Real.log 37 / (37 : ℝ) ^ s +
    Real.log 41 / (41 : ℝ) ^ s +
    Real.log 43 / (43 : ℝ) ^ s +
    Real.log 47 / (47 : ℝ) ^ s +
    Real.log 7 / (49 : ℝ) ^ s +
    Real.log 53 / (53 : ℝ) ^ s +
    Real.log 59 / (59 : ℝ) ^ s +
    Real.log 61 / (61 : ℝ) ^ s +
    Real.log 2 / (64 : ℝ) ^ s

private theorem h14Finite_eq (s : ℕ) :
    (∑ n ∈ Finset.range 65, h14QTerm s n) = h14Finite s := by
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
  have h1 : ArithmeticFunction.vonMangoldt 1 = 0 := by simp
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h5 : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)
  have h6 : ArithmeticFunction.vonMangoldt 6 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h7 : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ (3 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h9 : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h10 : ArithmeticFunction.vonMangoldt 10 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h11 : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 11)
  have h12 : ArithmeticFunction.vonMangoldt 12 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h13 : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 13)
  have h14 : ArithmeticFunction.vonMangoldt 14 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h15 : ArithmeticFunction.vonMangoldt 15 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h16 : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    rw [show (16 : ℕ) = 2 ^ (4 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (4 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h17 : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 17)
  have h18 : ArithmeticFunction.vonMangoldt 18 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h19 : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 19)
  have h20 : ArithmeticFunction.vonMangoldt 20 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h21 : ArithmeticFunction.vonMangoldt 21 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h22 : ArithmeticFunction.vonMangoldt 22 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h23 : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 23)
  have h24 : ArithmeticFunction.vonMangoldt 24 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h25 : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
    rw [show (25 : ℕ) = 5 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)
  have h26 : ArithmeticFunction.vonMangoldt 26 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h27 : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
    rw [show (27 : ℕ) = 3 ^ (3 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have h28 : ArithmeticFunction.vonMangoldt 28 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h29 : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 29)
  have h30 : ArithmeticFunction.vonMangoldt 30 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h31 : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 31)
  have h32 : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
    rw [show (32 : ℕ) = 2 ^ (5 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (5 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have h33 : ArithmeticFunction.vonMangoldt 33 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h34 : ArithmeticFunction.vonMangoldt 34 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 17 = p := huniq 17 ⟨by norm_num, by norm_num⟩
    omega
  have h35 : ArithmeticFunction.vonMangoldt 35 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h36 : ArithmeticFunction.vonMangoldt 36 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h37 : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 37)
  have h38 : ArithmeticFunction.vonMangoldt 38 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 19 = p := huniq 19 ⟨by norm_num, by norm_num⟩
    omega
  have h39 : ArithmeticFunction.vonMangoldt 39 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h40 : ArithmeticFunction.vonMangoldt 40 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h41 : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 41)
  have h42 : ArithmeticFunction.vonMangoldt 42 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h43 : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 43)
  have h44 : ArithmeticFunction.vonMangoldt 44 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h45 : ArithmeticFunction.vonMangoldt 45 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h46 : ArithmeticFunction.vonMangoldt 46 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 23 = p := huniq 23 ⟨by norm_num, by norm_num⟩
    omega
  have h47 : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 47)
  have h48 : ArithmeticFunction.vonMangoldt 48 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h49 : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
    rw [show (49 : ℕ) = 7 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)
  have h50 : ArithmeticFunction.vonMangoldt 50 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    omega
  have h51 : ArithmeticFunction.vonMangoldt 51 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 17 = p := huniq 17 ⟨by norm_num, by norm_num⟩
    omega
  have h52 : ArithmeticFunction.vonMangoldt 52 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 13 = p := huniq 13 ⟨by norm_num, by norm_num⟩
    omega
  have h53 : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 53)
  have h54 : ArithmeticFunction.vonMangoldt 54 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h55 : ArithmeticFunction.vonMangoldt 55 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 5 = p := huniq 5 ⟨by norm_num, by norm_num⟩
    have hb : 11 = p := huniq 11 ⟨by norm_num, by norm_num⟩
    omega
  have h56 : ArithmeticFunction.vonMangoldt 56 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h57 : ArithmeticFunction.vonMangoldt 57 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 19 = p := huniq 19 ⟨by norm_num, by norm_num⟩
    omega
  have h58 : ArithmeticFunction.vonMangoldt 58 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 29 = p := huniq 29 ⟨by norm_num, by norm_num⟩
    omega
  have h59 : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 59)
  have h60 : ArithmeticFunction.vonMangoldt 60 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    omega
  have h61 : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 61)
  have h62 : ArithmeticFunction.vonMangoldt 62 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 2 = p := huniq 2 ⟨by norm_num, by norm_num⟩
    have hb : 31 = p := huniq 31 ⟨by norm_num, by norm_num⟩
    omega
  have h63 : ArithmeticFunction.vonMangoldt 63 = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have ha : 3 = p := huniq 3 ⟨by norm_num, by norm_num⟩
    have hb : 7 = p := huniq 7 ⟨by norm_num, by norm_num⟩
    omega
  have h64 : ArithmeticFunction.vonMangoldt 64 = Real.log 2 := by
    rw [show (64 : ℕ) = 2 ^ (6 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (6 : ℕ) ≠ 0)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  simp only [h14QTerm, h14Finite, Finset.sum_range_succ, Finset.sum_range_zero,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64,
    Nat.cast_ofNat, zero_div, zero_add, add_zero]

private def h14Tail (s : ℕ) (x : ℝ) : ℝ := x ^ (1 - (s : ℝ)) / 2

private theorem h14Tail_antitone (s : ℕ) (hs : 3 ≤ s) :
    AntitoneOn (h14Tail s) (Set.Ici (64 : ℝ)) := by
  intro a ha b hb hab
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp ha]) hab
      (by
        have hs' : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
        linarith)) (by norm_num)

private theorem h14Tail_integrable (s : ℕ) (hs : 3 ≤ s) :
    MeasureTheory.IntegrableOn (h14Tail s) (Set.Ioi (64 : ℝ)) := by
  exact (integrableOn_Ioi_rpow_of_lt
    (by
      have hs' : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith)
    (by norm_num : (0 : ℝ) < 64)).div_const 2

private theorem h14Tail_nonneg (s : ℕ) (x : ℝ) (hx : x ∈ Set.Ioi (64 : ℝ)) :
    0 ≤ h14Tail s x := by
  exact div_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _) (by norm_num)

private theorem h14Term_le_tail (s n : ℕ) (hn : 65 ≤ n) :
    h14QTerm s n ≤ h14Tail s n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) / 2 :=
    ArithmeticFunction.vonMangoldt_le_log.trans (log_le_half n hn0)
  calc
    h14QTerm s n ≤ ((n : ℝ) / 2) / (n : ℝ) ^ s :=
      div_le_div_of_nonneg_right hl (by positivity)
    _ = h14Tail s n := by
      rw [h14Tail, Real.rpow_sub hn0, Real.rpow_one, Real.rpow_natCast]
      ring

private theorem h14Q_finite_lower (s : ℕ) (hs : 3 ≤ s) :
    h14Finite s ≤ h14Q s := by
  rw [← h14Finite_eq]
  apply sum_le_hasSum (Finset.range 65)
    (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (h14Q_hasSum s (by omega))

private theorem h14Q_finite_upper (s : ℕ) (hs : 3 ≤ s) :
    h14Q s ≤ h14Finite s + (∫ x in Set.Ioi (64 : ℝ), h14Tail s x) := by
  have hseries := (h14Q_hasSum s (by omega)).summable
  have htail := (summable_nat_add_iff 65).mpr hseries
  have hgfull : Summable (fun n : ℕ => h14Tail s n) :=
    (h14Tail_antitone s hs).summable_of_integrableOn_Ioi
      (h14Tail_integrable s hs) (h14Tail_nonneg s)
  have hgtail := (summable_nat_add_iff 65).mpr hgfull
  have htail_le := htail.tsum_le_tsum
    (fun n => h14Term_le_tail s (n + 65) (by omega)) hgtail
  have htint := (h14Tail_antitone s hs).tsum_comp_add_le_integral 64
    (h14Tail_integrable s hs) (h14Tail_nonneg s)
  norm_num only [Nat.cast_ofNat] at htint
  have htint' : (∑' n : ℕ, h14Tail s (n + 65 : ℕ)) ≤
      ∫ x in Set.Ioi (64 : ℝ), h14Tail s x := by
    simpa only [← Nat.add_assoc, show (64 + 1 : ℕ) = 65 by norm_num] using htint
  have hsplit := hseries.sum_add_tsum_nat_add 65
  rw [(h14Q_hasSum s (by omega)).tsum_eq, h14Finite_eq] at hsplit
  linarith only [hsplit, htail_le, htint']

private theorem h14Q6_bound : h14Q 6 ≤ (12633076304737 / 1000000000000000 : ℝ) := by
  have h := h14Q_finite_upper 6 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 6 x) = (1 / 134217728 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (6 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (6 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 6 ≤ (17249321509217161498400458902529221275645632912349903331633559641695482165021093576227780971581265613435917700914900024065485577135422988848470963330504156371061324564891212261 / 1365410235157891238947835315549977423165935059055842834311559910610947327036629826991657180903272858646616152840361446862489314125590244186695462289408000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (17249321509217161498400458902529221275645632912349903331633559641695482165021093576227780971581265613435917700914900024065485577135422988848470963330504156371061324564891212261 / 1365410235157891238947835315549977423165935059055842834311559910610947327036629826991657180903272858646616152840361446862489314125590244186695462289408000000000000000000000000000 : ℝ) + (1 / 134217728) ≤ (12633076304737 / 1000000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

private theorem h14Q8_bound : (1445084153477 / 500000000000000 : ℝ) ≤ h14Q 8 := by
  have h := h14Q_finite_lower 8 (by norm_num)
  have hf : (3677274747139739474093032805621964745927047700647429769155714443776690319280276256892856506192440708792693455740908631592280350760978836944345287483860587678359512993791910832703034924532994089196263330580424016220485903653737923 / 1272339308732082349912793946777540127293305849622521581431386473593914333794257667919294400239490867213709238425438793277955737370276553670500109253431211341813784240832954932029606242586777308438200320000000000000000000000000000000 : ℝ) ≤ h14Finite 8 := by
    dsimp [h14Finite]
    linarith only [h14Log2.1, h14Log3.1, h14Log5.1, h14Log7.1, h14Log11.1, h14Log13.1, h14Log17.1, h14Log19.1, h14Log23.1, h14Log29.1, h14Log31.1, h14Log37.1, h14Log41.1, h14Log43.1, h14Log47.1, h14Log53.1, h14Log59.1, h14Log61.1]
  have hr : (1445084153477 / 500000000000000 : ℝ) ≤ (3677274747139739474093032805621964745927047700647429769155714443776690319280276256892856506192440708792693455740908631592280350760978836944345287483860587678359512993791910832703034924532994089196263330580424016220485903653737923 / 1272339308732082349912793946777540127293305849622521581431386473593914333794257667919294400239490867213709238425438793277955737370276553670500109253431211341813784240832954932029606242586777308438200320000000000000000000000000000000) := by norm_num
  linarith only [h, hf, hr]

private theorem h14Q10_bound : h14Q 10 ≤ (174085111381 / 250000000000000 : ℝ) := by
  have h := h14Q_finite_upper 10 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 10 x) = (1 / 4503599627370496 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (10 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (10 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 10 ≤ (1857577211964025815411150338103476064653274472898733597229358463009816620319307509011926686536563726599393389128504318823821108457828409626456008602869442476331313283636830763529280841835350382127391520125002119150132535455405518355859430147700254784863165031816566162003200345236901 / 2667627917557450816561849618012376138330598469099411734267724087723496016100571871889637252651104842866736498652142736309663457134840979906909332338838037316722266173420920907059876823936150802692008425638944208469371356106518994769688343197493546188800000000000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (1857577211964025815411150338103476064653274472898733597229358463009816620319307509011926686536563726599393389128504318823821108457828409626456008602869442476331313283636830763529280841835350382127391520125002119150132535455405518355859430147700254784863165031816566162003200345236901 / 2667627917557450816561849618012376138330598469099411734267724087723496016100571871889637252651104842866736498652142736309663457134840979906909332338838037316722266173420920907059876823936150802692008425638944208469371356106518994769688343197493546188800000000000000000000000000000000000 : ℝ) + (1 / 4503599627370496) ≤ (174085111381 / 250000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

private theorem h14Q12_bound : (2677198143 / 15625000000000 : ℝ) ≤ h14Q 12 := by
  have h := h14Q_finite_lower 12 (by norm_num)
  have hf : (425917548289740772598845621061159896700160705476288498215162310804980542657065936860942525756878337501403239071034147897496295863932293405091665514279344388433217865455336405389037832977176268191280091941767428195198735982693834242021839142362348086033793294802476190812469036665299614727174370378220819757601678790974930532113143765443 / 2485793480365237136503119446972360110536523498394024653874541743926968137354882849424565745530347249324850334855712980017406796948387639322546653446721294268632682601477170772602132945312171463061837353326059512871906330445486044185629125438209088379054748648771408824725509757725747413019488998653952000000000000000000000000000000000000000 : ℝ) ≤ h14Finite 12 := by
    dsimp [h14Finite]
    linarith only [h14Log2.1, h14Log3.1, h14Log5.1, h14Log7.1, h14Log11.1, h14Log13.1, h14Log17.1, h14Log19.1, h14Log23.1, h14Log29.1, h14Log31.1, h14Log37.1, h14Log41.1, h14Log43.1, h14Log47.1, h14Log53.1, h14Log59.1, h14Log61.1]
  have hr : (2677198143 / 15625000000000 : ℝ) ≤ (425917548289740772598845621061159896700160705476288498215162310804980542657065936860942525756878337501403239071034147897496295863932293405091665514279344388433217865455336405389037832977176268191280091941767428195198735982693834242021839142362348086033793294802476190812469036665299614727174370378220819757601678790974930532113143765443 / 2485793480365237136503119446972360110536523498394024653874541743926968137354882849424565745530347249324850334855712980017406796948387639322546653446721294268632682601477170772602132945312171463061837353326059512871906330445486044185629125438209088379054748648771408824725509757725747413019488998653952000000000000000000000000000000000000000) := by norm_num
  linarith only [h, hf, hr]

private theorem h14Q14_bound : h14Q 14 ≤ (42538887969 / 1000000000000000 : ℝ) := by
  have h := h14Q_finite_upper 14 (by norm_num)
  have ht : (∫ x in Set.Ioi (64 : ℝ), h14Tail 14 x) = (1 / 113336795588871485128704 : ℝ) := by
    change (∫ x in Set.Ioi (64 : ℝ), x ^ (1 - (14 : ℝ)) / 2) = _
    rw [MeasureTheory.integral_div, integral_Ioi_rpow_of_lt
      (by norm_num : (1 - (14 : ℝ)) < -1) (by norm_num : (0 : ℝ) < 64)]
    norm_num [Real.rpow_neg_natCast]
  have hf : h14Finite 14 ≤ (221703978187685851911099559204634454887584281497709992886425975529391773382425321273661557671319187584317198060011632827481718349905383345521139417137901278314551660639576458698243205572166250535908491039797432148348615509775333685305286570702206306578384097064819183375263536112151192169600450070319375093428144775402207233877570835342430815235169863297130329976022485667589578514257855141 / 5211795344209504029754563105301476616109476784967940523077477746495069349658767178514705802768329381958887254794348584104337731880320527057831810163023431573521473290329067148337234578401209466566945624662227907460925816785471912758087460930616071722590068600245043508128183385732491533763292906820223875028782320956504515332195762655303414291554631680000000000000000000000000000000000000000000 : ℝ) := by
    dsimp [h14Finite]
    linarith only [h14Log2.2, h14Log3.2, h14Log5.2, h14Log7.2, h14Log11.2, h14Log13.2, h14Log17.2, h14Log19.2, h14Log23.2, h14Log29.2, h14Log31.2, h14Log37.2, h14Log41.2, h14Log43.2, h14Log47.2, h14Log53.2, h14Log59.2, h14Log61.2]
  have hr : (221703978187685851911099559204634454887584281497709992886425975529391773382425321273661557671319187584317198060011632827481718349905383345521139417137901278314551660639576458698243205572166250535908491039797432148348615509775333685305286570702206306578384097064819183375263536112151192169600450070319375093428144775402207233877570835342430815235169863297130329976022485667589578514257855141 / 5211795344209504029754563105301476616109476784967940523077477746495069349658767178514705802768329381958887254794348584104337731880320527057831810163023431573521473290329067148337234578401209466566945624662227907460925816785471912758087460930616071722590068600245043508128183385732491533763292906820223875028782320956504515332195762655303414291554631680000000000000000000000000000000000000000000 : ℝ) + (1 / 113336795588871485128704) ≤ (42538887969 / 1000000000000000) := by norm_num
  rw [ht] at h
  linarith only [h, hf, hr]

/- Private consumed sector proof, adapted verbatim from the static finite-sector source. -/
namespace H14Sector
open scoped BigOperators Topology
open Set Complex

private def stripImaginary (u p : ℝ) : ℝ := Real.sqrt (u * (1 - 4 * p))

private def factor {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) : ℂ :=
  ((u + p + c j : ℝ) : ℂ) + (stripImaginary u p : ℂ) * I

private def reciprocalProduct {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℂ :=
  ∏ j, (factor c u p j)⁻¹

private def weight {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  (reciprocalProduct c u p).re

private def angle {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) : ℝ :=
  Real.arctan (stripImaginary u p / (u + p + c j))

private def totalAngle {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  ∑ j, angle c u p j

private def amplitude {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  ∏ j, ‖factor c u p j‖⁻¹

private def threshold (N : ℕ) : ℝ := 4 * ((N : ℝ) + 1) ^ 2 / Real.pi ^ 2

private lemma factor_re {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) :
    (factor c u p j).re = u + p + c j := by simp [factor]

private lemma factor_im {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) :
    (factor c u p j).im = stripImaginary u p := by simp [factor]

private lemma factor_real_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    0 < u + p + c j := by linarith [hc j]

private theorem factor_ne_zero {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    factor c u p j ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hx := factor_real_pos hc hu hp j
  simp only [factor_re, Complex.zero_re] at hr
  linarith

private lemma imaginary_bounds {u p : ℝ} (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    0 ≤ stripImaginary u p ∧ stripImaginary u p ≤ Real.sqrt u := by
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt ?_⟩
  have h := mul_nonneg hu.le hp.1
  nlinarith

private lemma imaginary_sq {u p : ℝ} (hu : 0 < u) (hp : p ≤ 1 / 4) :
    stripImaginary u p ^ 2 = u * (1 - 4 * p) := by
  exact Real.sq_sqrt (mul_nonneg hu.le (by linarith))

private lemma imaginary_pos {u p : ℝ} (hu : 0 < u) (hp : p < 1 / 4) :
    0 < stripImaginary u p := by
  exact Real.sqrt_pos.2 (mul_pos hu (by linarith))

private lemma angle_bounds {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) (j : Fin N) :
    0 ≤ angle c u p j ∧ angle c u p j ≤ 1 / Real.sqrt u := by
  have hx := factor_real_pos hc hu hp.1 j
  have hb := imaginary_bounds hu hp
  have hs := Real.sqrt_pos.2 hu
  have hss := Real.sq_sqrt hu.le
  have hratio : stripImaginary u p / (u + p + c j) ≤ 1 / Real.sqrt u := by
    have hxu : u ≤ u + p + c j := by linarith [hp.1, hc j]
    calc
      stripImaginary u p / (u + p + c j) ≤ stripImaginary u p / u :=
        div_le_div_of_nonneg_left hb.1 hu hxu
      _ ≤ 1 / Real.sqrt u := by
        apply (div_le_div_iff₀ hu hs).2
        have hm := mul_le_mul_of_nonneg_right hb.2 hs.le
        nlinarith
  have hnonneg := div_nonneg hb.1 hx.le
  exact ⟨Real.arctan_nonneg.2 hnonneg,
    (Real.arctan_le_self hnonneg).trans hratio⟩

private lemma totalAngle_bounds {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    0 ≤ totalAngle c u p ∧ totalAngle c u p ≤ (N : ℝ) / Real.sqrt u := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (angle_bounds hc hu hp j).1)
  · have h := Finset.sum_le_sum (s := Finset.univ)
      (fun j _ => (angle_bounds hc hu hp j).2)
    simpa [totalAngle, div_eq_mul_inv] using h

private theorem augmented_angle_mem {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) (j : Fin N) :
    totalAngle c u p + angle c u p j ∈ Ico 0 (Real.pi / 2) := by
  have hT := totalAngle_bounds hc hu hp
  have hj := angle_bounds hc hu hp j
  refine ⟨add_nonneg hT.1 hj.1, lt_of_le_of_lt ?_ hsector⟩
  calc
    totalAngle c u p + angle c u p j ≤
        (N : ℝ) / Real.sqrt u + 1 / Real.sqrt u := add_le_add hT.2 hj.2
    _ = ((N : ℝ) + 1) / Real.sqrt u := by ring

private lemma totalAngle_mem {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    totalAngle c u p ∈ Ico 0 (Real.pi / 2) := by
  have hT := totalAngle_bounds hc hu hp
  refine ⟨hT.1, lt_of_le_of_lt hT.2 (lt_trans ?_ hsector)⟩
  exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 hu)).2 (by linarith)

private lemma arg_eq_angle {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    Complex.arg (factor c u p j) = angle c u p j := by
  have hx : 0 < (factor c u p j).re := by
    rw [factor_re]; exact factor_real_pos hc hu hp j
  have ht : Real.tan (Complex.arg (factor c u p j)) =
      stripImaginary u p / (u + p + c j) := by
    rw [Complex.tan_arg, factor_im, factor_re]
  exact (Real.arctan_eq_of_tan_eq ht
    ⟨Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hx),
      Complex.arg_lt_pi_div_two_iff.2 (Or.inl hx)⟩).symm

private lemma factor_inverse_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    (factor c u p j)⁻¹ = ((‖factor c u p j‖⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-angle c u p j : ℝ) : ℂ) * I) := by
  have hpol : ((‖factor c u p j‖ : ℝ) : ℂ) *
      Complex.exp ((angle c u p j : ℂ) * I) = factor c u p j := by
    rw [← arg_eq_angle hc hu hp j]
    exact Complex.norm_mul_exp_arg_mul_I _
  calc
    (factor c u p j)⁻¹ =
        (((‖factor c u p j‖ : ℝ) : ℂ) *
          Complex.exp ((angle c u p j : ℂ) * I))⁻¹ := congrArg Inv.inv hpol.symm
    _ = _ := by
      simp only [mul_inv_rev, ← Complex.exp_neg, Complex.ofReal_inv,
        Complex.ofReal_neg, neg_mul]
      ring

private lemma amplitude_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    0 < amplitude c u p := by
  exact Finset.prod_pos (fun j _ => inv_pos.2
    (norm_pos_iff.2 (factor_ne_zero hc hu hp j)))

private theorem reciprocalProduct_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    reciprocalProduct c u p = (amplitude c u p : ℂ) *
      Complex.exp (((-totalAngle c u p : ℝ) : ℂ) * I) := by
  have hs : (∑ j : Fin N, ((-angle c u p j : ℝ) : ℂ) * I) =
      ((-totalAngle c u p : ℝ) : ℂ) * I := by
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, Finset.sum_neg_distrib,
      totalAngle]
  calc
    reciprocalProduct c u p = ∏ j : Fin N,
        (((‖factor c u p j‖⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-angle c u p j : ℝ) : ℂ) * I)) := by
      exact Finset.prod_congr rfl (fun j _ => factor_inverse_polar hc hu hp j)
    _ = (∏ j : Fin N, ((‖factor c u p j‖⁻¹ : ℝ) : ℂ)) *
        ∏ j : Fin N, Complex.exp (((-angle c u p j : ℝ) : ℂ) * I) :=
      Finset.prod_mul_distrib
    _ = _ := by rw [← Complex.exp_sum, hs]; simp [amplitude]

private theorem reciprocalProduct_div_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    reciprocalProduct c u p / factor c u p j =
      (‖reciprocalProduct c u p / factor c u p j‖ : ℂ) *
        Complex.exp (((-(totalAngle c u p + angle c u p j) : ℝ) : ℂ) * I) := by
  let a := amplitude c u p * ‖factor c u p j‖⁻¹
  have ha : 0 < a := mul_pos (amplitude_pos hc hu hp)
    (inv_pos.2 (norm_pos_iff.2 (factor_ne_zero hc hu hp j)))
  have he : reciprocalProduct c u p / factor c u p j = (a : ℂ) *
      Complex.exp (((-(totalAngle c u p + angle c u p j) : ℝ) : ℂ) * I) := by
    rw [div_eq_mul_inv, reciprocalProduct_polar hc hu hp,
      factor_inverse_polar hc hu hp j]
    dsimp [a]
    push_cast
    rw [show -(↑(totalAngle c u p) + ↑(angle c u p j)) * I =
      (-↑(totalAngle c u p) * I) + (-↑(angle c u p j) * I) by ring,
      Complex.exp_add]
    ring
  have hn : ‖reciprocalProduct c u p / factor c u p j‖ = a := by
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hn]
  exact he

private theorem weight_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    0 < weight c u p := by
  have ht := totalAngle_mem hc hu hp hsector
  have hcos := Real.cos_pos_of_mem_Ioo
    (show totalAngle c u p ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩)
  have he : weight c u p = amplitude c u p * Real.cos (totalAngle c u p) := by
    rw [weight, reciprocalProduct_polar hc hu hp.1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [he]
  exact mul_pos (amplitude_pos hc hu hp.1) hcos

private lemma hasDerivAt_imaginary_u {u p : ℝ} (hu : 0 < u) (hp : p ≤ 1 / 4) :
    HasDerivAt (fun v : ℝ => stripImaginary v p) (stripImaginary u p / (2 * u)) u := by
  by_cases hb : p = 1 / 4
  · subst p
    simpa [stripImaginary] using (hasDerivAt_const u (0 : ℝ))
  · have hp' : p < 1 / 4 := lt_of_le_of_ne hp hb
    have hrad : u * (1 - 4 * p) ≠ 0 := ne_of_gt (mul_pos hu (by linarith))
    have hd := ((hasDerivAt_id u).mul_const (1 - 4 * p)).sqrt hrad
    have hsq := imaginary_sq hu hp
    have him := imaginary_pos hu hp'
    have he : (1 - 4 * p) / (2 * stripImaginary u p) =
        stripImaginary u p / (2 * u) := by
      apply (div_eq_div_iff (by positivity : 2 * stripImaginary u p ≠ 0)
        (by positivity : 2 * u ≠ 0)).2
      nlinarith
    have hd' : HasDerivAt (fun v : ℝ => stripImaginary v p)
        ((1 - 4 * p) / (2 * stripImaginary u p)) u := by
      simpa [stripImaginary] using hd
    rw [he] at hd'
    exact hd'

private lemma hasDerivAt_imaginary_p {u p : ℝ} (hu : 0 < u) (hp : p < 1 / 4) :
    HasDerivAt (fun q : ℝ => stripImaginary u q) (-2 * u / stripImaginary u p) p := by
  have hrad : u * (1 - 4 * p) ≠ 0 := ne_of_gt (mul_pos hu (by linarith))
  have hlin : HasDerivAt (fun q : ℝ => u * (1 - 4 * q)) (-4 * u) p := by
    convert (((hasDerivAt_id p).const_mul 4).const_sub 1).const_mul u using 1 <;>
      simp [Function.id_def] <;> ring
  have hd := hlin.sqrt hrad
  convert hd using 1 <;>
    simp only [stripImaginary, div_eq_mul_inv, mul_inv_rev] <;> ring

private lemma hasDerivAt_product {N : ℕ} {f : Fin N → ℝ → ℂ} {d : ℂ} {t : ℝ}
    (hf : ∀ j, HasDerivAt (f j) d t) (hn : ∀ j, f j t ≠ 0) :
    HasDerivAt (fun x : ℝ => ∏ j, (f j x)⁻¹)
      (-(∑ j, ((∏ k, (f k t)⁻¹) / f j t) * d)) t := by
  classical
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun j _ => (hf j).inv (hn j))
  convert hd using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hp := Finset.mul_prod_erase Finset.univ (fun k => (f k t)⁻¹)
    (Finset.mem_univ j)
  rw [← hp]
  simp only [smul_eq_mul, Pi.inv_apply]
  field_simp [hn j] <;> ring

private def derivativeTerm {N : ℕ} (c : Fin N → ℝ) (u p v : ℝ) (j : Fin N) : ℝ :=
  ‖reciprocalProduct c u p / factor c u p j‖ *
    (Real.cos (totalAngle c u p + angle c u p j) +
      v * Real.sin (totalAngle c u p + angle c u p j))

private lemma real_product_derivative {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (v : ℝ) :
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + (v : ℂ) * I))).re = -∑ j, derivativeTerm c u p v j := by
  simp only [Complex.neg_re, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [reciprocalProduct_div_polar hc hu hp j]
  simp only [Complex.mul_re, Complex.mul_im]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp [derivativeTerm, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg, Real.cos_add, Real.sin_add] <;> ring

private theorem hasDerivAt_weight_u {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    HasDerivAt (fun v : ℝ => weight c v p)
      (-∑ j, ‖reciprocalProduct c u p / factor c u p j‖ *
        (Real.cos (totalAngle c u p + angle c u p j) +
          (stripImaginary u p / (2 * u)) *
            Real.sin (totalAngle c u p + angle c u p j))) u := by
  have hf : ∀ j, HasDerivAt (fun v : ℝ => factor c v p j)
      (1 + ((stripImaginary u p / (2 * u) : ℝ) : ℂ) * I) u := by
    intro j
    have hr := (((hasDerivAt_id u).add_const p).add_const (c j)).ofReal_comp
    have hi := ((hasDerivAt_imaginary_u hu hp.2).ofReal_comp).mul_const I
    have hsum := hr.add hi
    convert hsum using 1 <;>
      (try funext y) <;>
      simp [factor, Function.comp_def]
  have hF := hasDerivAt_product hf (factor_ne_zero hc hu hp.1)
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hF
  change HasDerivAt (fun v : ℝ => weight c v p)
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + ((stripImaginary u p / (2 * u) : ℝ) : ℂ) * I))).re u at hR
  rw [real_product_derivative hc hu hp.1] at hR
  exact hR

private theorem hasDerivAt_weight_p {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Ico 0 (1 / 4)) :
    HasDerivAt (fun q : ℝ => weight c u q)
      (-∑ j, ‖reciprocalProduct c u p / factor c u p j‖ *
        (Real.cos (totalAngle c u p + angle c u p j) -
          (2 * u / stripImaginary u p) *
            Real.sin (totalAngle c u p + angle c u p j))) p := by
  have hf : ∀ j, HasDerivAt (fun q : ℝ => factor c u q j)
      (1 + ((-2 * u / stripImaginary u p : ℝ) : ℂ) * I) p := by
    intro j
    have hr := (((hasDerivAt_id p).const_add u).add_const (c j)).ofReal_comp
    have hi := ((hasDerivAt_imaginary_p hu hp.2).ofReal_comp).mul_const I
    have hsum := hr.add hi
    convert hsum using 1 <;>
      (try funext y) <;>
      simp [factor, Function.comp_def]
  have hF := hasDerivAt_product hf (factor_ne_zero hc hu hp.1)
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p hF
  change HasDerivAt (fun q : ℝ => weight c u q)
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + ((-2 * u / stripImaginary u p : ℝ) : ℂ) * I))).re p at hR
  rw [real_product_derivative hc hu hp.1] at hR
  simpa only [derivativeTerm, neg_mul, neg_div, sub_eq_add_neg] using hR

private lemma quotient_norm_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    0 < ‖reciprocalProduct c u p / factor c u p j‖ := by
  apply norm_pos_iff.2
  exact div_ne_zero (Finset.prod_ne_zero_iff.2
    (fun k _ => inv_ne_zero (factor_ne_zero hc hu hp k)))
      (factor_ne_zero hc hu hp j)

private theorem deriv_weight_u_neg {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hN : 0 < N) (hc : ∀ j, 0 ≤ c j) (hu : 0 < u)
    (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    deriv (fun v : ℝ => weight c v p) u < 0 := by
  rw [(hasDerivAt_weight_u hc hu hp).deriv]
  apply neg_neg_of_pos
  apply Finset.sum_pos
  · intro j _
    have ha := augmented_angle_mem hc hu hp hsector j
    have hcos := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩
    have hsin := Real.sin_nonneg_of_mem_Icc
      ⟨ha.1, by linarith [Real.pi_pos, ha.2]⟩
    apply mul_pos (quotient_norm_pos hc hu hp.1 j)
    exact add_pos_of_pos_of_nonneg hcos
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity)) hsin)
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩

private lemma p_bracket_neg {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0) (hu : 0 < u) (hup : p < u)
    (hp : p ∈ Ico 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) (j : Fin N) :
    Real.cos (totalAngle c u p + angle c u p j) -
      (2 * u / stripImaginary u p) *
        Real.sin (totalAngle c u p + angle c u p j) < 0 := by
  obtain ⟨j₀, hj₀⟩ := hz
  have hpclosed : p ∈ Icc 0 (1 / 4) := ⟨hp.1, hp.2.le⟩
  have hb := imaginary_pos hu hp.2
  have ha := augmented_angle_mem hc hu hpclosed hsector j
  have h0 := angle_bounds hc hu hpclosed j₀
  have hj := angle_bounds hc hu hpclosed j
  have hsum : angle c u p j₀ ≤ totalAngle c u p :=
    Finset.single_le_sum (fun k _ => (angle_bounds hc hu hpclosed k).1)
      (Finset.mem_univ j₀)
  have hle : angle c u p j₀ ≤ totalAngle c u p + angle c u p j := by linarith
  have ht := Real.strictMonoOn_tan.monotoneOn
    (show angle c u p j₀ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], (hle.trans_lt ha.2)⟩)
    (show totalAngle c u p + angle c u p j ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], ha.2⟩) hle
  have ht0 : Real.tan (angle c u p j₀) = stripImaginary u p / (u + p) := by
    simp [angle, hj₀, Real.tan_arctan]
  rw [ht0] at ht
  have hratio : stripImaginary u p / (2 * u) < stripImaginary u p / (u + p) := by
    have hup0 : 0 < u + p := by linarith [hu, hp.1]
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * u)
      hup0).2
    nlinarith [mul_pos hb (sub_pos.2 hup)]
  have htan := hratio.trans_le ht
  have hcos := Real.cos_pos_of_mem_Ioo
    (show totalAngle c u p + angle c u p j ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], ha.2⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  have hm := (div_lt_div_iff₀ (by positivity : 0 < 2 * u) hcos).1 htan
  have hfin : Real.cos (totalAngle c u p + angle c u p j) <
      (2 * u * Real.sin (totalAngle c u p + angle c u p j)) /
        stripImaginary u p := (lt_div_iff₀ hb).2 (by nlinarith)
  rw [show (2 * u * Real.sin (totalAngle c u p + angle c u p j)) /
      stripImaginary u p = (2 * u / stripImaginary u p) *
        Real.sin (totalAngle c u p + angle c u p j) by ring] at hfin
  linarith

private theorem deriv_weight_p_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0) (hu : 0 < u) (hup : p < u)
    (hp : p ∈ Ico 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    0 < deriv (fun q : ℝ => weight c u q) p := by
  rw [(hasDerivAt_weight_p hc hu hp).deriv, neg_pos]
  apply Finset.sum_neg
  · intro j _
    exact mul_neg_of_pos_of_neg (quotient_norm_pos hc hu hp.1 j)
      (p_bracket_neg hc hz hu hup hp hsector j)
  · obtain ⟨j₀, _⟩ := hz
    exact ⟨j₀, Finset.mem_univ _⟩

private lemma continuousAt_weight_p {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    ContinuousAt (fun q : ℝ => weight c u q) p := by
  have hF : ContinuousAt (fun q : ℝ => reciprocalProduct c u q) p := by
    apply tendsto_finsetProd Finset.univ
    intro j _
    have hfac : ContinuousAt (fun b : ℝ => factor c u b j) p := by
      unfold factor stripImaginary
      fun_prop
    change Filter.Tendsto ((fun b : ℝ => factor c u b j)⁻¹) (𝓝 p)
      (𝓝 ((factor c u p j)⁻¹))
    exact (hfac.inv₀ (factor_ne_zero hc hu hp j)).tendsto
  exact Complex.continuous_re.continuousAt.comp hF

private theorem strictAntiOn_weight_u {N : ℕ} {c : Fin N → ℝ} {p : ℝ}
    (hN : 0 < N) (hc : ∀ j, 0 ≤ c j) (hp : p ∈ Icc 0 (1 / 4)) :
    StrictAntiOn (fun u : ℝ => weight c u p) (Ioi (threshold N)) := by
  have hparam : ∀ u ∈ Ioi (threshold N), 0 < u ∧
      ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2 := by
    intro u hu
    have hT : 0 ≤ threshold N := by unfold threshold; positivity
    have hu0 : 0 < u := lt_of_le_of_lt hT hu
    have hs := Real.sqrt_pos.2 hu0
    have hq : 0 < 2 * ((N : ℝ) + 1) / Real.pi := by positivity
    have hsq : (2 * ((N : ℝ) + 1) / Real.pi) ^ 2 = threshold N := by
      unfold threshold; ring
    have hroot : 2 * ((N : ℝ) + 1) / Real.pi < Real.sqrt u := by
      apply (Real.lt_sqrt hq.le).2
      have hbound : (2 * ((N : ℝ) + 1) / Real.pi) ^ 2 < u := by
        rw [hsq]; exact hu
      exact hbound
    have hmul := (div_lt_iff₀ Real.pi_pos).1 hroot
    refine ⟨hu0, (div_lt_iff₀ hs).2 ?_⟩
    nlinarith
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro u hu
    exact (hasDerivAt_weight_u hc (hparam u hu).1 hp).continuousAt.continuousWithinAt
  · intro u hu
    have humem := interior_subset hu
    exact deriv_weight_u_neg hN hc (hparam u humem).1 hp (hparam u humem).2

private theorem strictMonoOn_weight_p {N : ℕ} {c : Fin N → ℝ} {u : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0)
    (hu : 0 < u)
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    StrictMonoOn (weight c u) (Icc 0 (1 / 4)) := by
  have hN : 0 < N := by
    obtain ⟨j₀, _⟩ := hz
    exact lt_of_le_of_lt (Nat.zero_le j₀.val) j₀.isLt
  have hNc : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hs := Real.sqrt_pos.2 hu
  have hmul := (div_lt_iff₀ hs).1 hsector
  have hroot : 1 < Real.sqrt u := by
    by_contra hn
    have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
      (by positivity : 0 ≤ Real.pi / 2)
    nlinarith [Real.pi_lt_four]
  have huone : (1 : ℝ) < u := by
    have h := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).1 hroot
    simpa using h
  have huquarter : (1 / 4 : ℝ) < u := lt_trans (by norm_num) huone
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro p hp
    exact (continuousAt_weight_p hc hu hp.1).continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact deriv_weight_p_pos hc hz hu (lt_trans hp.2 huquarter)
      ⟨hp.1.le, hp.2⟩ hsector

/- Simultaneous conjugation is valid for every real imaginary part, including zero. -/
private theorem reciprocalProduct_signed_conj {N : ℕ} (c : Fin N → ℝ) (x b : ℝ) :
    (∏ j : Fin N, (((x + c j : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹) =
      star (∏ j : Fin N, (((x + c j : ℝ) : ℂ) + (b : ℂ) * I)⁻¹) := by
  simp only [Complex.star_def, map_prod, map_inv₀, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]

private theorem real_product_signed_reduction {N : ℕ} (c : Fin N → ℝ) (u p b : ℝ)
    (hb : b ^ 2 = u * (1 - 4 * p)) :
    (∏ j : Fin N, (((u + p + c j : ℝ) : ℂ) + (b : ℂ) * I)⁻¹).re =
      weight c u p := by
  have hrad : 0 ≤ u * (1 - 4 * p) := by rw [← hb]; positivity
  have hs : stripImaginary u p ^ 2 = u * (1 - 4 * p) := Real.sq_sqrt hrad
  have hsign : b = stripImaginary u p ∨ b = -stripImaginary u p := by
    exact sq_eq_sq_iff_eq_or_eq_neg.1 (hb.trans hs.symm)
  rcases hsign with h | h
  · subst b; rfl
  · rw [h, reciprocalProduct_signed_conj c (u + p) (stripImaginary u p)]
    simp only [Complex.star_def, Complex.conj_re]
    rfl


end H14Sector

namespace H14Sector
private def shifts : Fin 6 → ℝ := ![0, 30, 56, 90, 132, 182]

private lemma shifts_nonneg : ∀ j, 0 ≤ shifts j := by
  intro j
  fin_cases j <;> norm_num [shifts]

private lemma shifts_zero : ∃ j, shifts j = 0 := ⟨0, by norm_num [shifts]⟩

private lemma six_phase {u : ℝ} (hu : 100 < u) :
    ((6 : ℝ) + 1) / Real.sqrt u < Real.pi / 2 := by
  have hs : 10 < Real.sqrt u := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 10)).2
    norm_num
    exact hu
  have hrat : (7 : ℝ) / Real.sqrt u < 7 / 10 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hs
  norm_num only at *
  linarith [Real.pi_gt_three]

private lemma six_threshold : threshold 6 < 100 := by
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  change 4 * ((6 : ℝ) + 1) ^ 2 / Real.pi ^ 2 < 100
  apply (div_lt_iff₀ hpi2).2
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

private theorem six_positive {u p : ℝ} (hu : 100 < u) (hp : p ∈ Set.Icc 0 (1 / 4)) :
    0 < weight shifts u p := by
  exact weight_pos shifts_nonneg (by linarith) hp (six_phase hu)

private theorem six_lower {u p : ℝ} (hu : 100 < u) (hupper : u ≤ 196)
    (hp : p ∈ Set.Icc 0 (1 / 4)) :
    weight shifts 196 0 ≤ weight shifts u p := by
  have ha := strictAntiOn_weight_u (by decide : 0 < 6) shifts_nonneg hp
  have hleft : u ∈ Set.Ioi (threshold 6) := lt_trans six_threshold hu
  have hright : (196 : ℝ) ∈ Set.Ioi (threshold 6) := by
    exact lt_trans six_threshold (by norm_num)
  have hucomp : weight shifts 196 p ≤ weight shifts u p :=
    ha.antitoneOn hleft hright hupper
  have hm := strictMonoOn_weight_p shifts_nonneg shifts_zero
    (by norm_num : (0 : ℝ) < 196) (six_phase (by norm_num : (100 : ℝ) < 196))
  have hpcomp : weight shifts 196 0 ≤ weight shifts 196 p :=
    hm.monotoneOn (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 4)) hp hp.1
  exact hpcomp.trans hucomp

private theorem six_pair_value : 2 * weight shifts 196 0 =
    (345650537 : ℝ) / 72636763553532703907200 := by
  norm_num [weight, reciprocalProduct, factor, stripImaginary, shifts,
    Fin.prod_univ_succ, Complex.inv_re, Complex.inv_im, Complex.normSq,
    Complex.mul_re, Complex.mul_im]
end H14Sector

private def h14Kernel (rho : ℂ) : ℂ :=
  1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 30) *
    (rho * (1 - rho) + 56) * (rho * (1 - rho) + 90) *
    (rho * (1 - rho) + 132) * (rho * (1 - rho) + 182))

private def h14Weight (rho : ℂ) : ℝ := (h14Kernel rho).re

private def h14Mass : ℝ :=
  sixDefect / 3990729600 - h14EightDefect / 3555377280 +
    h14TenDefect / 6739588800 - h14TwelveDefect / 24711825600 +
    h14FourteenDefect / 216459734400

private theorem h14Shift_ne_zero (n : ℕ) (s : ℕ) (hs : 2 ≤ s) :
    actualData.zero n * (1 - actualData.zero n) + (s : ℂ) * ((s : ℂ) - 1) ≠ 0 := by
  have hs0 : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  have hstrip := (actualData.zero_isNontrivial n).2
  have he : actualData.zero n * (1 - actualData.zero n) + (s : ℂ) * ((s : ℂ) - 1) =
      ((s : ℂ) - actualData.zero n) * ((s : ℂ) - 1 + actualData.zero n) := by ring
  rw [he]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at hr
    linarith
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
      Complex.one_re, Complex.zero_re] at hr
    linarith

private theorem h14PartialFractions (n : ℕ) :
    h14Kernel (actualData.zero n) =
      (165 / 3990729600 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 30))) -
      (420 / 3555377280 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 56))) +
      (855 / 6739588800 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 90))) -
      (1518 / 24711825600 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 132))) +
      (2457 / 216459734400 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 182))) := by
  obtain ⟨h0, h1, _, _⟩ := actual_six_denominators n
  have hq := mul_ne_zero h0 h1
  have h30 : actualData.zero n * (1 - actualData.zero n) + 30 ≠ 0 := by
    convert h14Shift_ne_zero n 6 (by norm_num) using 1 <;> norm_num
  have h56 : actualData.zero n * (1 - actualData.zero n) + 56 ≠ 0 := by
    convert h14Shift_ne_zero n 8 (by norm_num) using 1 <;> norm_num
  have h90 : actualData.zero n * (1 - actualData.zero n) + 90 ≠ 0 := by
    convert h14Shift_ne_zero n 10 (by norm_num) using 1 <;> norm_num
  have h132 : actualData.zero n * (1 - actualData.zero n) + 132 ≠ 0 := by
    convert h14Shift_ne_zero n 12 (by norm_num) using 1 <;> norm_num
  have h182 : actualData.zero n * (1 - actualData.zero n) + 182 ≠ 0 := by
    convert h14Shift_ne_zero n 14 (by norm_num) using 1 <;> norm_num
  unfold h14Kernel
  field_simp [hq, h30, h56, h90, h132, h182]
  <;> ring

private theorem h14Weight_partialFractions (n : ℕ) :
    h14Weight (actualData.zero n) =
      (165 / 3990729600 : ℝ) * sixWeight (actualData.zero n) -
      (420 / 3555377280 : ℝ) * h14EightWeight (actualData.zero n) +
      (855 / 6739588800 : ℝ) * h14TenWeight (actualData.zero n) -
      (1518 / 24711825600 : ℝ) * h14TwelveWeight (actualData.zero n) +
      (2457 / 216459734400 : ℝ) * h14FourteenWeight (actualData.zero n) := by
  have h := congrArg Complex.re (h14PartialFractions n)
  simpa only [h14Weight, sixWeight, h14EightWeight, h14TenWeight,
    h14TwelveWeight, h14FourteenWeight, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, mul_zero,
    zero_div, add_zero] using h

private theorem h14_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14Weight (actualData.zero n)) h14Mass := by
  have h := ((((actual_six_hasSum.mul_left (165 / 3990729600 : ℝ)).sub
    (actual_h14Eight_hasSum.mul_left (420 / 3555377280 : ℝ))).add
    (actual_h14Ten_hasSum.mul_left (855 / 6739588800 : ℝ))).sub
    (actual_h14Twelve_hasSum.mul_left (1518 / 24711825600 : ℝ))).add
    (actual_h14Fourteen_hasSum.mul_left (2457 / 216459734400 : ℝ))
  convert h using 1
  · funext n
    rw [h14Weight_partialFractions]
    ring
  · unfold h14Mass
    ring

private theorem h14Mass_evaluation : h14Mass =
    66493177 / 143006288128704000 +
      (4 / 12649365729) * Real.eulerMascheroniConstant -
      Real.log 2 / 1816214400 - (9487 / 40477970332800) * Real.log Real.pi +
      h14Q 6 / 3990729600 - h14Q 8 / 3555377280 +
      h14Q 10 / 6739588800 - h14Q 12 / 24711825600 +
      h14Q 14 / 216459734400 := by
  rw [h14Mass, sixDefect_evaluation, h14EightDefect_evaluation,
    h14TenDefect_evaluation, h14TwelveDefect_evaluation, h14FourteenDefect_evaluation]
  unfold sixQ h14EightQ h14TenQ h14TwelveQ h14FourteenQ h14Q
  norm_num only [Nat.cast_ofNat] 
  ring

private theorem h14Mass_upper :
    h14Mass ≤ 72126772613108177 / 15194418113674800000000000000000 := by
  rw [h14Mass_evaluation]
  have hr : (66493177 / 143006288128704000 : ℝ) +
      (4 / 12649365729) * (5772157 / 10000000) -
      (6931471803 / 10000000000) / 1816214400 -
      (9487 / 40477970332800) * (2289459771 / 2000000000) +
      (12633076304737 / 1000000000000000) / 3990729600 -
      (1445084153477 / 500000000000000) / 3555377280 +
      (174085111381 / 250000000000000) / 6739588800 -
      (2677198143 / 15625000000000) / 24711825600 +
      (42538887969 / 1000000000000000) / 216459734400 =
        72126772613108177 / 15194418113674800000000000000000 := by norm_num
  linarith only [hr, h14Gamma.le, Real.log_two_gt_d9.le, h14LogPi.le,
    h14Q6_bound, h14Q8_bound, h14Q10_bound, h14Q12_bound, h14Q14_bound]

private theorem h14Weight_sector (rho : ℂ) :
    h14Weight rho = H14Sector.weight H14Sector.shifts (rho.im ^ 2)
      (rho.re * (1 - rho.re)) := by
  have hb : (rho.im * (1 - 2 * rho.re)) ^ 2 =
      rho.im ^ 2 * (1 - 4 * (rho.re * (1 - rho.re))) := by ring
  have he : rho * (1 - rho) =
      ((rho.im ^ 2 + rho.re * (1 - rho.re) : ℝ) : ℂ) +
        ((rho.im * (1 - 2 * rho.re) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
        ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im] <;> ring
  rw [← H14Sector.real_product_signed_reduction H14Sector.shifts
    (rho.im ^ 2) (rho.re * (1 - rho.re)) (rho.im * (1 - 2 * rho.re)) hb]
  have hprod : (∏ j : Fin 6,
      (((rho.im ^ 2 + rho.re * (1 - rho.re) + H14Sector.shifts j : ℝ) : ℂ) +
        ((rho.im * (1 - 2 * rho.re) : ℝ) : ℂ) * Complex.I)) =
      (rho * (1 - rho)) * (rho * (1 - rho) + 30) *
        (rho * (1 - rho) + 56) * (rho * (1 - rho) + 90) *
        (rho * (1 - rho) + 132) * (rho * (1 - rho) + 182) := by
    simp [H14Sector.shifts, Fin.prod_univ_succ, he]
    <;> push_cast <;> ring
  rw [Finset.prod_inv_distrib, hprod]
  simp only [h14Weight, h14Kernel, one_div]


private theorem h14Weight_pos (n : ℕ) : 0 < h14Weight (actualData.zero n) := by
  have hstrip := (actualData.zero_isNontrivial n).2
  obtain ⟨hp, hp4⟩ := strip_product_bounds hstrip.1 hstrip.2
  rw [h14Weight_sector]
  exact H14Sector.six_positive (actual_ordinate_sq_gt_hundred n) ⟨hp.le, hp4⟩

private theorem h14Weight_conj (rho : ℂ) : h14Weight (conj rho) = h14Weight rho := by
  have h : h14Kernel (conj rho) = conj (h14Kernel rho) := by
    simp only [h14Kernel, map_div₀, map_mul, map_add, map_sub, map_one,
      map_natCast, map_ofNat, starRingEnd_apply]
  unfold h14Weight
  rw [h, Complex.conj_re]

private theorem h14Pair_le (n : ℕ) :
    2 * ((actualData.multiplicity n : ℝ) * h14Weight (actualData.zero n)) ≤
      h14Mass := by
  classical
  have h := sum_le_hasSum ({n, actualData.conjugation n} : Finset ℕ)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (h14Weight_pos j).le) h14_hasSum
  rw [Finset.sum_pair (actual_conjugation_ne n).symm,
    actualData.multiplicity_conjugation, actualData.zero_conjugation,
    h14Weight_conj] at h
  linarith only [h]

private theorem h14Low_forces_mass (n : ℕ) (hu : (actualData.zero n).im ^ 2 ≤ 196) :
    345650537 / 72636763553532703907200 ≤ h14Mass := by
  have hstrip := (actualData.zero_isNontrivial n).2
  obtain ⟨hp, hp4⟩ := strip_product_bounds hstrip.1 hstrip.2
  have hl := H14Sector.six_lower (actual_ordinate_sq_gt_hundred n) hu ⟨hp.le, hp4⟩
  rw [← h14Weight_sector] at hl
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hmul : h14Weight (actualData.zero n) ≤
      (actualData.multiplicity n : ℝ) * h14Weight (actualData.zero n) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (h14Weight_pos n).le]
  have hv := H14Sector.six_pair_value
  linarith only [hl, hmul, hv, h14Pair_le n]

private theorem h14_ordinate_sq (n : ℕ) : 196 < (actualData.zero n).im ^ 2 := by
  by_contra h
  have hl := h14Low_forces_mass n (le_of_not_gt h)
  have hu := h14Mass_upper
  have hgap : (345650537 / 72636763553532703907200 : ℝ) -
      72126772613108177 / 15194418113674800000000000000000 =
        4091911135692077535684108547 /
          349994189092536057987654937200000000000000000 := by norm_num
  have hpos : (0 : ℝ) < 4091911135692077535684108547 /
      349994189092536057987654937200000000000000000 := by norm_num
  linarith only [hl, hu, hgap, hpos]

/-- Every original nontrivial zero has absolute ordinate greater than fourteen.
Both signs and the original positive analytic multiplicities are retained. -/
theorem actual_height_gt_fourteen (rho : ℂ) (hrho : IsNontrivialZero rho) :
    14 < |rho.im| := by
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hrho
  have hu := h14_ordinate_sq n
  rw [hn] at hu
  by_contra h
  have hle : |rho.im| ≤ 14 := le_of_not_gt h
  have hp := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ 14 + |rho.im| by positivity)
  nlinarith [sq_abs rho.im]

private theorem actual_inverse_square_le_height_fourteen (n : ℕ) :
    ((actualData.zero n).im)⁻¹ ^ 2 ≤
      (197 / 196 : ℝ) * pairWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  have hlower := (pairWeight_strip hs.1 hs.2).2
  have ht := actual_height_gt_fourteen (actualData.zero n)
    (actualData.zero_isNontrivial n)
  have hu : (196 : ℝ) < (actualData.zero n).im ^ 2 := by
    have hp : 0 < (|(actualData.zero n).im| - 14) *
        (|(actualData.zero n).im| + 14) :=
      mul_pos (sub_pos.mpr ht) (by linarith)
    nlinarith only [hp, sq_abs ((actualData.zero n).im)]
  have hpos : 0 < (actualData.zero n).im ^ 2 := by linarith
  calc
    ((actualData.zero n).im)⁻¹ ^ 2 = 1 / ((actualData.zero n).im ^ 2) := by
      simp only [inv_pow, one_div]
    _ ≤ (197 / 196 : ℝ) * (1 / ((actualData.zero n).im ^ 2 + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
      linarith
    _ ≤ (197 / 196 : ℝ) * pairWeight (actualData.zero n) :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)

private theorem actual_weighted_inverse_square_mass_le_height_fourteen :
    (∑' n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2) ≤ (197 / 196 : ℝ) * firstLiMass := by
  have hc := actual_pairWeight_hasSum.mul_left (197 / 196 : ℝ)
  have hdom : ∀ n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2 ≤
        (197 / 196 : ℝ) *
          ((actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n)) := by
    intro n
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (actual_inverse_square_le_height_fourteen n)
        (Nat.cast_nonneg (actualData.multiplicity n))
  simpa only [hc.tsum_eq] using
    actual_weighted_inverse_square_summable.tsum_le_tsum hdom hc.summable

/-- The complete natural-occurrence inverse-square mass has factor `197/196`.
Both signs, every distinct actual zero, and every analytic multiplicity are
preserved by the original occurrence equivalence. -/
theorem actual_inverse_square_mass_le_height_fourteen :
    (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) ≤ (197 / 196 : ℝ) * firstLiMass := by
  rw [actual_inverse_square_tsum_transport]
  exact actual_weighted_inverse_square_mass_le_height_fourteen

end D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

