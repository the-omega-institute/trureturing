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

private theorem firstLiMass_lt_one : firstLiMass < 1 := by
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


private theorem actual_sigma_inverse_square_summable :
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
