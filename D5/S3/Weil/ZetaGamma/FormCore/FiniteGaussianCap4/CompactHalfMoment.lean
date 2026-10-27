/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactHalfMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual compact exponential moments for the signed Gaussian certificate. -/
/-
Actual moment suppliers for the finite Gaussian signed multiplier.

Analytic suppliers for the finite Gaussian signed multiplier construction.
The positive-beta-series formula and parameters are those in the completed
independent review independent_check.py (SHA256
f1e7c5aee8882415df524430ad3012a81b4c0ba6c5b68baa5aff41c82f75fcb5).
That computation is a mathematical reference, never a proof premise.

The beta polynomial integral below uses Mathlib's existing complex beta API;
the series exchange uses its interval dominated-convergence theorem. We take
p >= 0, so real rpow has a continuous extension at zero, including p = 0.
All integrals are ordinary Mathlib interval integrals against volume.
No large numerical enclosure, matrix entry, physical bound, or RH is claimed.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianExpPiRounding
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! Actual compact half moments and positive beta-series bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set
open scoped BigOperators Topology

/-- Product from j = 0 through n, inclusive. -/
def momentDenominator (p : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (n + 1), (p + 1 + (j : ℝ))

/-- The positive coefficient a_n in the compact incomplete-gamma series. -/
def momentTerm (p b L : ℝ) (n : ℕ) : ℝ :=
  (b * L) ^ n / momentDenominator p n

def compactMoment (p b L : ℝ) : ℝ :=
  ∫ x : ℝ in 0..L, x ^ p * Real.exp (-b * x)

private theorem momentDenominator_pos {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 < momentDenominator p n := by
  apply Finset.prod_pos
  intro j _
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

private theorem momentTerm_nonneg {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) (n : ℕ) : 0 ≤ momentTerm p b L n := by
  exact div_nonneg (pow_nonneg (mul_pos hb hL).le n)
    (momentDenominator_pos hp n).le

private theorem momentTerm_succ (p b L : ℝ) (n : ℕ) :
    momentTerm p b L (n + 1) =
      momentTerm p b L n * (b * L) / (p + (n : ℝ) + 2) := by
  unfold momentTerm momentDenominator
  conv_lhs => rw [Finset.prod_range_succ, pow_succ]
  rw [show p + 1 + ((n + 1 : ℕ) : ℝ) = p + (n : ℝ) + 2 by
    push_cast <;> ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- This is a direct real-valued use of the pinned Mathlib beta evaluation,
not a new beta integral theory. -/
private theorem beta_polynomial_integral {p L : ℝ} (hp : 0 ≤ p)
    (hL : 0 < L) (n : ℕ) :
    (∫ x : ℝ in 0..L, x ^ p * (L - x) ^ n) =
      L ^ (p + (n : ℝ) + 1) * (n.factorial : ℝ) /
        momentDenominator p n := by
  have hu : 0 < ((p : ℂ) + 1).re := by simp <;> linarith
  have hbeta := Complex.betaIntegral_scaled
    ((p : ℂ) + 1) ((n : ℂ) + 1) hL
  rw [Complex.betaIntegral_eval_nat_add_one_right hu n] at hbeta
  have hexponent :
      (p : ℂ) + 1 + ((n : ℂ) + 1) - 1 =
        ((p + (n : ℝ) + 1 : ℝ) : ℂ) := by push_cast <;> ring
  rw [hexponent, ← Complex.ofReal_cpow hL.le] at hbeta
  have hden :
      (∏ j ∈ Finset.range (n + 1), ((p : ℂ) + 1 + (j : ℂ))) =
        (momentDenominator p n : ℂ) := by
    unfold momentDenominator
    push_cast <;> rfl
  rw [hden] at hbeta
  apply Complex.ofReal_injective
  calc
    ((∫ x : ℝ in 0..L, x ^ p * (L - x) ^ n : ℝ) : ℂ) =
        ∫ x : ℝ in 0..L, ((x ^ p * (L - x) ^ n : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal.symm
    _ = ∫ x : ℝ in 0..L,
        (x : ℂ) ^ ((p : ℂ) + 1 - 1) *
          ((L : ℂ) - x) ^ ((n : ℂ) + 1 - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL.le] at hx
      simp only [add_sub_cancel_right, Complex.cpow_natCast]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1 p]
      push_cast <;> rfl
    _ = _ := hbeta
    _ = ((L ^ (p + (n : ℝ) + 1) * (n.factorial : ℝ) /
        momentDenominator p n : ℝ) : ℂ) := by push_cast <;> ring

private theorem integral_series_term {p L : ℝ} (hp : 0 ≤ p)
    (hL : 0 < L) (b : ℝ) (n : ℕ) :
    (∫ x : ℝ in 0..L, x ^ p * (b * (L - x)) ^ n / (n.factorial : ℝ)) =
      L ^ (p + 1) * momentTerm p b L n := by
  have hf : (fun x : ℝ => x ^ p * (b * (L - x)) ^ n / (n.factorial : ℝ)) =
      (fun x : ℝ => (b ^ n / (n.factorial : ℝ)) * (x ^ p * (L - x) ^ n)) := by
    funext x
    rw [mul_pow]
    ring
  rw [hf, intervalIntegral.integral_const_mul, beta_polynomial_integral hp hL n]
  rw [show p + (n : ℝ) + 1 = (p + 1) + (n : ℝ) by ring,
    Real.rpow_add hL, Real.rpow_natCast]
  unfold momentTerm
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hd := (momentDenominator_pos hp n).ne'
  rw [mul_pow]
  field_simp [hn, hd]
  <;> ring

private theorem exp_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t

/-- Genuine integrability, summability, and equality. In particular neither
an expansion nor the value of the target integral is a hypothesis. -/
theorem compactMoment_series {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) :
    IntervalIntegrable (fun x : ℝ => x ^ p * Real.exp (-b * x)) volume 0 L ∧
      Summable (momentTerm p b L) ∧
      compactMoment p b L =
        Real.exp (-b * L) * L ^ (p + 1) * ∑' n : ℕ, momentTerm p b L n := by
  have hcontinuous : Continuous (fun x : ℝ => x ^ p * Real.exp (-b * x)) :=
    (Real.continuous_rpow_const hp).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hF (n : ℕ) : Continuous
      (fun x : ℝ => x ^ p * (b * (L - x)) ^ n / (n.factorial : ℝ)) :=
    ((Real.continuous_rpow_const hp).mul
      ((continuous_const.mul (continuous_const.sub continuous_id)).pow n)).div_const _
  have hmajor : HasSum
      (fun n : ℕ => L ^ p * (b * L) ^ n / (n.factorial : ℝ))
      (L ^ p * Real.exp (b * L)) := by
    simpa only [mul_div_assoc] using (exp_hasSum (b * L)).mul_left (L ^ p)
  have hdom : HasSum
      (fun n : ℕ => ∫ x : ℝ in 0..L,
        x ^ p * (b * (L - x)) ^ n / (n.factorial : ℝ))
      (∫ x : ℝ in 0..L, x ^ p * Real.exp (b * (L - x))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => L ^ p * (b * L) ^ n / (n.factorial : ℝ))
    · intro n
      exact (hF n).aestronglyMeasurable
    · intro n
      filter_upwards with x hx
      rw [uIoc_of_le hL.le] at hx
      have hx0 : 0 ≤ x := hx.1.le
      have hxL : 0 ≤ L - x := sub_nonneg.mpr hx.2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply mul_le_mul (Real.rpow_le_rpow hx0 hx.2 hp) _
        (pow_nonneg (mul_nonneg hb.le hxL) n) (Real.rpow_nonneg hL.le p)
      exact pow_le_pow_left₀ (mul_nonneg hb.le hxL) (by nlinarith) n
    · exact Filter.Eventually.of_forall (fun _ _ => hmajor.summable)
    · simp only [hmajor.tsum_eq]
      exact intervalIntegrable_const
    · filter_upwards with x _
      simpa only [mul_div_assoc] using
        (exp_hasSum (b * (L - x))).mul_left (x ^ p)
  simp_rw [integral_series_term hp hL b] at hdom
  have hc : 0 < L ^ (p + 1) := Real.rpow_pos_of_pos hL _
  have hs : Summable (momentTerm p b L) :=
    (summable_mul_left_iff hc.ne').mp hdom.summable
  have hvalue : (∫ x : ℝ in 0..L, x ^ p * Real.exp (b * (L - x))) =
      L ^ (p + 1) * ∑' n : ℕ, momentTerm p b L n := by
    rw [← hdom.tsum_eq, tsum_mul_left]
  refine ⟨hcontinuous.intervalIntegrable _ _, hs, ?_⟩
  unfold compactMoment
  calc
    (∫ x : ℝ in 0..L, x ^ p * Real.exp (-b * x)) =
        Real.exp (-b * L) *
          ∫ x : ℝ in 0..L, x ^ p * Real.exp (b * (L - x)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      have he : Real.exp (-b * x) =
          Real.exp (-b * L) * Real.exp (b * (L - x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change x ^ p * Real.exp (-b * x) =
        Real.exp (-b * L) * (x ^ p * Real.exp (b * (L - x)))
      rw [he]
      ring
    _ = _ := by rw [hvalue] <;> ring

private theorem series_tail_le {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) (N : ℕ)
    (hq : b * L / (p + (N : ℝ) + 2) < 1) :
    (∑' k : ℕ, momentTerm p b L (k + (N + 1))) ≤
      momentTerm p b L (N + 1) / (1 - b * L / (p + (N : ℝ) + 2)) := by
  let q : ℝ := b * L / (p + (N : ℝ) + 2)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := hq
  have hs := (compactMoment_series hp hb hL).2.1
  have htail : Summable (fun k : ℕ => momentTerm p b L (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 hs
  have hratio (n : ℕ) (hn : N ≤ n) :
      momentTerm p b L (n + 1) ≤ momentTerm p b L n * q := by
    rw [momentTerm_succ, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (momentTerm_nonneg hp hb hL n)
    apply div_le_div_of_nonneg_left (mul_pos hb hL).le (by positivity)
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbound (k : ℕ) : momentTerm p b L (k + (N + 1)) ≤
      momentTerm p b L (N + 1) * q ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        momentTerm p b L (k + 1 + (N + 1)) ≤
            momentTerm p b L (k + (N + 1)) * q := by
          rw [show k + 1 + (N + 1) = (k + (N + 1)) + 1 by omega]
          exact hratio (k + (N + 1)) (by omega)
        _ ≤ (momentTerm p b L (N + 1) * q ^ k) * q :=
          mul_le_mul_of_nonneg_right ih hq0
        _ = _ := by rw [pow_succ] <;> ring
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (momentTerm p b L (N + 1))
  calc
    (∑' k : ℕ, momentTerm p b L (k + (N + 1))) ≤
        ∑' k : ℕ, momentTerm p b L (N + 1) * q ^ k :=
      htail.tsum_le_tsum hbound hgeo.summable
    _ = _ := by rw [hgeo.tsum_eq] <;> simp only [q, div_eq_mul_inv]

/-- Positivity gives a lower bound for every prefix, without a ratio test. -/
theorem compactMoment_prefix_lower {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) (N : ℕ) :
    (Real.exp (-b * L) * L ^ (p + 1)) *
      (∑ n ∈ Finset.range (N + 1), momentTerm p b L n) ≤ compactMoment p b L := by
  obtain ⟨_, hs, hv⟩ := compactMoment_series hp hb hL
  have hc : 0 ≤ Real.exp (-b * L) * L ^ (p + 1) := by positivity
  rw [hv]
  apply mul_le_mul_of_nonneg_left _ hc
  exact hs.sum_le_tsum (Finset.range (N + 1))
    (fun n _ => momentTerm_nonneg hp hb hL n)

/-- Prefix includes n = N. The first omitted term is a_(N+1).
The q here is slightly conservative: every subsequent ratio is at most q. -/
theorem compactMoment_prefix_bounds {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) (N : ℕ)
    (hq : b * L / (p + (N : ℝ) + 2) < 1) :
    let c := Real.exp (-b * L) * L ^ (p + 1)
    let s := ∑ n ∈ Finset.range (N + 1), momentTerm p b L n
    c * s ≤ compactMoment p b L ∧
      compactMoment p b L ≤ c * (s + momentTerm p b L (N + 1) /
        (1 - b * L / (p + (N : ℝ) + 2))) := by
  dsimp only
  obtain ⟨_, hs, hv⟩ := compactMoment_series hp hb hL
  have hc : 0 ≤ Real.exp (-b * L) * L ^ (p + 1) := by positivity
  refine ⟨compactMoment_prefix_lower hp hb hL N, ?_⟩
  rw [hv]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [← hs.sum_add_tsum_nat_add (N + 1)]
  exact add_le_add le_rfl (series_tail_le hp hb hL N hq)

/-- Integration by parts expressed by the derivative of x^(p+1) exp(-b x).
For p >= 0 the derivative also exists at zero, so the endpoint causes no
improper-integral convention or unproved limiting step. -/
private theorem compactMoment_step {p b L : ℝ} (hp : 0 ≤ p)
    (hb : 0 < b) (hL : 0 < L) :
    b * compactMoment (p + 1) b L = (p + 1) * compactMoment p b L -
      L ^ (p + 1) * Real.exp (-b * L) := by
  have hi := (compactMoment_series hp hb hL).1
  have hi' := (compactMoment_series (p := p + 1) (by linarith) hb hL).1
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => y ^ (p + 1) * Real.exp (-b * y))
      ((p + 1) * (x ^ p * Real.exp (-b * x)) -
        b * (x ^ (p + 1) * Real.exp (-b * x))) x := by
    have hx := Real.hasDerivAt_rpow_const (x := x) (p := p + 1)
      (Or.inr (by linarith : 1 ≤ p + 1))
    have he : HasDerivAt (fun y : ℝ => Real.exp (-b * y))
        (Real.exp (-b * x) * (-b)) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (-b)).exp
    rw [show p + 1 - 1 = p by ring] at hx
    convert hx.mul he using 1 <;> first | rfl | ring
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := L) (fun x _ => hd x) ((hi.const_mul (p + 1)).sub (hi'.const_mul b))
  rw [intervalIntegral.integral_sub (hi.const_mul (p + 1)) (hi'.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hft
  have hzero : (0 : ℝ) ^ (p + 1) = 0 := Real.zero_rpow (by linarith)
  simp only [hzero, zero_mul, sub_zero] at hft
  change (p + 1) * compactMoment p b L - b * compactMoment (p + 1) b L = _ at hft
  linear_combination -hft

/-- Actual half moments used in the signed multiplier contractions. -/
def H (m : ℕ) : ℝ := compactMoment ((m : ℝ) + 11 / 2) 2 6

/-- H_0 is supplied by the analytic series, with genuine integrability.
There is no numerical interval hypothesis in this declaration. -/
theorem H0_series :
    IntervalIntegrable (fun x : ℝ => x ^ (11 / 2 : ℝ) * Real.exp (-2 * x))
      volume 0 6 ∧
    Summable (momentTerm (11 / 2) 2 6) ∧
    H 0 = Real.exp (-12) * (6 : ℝ) ^ (13 / 2 : ℝ) *
      ∑' n : ℕ, (12 : ℝ) ^ n /
        (∏ j ∈ Finset.range (n + 1), (13 / 2 + (j : ℝ))) := by
  simpa only [H, Nat.cast_zero, zero_add, momentTerm, momentDenominator,
    show (2 : ℝ) * 6 = 12 by norm_num,
    show -(2 : ℝ) * 6 = -12 by norm_num,
    show (11 / 2 : ℝ) + 1 = 13 / 2 by norm_num] using
    (compactMoment_series (p := (11 / 2 : ℝ)) (b := 2) (L := 6)
      (by norm_num) (by norm_num) (by norm_num))

/-- Higher half moments use the same actual integral domain as H_0. -/
theorem H_integrable (m : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ ((m : ℝ) + 11 / 2) * Real.exp (-2 * x))
      volume 0 6 := by
  exact (compactMoment_series (p := (m : ℝ) + 11 / 2) (b := 2) (L := 6)
    (by positivity) (by norm_num) (by norm_num)).1

/-- The actual IBP recurrence used after the H_0 supplier. -/
theorem H_succ (m : ℕ) :
    H (m + 1) = ((m : ℝ) + 13 / 2) / 2 * H m -
      (6 : ℝ) ^ ((m : ℝ) + 13 / 2) * Real.exp (-12) / 2 := by
  have h := compactMoment_step (p := (m : ℝ) + 11 / 2) (b := 2) (L := 6)
    (by positivity) (by norm_num) (by norm_num)
  have he : (m : ℝ) + 11 / 2 + 1 = (m : ℝ) + 13 / 2 := by ring
  have he' : ((m + 1 : ℕ) : ℝ) + 11 / 2 = (m : ℝ) + 13 / 2 := by
    push_cast <;> ring
  change compactMoment (((m + 1 : ℕ) : ℝ) + 11 / 2) 2 6 = _
  rw [he']
  rw [he] at h
  norm_num only [show -(2 : ℝ) * 6 = -12 by norm_num] at h
  change 2 * compactMoment ((m : ℝ) + 13 / 2) 2 6 =
    ((m : ℝ) + 13 / 2) * H m - (6 : ℝ) ^ ((m : ℝ) + 13 / 2) * Real.exp (-12) at h
  linear_combination (1 / 2 : ℝ) * h

/-- Ready for exact rational/exponential interval inputs in a later flight.
Only the analytic reduction is supplied here. -/
theorem H0_prefix_lower (N : ℕ) :
    (Real.exp (-12) * (6 : ℝ) ^ (13 / 2 : ℝ)) *
      (∑ n ∈ Finset.range (N + 1), momentTerm (11 / 2) 2 6 n) ≤ H 0 := by
  simpa only [H, Nat.cast_zero, zero_add,
    show -(2 : ℝ) * 6 = -12 by norm_num,
    show (11 / 2 : ℝ) + 1 = 13 / 2 by norm_num] using
    (compactMoment_prefix_lower (p := (11 / 2 : ℝ)) (b := 2) (L := 6)
      (by norm_num) (by norm_num) (by norm_num) N)

theorem H0_prefix_bounds (N : ℕ) (hN : 12 / ((N : ℝ) + 15 / 2) < 1) :
    let c := Real.exp (-12) * (6 : ℝ) ^ (13 / 2 : ℝ)
    let s := ∑ n ∈ Finset.range (N + 1), momentTerm (11 / 2) 2 6 n
    c * s ≤ H 0 ∧ H 0 ≤ c * (s + momentTerm (11 / 2) 2 6 (N + 1) /
      (1 - 12 / ((N : ℝ) + 15 / 2))) := by
  have hq : (2 : ℝ) * 6 / (11 / 2 + (N : ℝ) + 2) < 1 := by
    simpa only [show (2 : ℝ) * 6 = 12 by norm_num,
      show (11 / 2 : ℝ) + (N : ℝ) + 2 = (N : ℝ) + 15 / 2 by ring] using hN
  simpa [H, show (11 / 2 : ℝ) + 1 = 13 / 2 by norm_num,
    show (2 : ℝ) * 6 = 12 by norm_num,
    show -(2 : ℝ) * 6 = -12 by norm_num,
    show (11 / 2 : ℝ) + (N : ℝ) + 2 = (N : ℝ) + 15 / 2 by ring] using
    (compactMoment_prefix_bounds (p := (11 / 2 : ℝ)) (b := 2) (L := 6)
      (by norm_num) (by norm_num) (by norm_num) N hq)

end FiniteGaussianCap475
