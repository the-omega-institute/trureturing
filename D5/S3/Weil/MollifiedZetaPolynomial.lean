/- GID: D5/S3/Weil/MollifiedZetaPolynomial
   generality: G
   mirror-B: D5/B/S3/Weil/MollifiedZetaPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Möbius mollifier cancels the initial coefficients of the zeta polynomial. -/

import D5.S3.Arith.Divisors.DivisorSubpower
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Finite Möbius convolution for the mollified zeta function -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.MollifiedZetaPolynomial

open Finset
open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

/-- A Dirichlet polynomial with natural indices in a prescribed finite set. -/
def dirichletPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n / (n : ℂ) ^ s

/-- The ordinary zeta sum through index `N`. -/
def zetaPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  dirichletPolynomial (Icc 1 N) (fun _ => 1) s

/-- The Möbius Dirichlet polynomial through index `X`. -/
def mollifier (X : ℕ) (s : ℂ) : ℂ :=
  dirichletPolynomial (Icc 1 X) (fun d => (μ d : ℂ)) s

/-- The convolution coefficient for the two cutoffs. -/
def coeff (N X n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N), μ d

/-- The part of the mollified zeta sum above the Möbius cutoff. -/
def tailPolynomial (N X : ℕ) (s : ℂ) : ℂ :=
  dirichletPolynomial (Ioc X (N * X)) (fun n => (coeff N X n : ℂ)) s

private def cutoff (A : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Icc 1 A then a n else 0

private theorem hasSum_cutoff (A : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    LSeriesHasSum (cutoff A a) s (dirichletPolynomial (Icc 1 A) a s) := by
  have hsum :
      (∑ n ∈ Icc 1 A, LSeries.term (cutoff A a) s n) =
        dirichletPolynomial (Icc 1 A) a s := by
    unfold dirichletPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt ((Finset.mem_Icc.mp hn).1)
    rw [LSeries.term_of_ne_zero hn0, cutoff, if_pos hn]
  change HasSum (LSeries.term (cutoff A a) s) _
  rw [← hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp [LSeries.term_of_ne_zero hn0, cutoff, hn]

private theorem cutoff_convolution (N X n : ℕ) :
    (cutoff X (fun d => (μ d : ℂ)) ⍟ cutoff N (fun _ => 1)) n =
      (coeff N X n : ℂ) := by
  rw [LSeries.convolution_def, coeff, Int.cast_sum, Finset.sum_filter]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal
    (fun d q => cutoff X (fun d => (μ d : ℂ)) d * cutoff N (fun _ => 1) q)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hqpos : 1 ≤ n / d := Nat.div_pos (Nat.divisor_le hd) hdpos
  simp only [cutoff, Finset.mem_Icc, hdpos, hqpos, true_and]
  by_cases hdX : d ≤ X <;> by_cases hqN : n / d ≤ N <;> simp [hdX, hqN]

private theorem coeff_of_le {N X n : ℕ} (hXN : X ≤ N) (hnX : n ≤ X) :
    coeff N X n = if n = 1 then 1 else 0 := by
  have hfilter : n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N) = n.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact ⟨(Nat.divisor_le hd).trans hnX, (Nat.div_le_self n d).trans (hnX.trans hXN)⟩
  rw [coeff, hfilter, ← ArithmeticFunction.coe_mul_zeta_apply (f := μ),
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

private theorem coeff_eq_zero_of_mul_lt {N X n : ℕ} (hn : N * X < n) :
    coeff N X n = 0 := by
  unfold coeff
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hd, hdX, hqN⟩ := Finset.mem_filter.mp hd
  have hnle : n ≤ N * X := calc
    n = n / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm
    _ ≤ N * X := Nat.mul_le_mul hqN hdX
  exact (not_le_of_gt hn hnle).elim

/-- The truncated product minus its constant term is supported on `X < n ≤ N * X`. -/
theorem zetaPartialSum_mul_mollifier_sub_one {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N)
    (s : ℂ) : zetaPartialSum N s * mollifier X s - 1 = tailPolynomial N X s := by
  let f : ℕ → ℂ := cutoff X (fun d => (μ d : ℂ))
  let g : ℕ → ℂ := cutoff N (fun _ => 1)
  let S : Finset ℕ := insert 1 (Ioc X (N * X))
  have hc (n : ℕ) : (f ⍟ g) n = (coeff N X n : ℂ) := cutoff_convolution N X n
  have hzero : ∀ n ∉ S, LSeries.term (f ⍟ g) s n = 0 := by
    intro n hn
    have hn1 : n ≠ 1 := fun h => hn (by simp [S, h])
    have hntail : n ∉ Ioc X (N * X) := fun h => hn (by simp [S, h])
    have hb : coeff N X n = 0 := by
      by_cases hnX : n ≤ X
      · rw [coeff_of_le hXN hnX, if_neg hn1]
      · have hlarge : N * X < n :=
          lt_of_not_ge fun h => hntail (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnX, h⟩)
        exact coeff_eq_zero_of_mul_lt hlarge
    simp [LSeries.term_def, hc, hb]
  have hhead : (1 : ℕ) ∉ Ioc X (N * X) := fun h =>
    (not_lt_of_ge hX) (Finset.mem_Ioc.mp h).1
  have hone : LSeries.term (f ⍟ g) s 1 = 1 := by
    rw [LSeries.term_of_ne_zero (by decide : (1 : ℕ) ≠ 0), hc, coeff_of_le hXN hX]
    simp
  have hfin : (∑ n ∈ S, LSeries.term (f ⍟ g) s n) = 1 + tailPolynomial N X s := by
    change (∑ n ∈ insert 1 (Ioc X (N * X)), LSeries.term (f ⍟ g) s n) = _
    rw [Finset.sum_insert hhead, hone, tailPolynomial, dirichletPolynomial]
    apply congrArg (fun z : ℂ => 1 + z)
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt ((Nat.zero_le X).trans_lt (Finset.mem_Ioc.mp hn).1)
    rw [LSeries.term_of_ne_zero hn0, hc]
  have hprod : HasSum (LSeries.term (f ⍟ g) s) (mollifier X s * zetaPartialSum N s) :=
    (hasSum_cutoff X (fun d => (μ d : ℂ)) s).convolution (hasSum_cutoff N (fun _ => 1) s)
  have hvalue := HasSum.unique hprod (hasSum_sum_of_ne_finset_zero hzero)
  rw [hfin] at hvalue
  calc
    zetaPartialSum N s * mollifier X s - 1 = (1 + tailPolynomial N X s) - 1 := by
      rw [mul_comm (zetaPartialSum N s), hvalue]
    _ = tailPolynomial N X s := by ring

/-- Each truncated Möbius convolution coefficient is bounded by the divisor count. -/
theorem abs_coeff_le_divisors_card (N X n : ℕ) :
    |coeff N X n| ≤ (n.divisors.card : ℤ) := by
  let S := n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N)
  calc
    |coeff N X n| = |∑ d ∈ S, μ d| := rfl
    _ ≤ ∑ d ∈ S, |μ d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, (1 : ℤ) := Finset.sum_le_sum fun _ _ =>
      ArithmeticFunction.abs_moebius_le_one
    _ = (S.card : ℤ) := by simp
    _ ≤ (n.divisors.card : ℤ) := by
      exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ X ∧ n / d ≤ N)

/-- The coefficient bound with a constant uniform in both truncation lengths. -/
theorem norm_coeff_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N X n : ℕ, n ≠ 0 →
      ‖(coeff N X n : ℂ)‖ ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hDiv⟩ :=
    D5.S3.Arith.Divisors.DivisorSubpower.card_divisors_subpower ε hε
  refine ⟨C, hC, fun N X n hn => ?_⟩
  apply le_trans _ (hDiv n hn)
  rw [Complex.norm_intCast]
  exact_mod_cast abs_coeff_le_divisors_card N X n

/-- Every term of the Möbius polynomial has norm at most one on the closed right half-plane. -/
private theorem norm_mollifier_term_le_one {s : ℂ} (hs : 0 ≤ s.re) {d : ℕ}
    (hd : 1 ≤ d) : ‖(μ d : ℂ) / (d : ℂ) ^ s‖ ≤ 1 := by
  have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow := Real.one_le_rpow hdR hs
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hd]
  exact (div_le_one₀ (zero_lt_one.trans_le hpow)).mpr (hμ.trans hpow)

/-- The pointwise bound `|M_X(s)| ≤ X` for `0 ≤ re s`, including the imaginary axis. -/
theorem norm_mollifier_le (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mollifier X s‖ ≤ (X : ℝ) := by
  unfold mollifier dirichletPolynomial
  calc
    ‖∑ d ∈ Icc 1 X, (μ d : ℂ) / (d : ℂ) ^ s‖ ≤
        ∑ d ∈ Icc 1 X, ‖(μ d : ℂ) / (d : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Icc 1 X, (1 : ℝ) := Finset.sum_le_sum fun _ hd =>
      norm_mollifier_term_le_one hs (Finset.mem_Icc.mp hd).1
    _ = (X : ℝ) := by simp

/-- The mollified zeta approximation error is at most `X` times the zeta truncation error. -/
theorem norm_mollifiedZeta_sub_tail_le {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖riemannZeta s * mollifier X s - 1 - tailPolynomial N X s‖ ≤
      (X : ℝ) * ‖riemannZeta s - zetaPartialSum N s‖ := by
  rw [← zetaPartialSum_mul_mollifier_sub_one hX hXN s]
  have herror : riemannZeta s * mollifier X s - 1 -
      (zetaPartialSum N s * mollifier X s - 1) =
        (riemannZeta s - zetaPartialSum N s) * mollifier X s := by ring
  rw [herror, norm_mul, mul_comm (‖riemannZeta s - zetaPartialSum N s‖)]
  exact mul_le_mul_of_nonneg_right (norm_mollifier_le X hs) (norm_nonneg _)

private theorem continuous_dirichletPolynomial {S : Finset ℕ} (hS : ∀ n ∈ S, n ≠ 0)
    (a : ℕ → ℂ) : Continuous (dirichletPolynomial S a) := by
  unfold dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hS n hn
  exact continuous_const.div (continuous_const_cpow' hn0)
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

/-- The actual mollified zeta mean square is bounded by the polynomial mean square and
the zeta truncation mean square. The segment avoids the pole at `s = 1`. -/
theorem integral_norm_mollifiedZeta_sub_one_sq_le {N X : ℕ}
    (hX : 1 ≤ X) (hXN : X ≤ N) {u a b : ℝ} (hu : 0 ≤ u) (hab : a ≤ b)
    (hNoPole : ∀ t ∈ Set.Icc a b, (u : ℂ) + (t : ℂ) * Complex.I ≠ 1) :
    (∫ t in a..b, ‖riemannZeta ((u : ℂ) + (t : ℂ) * Complex.I) *
          mollifier X ((u : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2) ≤
      2 * (∫ t in a..b, ‖tailPolynomial N X ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) +
      (2 * (X : ℝ) ^ 2) * (∫ t in a..b, ‖riemannZeta ((u : ℂ) + (t : ℂ) * Complex.I) -
        zetaPartialSum N ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  let z (t : ℝ) : ℂ := (u : ℂ) + (t : ℂ) * Complex.I
  let F (t : ℝ) : ℂ := riemannZeta (z t) * mollifier X (z t) - 1
  let P (t : ℝ) : ℂ := tailPolynomial N X (z t)
  let E (t : ℝ) : ℂ := riemannZeta (z t) - zetaPartialSum N (z t)
  change (∫ t in a..b, ‖F t‖ ^ 2) ≤
    2 * (∫ t in a..b, ‖P t‖ ^ 2) + (2 * (X : ℝ) ^ 2) * (∫ t in a..b, ‖E t‖ ^ 2)
  have hz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hZ : ContinuousOn (fun t => riemannZeta (z t)) (Set.Icc a b) := by
    intro t ht
    have hζ : ContinuousAt riemannZeta (z t) :=
      (differentiableAt_riemannZeta (hNoPole t ht)).continuousAt
    exact (hζ.comp (hz.continuousAt (x := t))).continuousWithinAt
  have hpos (A : ℕ) (n : ℕ) (hn : n ∈ Icc 1 A) : n ≠ 0 :=
    ne_of_gt (Finset.mem_Icc.mp hn).1
  have hM : Continuous (fun t => mollifier X (z t)) :=
    (continuous_dirichletPolynomial (hpos X) (fun d => (μ d : ℂ))).comp hz
  have hD : Continuous (fun t => zetaPartialSum N (z t)) :=
    (continuous_dirichletPolynomial (hpos N) (fun _ => 1)).comp hz
  have hP : Continuous P :=
    (continuous_dirichletPolynomial (S := Ioc X (N * X))
      (fun n hn => ne_of_gt ((Nat.zero_le X).trans_lt (Finset.mem_Ioc.mp hn).1))
      (fun n => (coeff N X n : ℂ))).comp hz
  have hF : ContinuousOn F (Set.Icc a b) := (hZ.mul hM.continuousOn).sub continuousOn_const
  have hE : ContinuousOn E (Set.Icc a b) := hZ.sub hD.continuousOn
  have hFi : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume a b :=
    (hF.norm.pow 2).intervalIntegrable_of_Icc hab
  have hEi : IntervalIntegrable (fun t => ‖E t‖ ^ 2) volume a b :=
    (hE.norm.pow 2).intervalIntegrable_of_Icc hab
  have hPi : IntervalIntegrable (fun t => ‖P t‖ ^ 2) volume a b :=
    (hP.norm.pow 2).intervalIntegrable a b
  have hpoint (t : ℝ) (_ : t ∈ Set.Icc a b) :
      ‖F t‖ ^ 2 ≤ 2 * ‖P t‖ ^ 2 + (2 * (X : ℝ) ^ 2) * ‖E t‖ ^ 2 := by
    have hRe : 0 ≤ (z t).re := by simpa [z, Complex.add_re, Complex.mul_re] using hu
    have hdiff : ‖F t - P t‖ ≤ (X : ℝ) * ‖E t‖ :=
      norm_mollifiedZeta_sub_tail_le hX hXN hRe
    have htriangle := norm_add_le (F t - P t) (P t)
    rw [sub_add_cancel] at htriangle
    calc
      ‖F t‖ ^ 2 ≤ ((X : ℝ) * ‖E t‖ + ‖P t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (htriangle.trans (add_le_add_left hdiff _)) 2
      _ ≤ _ := by nlinarith only [sq_nonneg ((X : ℝ) * ‖E t‖ - ‖P t‖)]
  have h := intervalIntegral.integral_mono_on hab hFi
    ((hPi.const_mul (2 : ℝ)).add (hEi.const_mul (2 * (X : ℝ) ^ 2))) hpoint
  rw [intervalIntegral.integral_add (hPi.const_mul (2 : ℝ)) (hEi.const_mul (2 * (X : ℝ) ^ 2))] at h
  simpa only [intervalIntegral.integral_const_mul] using h

end D5.S3.Weil.ZetaPntBounds.MollifiedZetaPolynomial
