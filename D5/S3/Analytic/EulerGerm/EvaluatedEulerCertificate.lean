/- GID: D5/S3/Analytic/EulerGerm/EvaluatedEulerCertificate
   generality: G
   mirror-B: D5/B/S3/Analytic/EulerGerm/EvaluatedEulerCertificate
   mirror-E: none(waiver:symbolic-uniform-estimate)
   anchors: []
   utility: none
   digest: Finite algebraic Euler cancellation certificates give uniform analytic prime remainders. -/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
A finite algebraic certificate separates coefficient elimination from analytic
evaluation. Its identity is imposed for all complex coordinate vectors, before
weights, halfplanes, primes, and perturbations are chosen. The theorem below
does not construct the certificate or assert all-order Euler extraction.
-/

namespace D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate

noncomputable section

open Finset Complex

variable {J I T : Type} [Fintype J] [Fintype I] [Fintype T]

/-- An ordinary monomial, including the zero multiindex. -/
def monomialValue (n : J → ℕ) (z : J → ℂ) : ℂ := ∏ j, z j ^ n j

/-- Finite algebraic data; repeated correction modes and tail modes are allowed. -/
structure Data (J I T : Type) [Fintype J] [Fintype I] [Fintype T] where
  linear : J → ℤ
  mode : I → J → ℕ
  power : I → ℤ
  tailMode : T → J → ℕ
  tailCoeff : T → ℤ

def Data.numerator (d : Data J I T) (z : J → ℂ) : ℂ :=
  ∏ i, (1 - monomialValue (d.mode i) z) ^ (d.power i).toNat

def Data.denominator (d : Data J I T) (z : J → ℂ) : ℂ :=
  ∏ i, (1 - monomialValue (d.mode i) z) ^ (-d.power i).toNat

def Data.tail (d : Data J I T) (z : J → ℂ) : ℂ :=
  ∑ t, (d.tailCoeff t : ℂ) * monomialValue (d.tailMode t) z

/-- An equality of finite algebraic expressions, without analytic parameters. -/
def Data.Certificate (d : Data J I T) : Prop :=
  ∀ z : J → ℂ,
    (1 + ∑ j, (d.linear j : ℂ) * z j) * d.numerator z =
      d.denominator z + d.tail z

def point (b : J → ℝ) (p : Nat.Primes) (s : ℂ) : J → ℂ :=
  fun j => Complex.exp (-(b j : ℂ) * s * (Real.log (p : ℝ) : ℂ))

def Data.corrected (d : Data J I T) (b : J → ℝ)
    (R : Nat.Primes → ℂ → ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 + ∑ j, (d.linear j : ℂ) * point b p s j + R p s) *
    ∏ i, (1 - monomialValue (d.mode i) (point b p s)) ^ d.power i

private theorem monomial_point (n : J → ℕ) (b : J → ℝ)
    (p : Nat.Primes) (s : ℂ) :
    monomialValue n (point b p s) =
      Complex.exp (-((∑ j, (n j : ℝ) * b j : ℝ) : ℂ) * s *
        (Real.log (p : ℝ) : ℂ)) := by
  simp only [monomialValue, point, ← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Finset.sum_mul, neg_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem monomial_norm_le (n : J → ℕ) (b : J → ℝ)
    (p : Nat.Primes) (s : ℂ) (m ε : ℝ)
    (hm : 0 < m) (hb : ∀ j, m ≤ b j) (hε : 0 < ε)
    (hs : ε < s.re) (hn : 1 ≤ ∑ j, n j) :
    ‖monomialValue n (point b p s)‖ ≤ Real.exp (-m * ε * Real.log 2) := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp
  have hdeg : (1 : ℝ) ≤ ∑ j, (n j : ℝ) := by exact_mod_cast hn
  have hw : m ≤ ∑ j, (n j : ℝ) * b j := by
    calc
      m ≤ (∑ j, (n j : ℝ)) * m := by nlinarith
      _ = ∑ j, (n j : ℝ) * m := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)
  rw [monomial_point, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, Complex.neg_im, mul_zero]
  apply Real.exp_le_exp.mpr
  have hprod := mul_le_mul hw hs.le (le_of_lt hε) (le_of_lt (hm.trans_le hw))
  have hw0 : 0 ≤ ∑ j, (n j : ℝ) * b j := hm.le.trans hw
  have hs0 : 0 ≤ s.re := hε.le.trans hs.le
  have hprod' := mul_le_mul hprod hlp hl.le (mul_nonneg hw0 hs0)
  nlinarith

private theorem tail_monomial_norm_le (n : J → ℕ) (b : J → ℝ)
    (p : Nat.Primes) (s : ℂ) (m ε : ℝ) (N : ℕ)
    (hm : 0 < m) (hb : ∀ j, m ≤ b j) (hε : 0 < ε)
    (hs : ε < s.re) (hn : N + 1 ≤ ∑ j, n j)
    (hcut : 2 ≤ (N + 1 : ℝ) * ε * m) :
    ‖monomialValue n (point b p s)‖ ≤ 1 / (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hdeg : (N + 1 : ℝ) ≤ ∑ j, (n j : ℝ) := by exact_mod_cast hn
  have hw : (N + 1 : ℝ) * m ≤ ∑ j, (n j : ℝ) * b j := by
    calc
      _ ≤ (∑ j, (n j : ℝ)) * m := mul_le_mul_of_nonneg_right hdeg hm.le
      _ = ∑ j, (n j : ℝ) * m := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)
  have hw0 : 0 ≤ ∑ j, (n j : ℝ) * b j := le_trans (by positivity) hw
  have hh : 2 ≤ (∑ j, (n j : ℝ) * b j) * s.re := by
    have := mul_le_mul hw hs.le hε.le hw0
    nlinarith
  rw [monomial_point, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, Complex.neg_im, mul_zero]
  calc
    _ ≤ Real.exp (-(2 * Real.log (p : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hh hlp]
    _ = 1 / (p : ℝ) ^ 2 := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log (p : ℝ) =
        (2 : ℕ) * Real.log (p : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hp]
      simp

private theorem integer_power_split (z : ℂ) (k : ℤ) :
    z ^ k = z ^ k.toNat / z ^ (-k).toNat := by
  cases k with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc]

/-- A finite algebraic cancellation certificate with a total-degree gap gives
one constant for the entire perturbation family on the whole open halfplane.
The positive lower weight `m` can be the minimum of any finite nonempty family.
No restriction is imposed on equality in the cutoff or on repeated weights. -/
theorem evaluated_certificate_uniform (d : Data J I T) (N : ℕ)
    (hcert : d.Certificate)
    (hmode : ∀ i, 1 ≤ ∑ j, d.mode i j)
    (htail : ∀ t, N + 1 ≤ ∑ j, d.tailMode t j)
    (b : J → ℝ) (m ε A : ℝ) (hm : 0 < m) (hb : ∀ j, m ≤ b j)
    (hε : 0 < ε) (hA : 0 ≤ A) (hcut : 2 ≤ (N + 1 : ℝ) * ε * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : Nat.Primes → ℂ → ℂ,
      (∀ p, AnalyticOnNhd ℂ (R p) {s : ℂ | ε < s.re}) →
      (∀ p s, ε < s.re → ‖R p s‖ ≤ A / (p : ℝ) ^ 2) →
      ∀ p, AnalyticOnNhd ℂ (d.corrected b R p) {s : ℂ | ε < s.re} ∧
        ∀ s, ε < s.re → ‖d.corrected b R p s - 1‖ ≤ C / (p : ℝ) ^ 2 := by
  classical
  let q := Real.exp (-m * ε * Real.log 2)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [mul_pos hm hε]
  let U : ℝ := ∏ i, (1 + q) ^ (d.power i).toNat
  let V : ℝ := ∏ i, (1 - q) ^ (-d.power i).toNat
  let D : ℝ := ∑ t, ‖(d.tailCoeff t : ℂ)‖
  have hU : 0 ≤ U := Finset.prod_nonneg fun i _ => by positivity
  have hV : 0 < V := Finset.prod_pos fun i _ => pow_pos (by linarith) _
  have hD : 0 ≤ D := Finset.sum_nonneg fun t _ => norm_nonneg _
  refine ⟨(D + A * U) / V, by positivity, ?_⟩
  intro R hR hbound p
  have hsmall (s : ℂ) (hs : ε < s.re) (i : I) :
      ‖monomialValue (d.mode i) (point b p s)‖ ≤ q :=
    monomial_norm_le _ _ _ _ _ _ hm hb hε hs (hmode i)
  have hne (s : ℂ) (hs : ε < s.re) (i : I) :
      1 - monomialValue (d.mode i) (point b p s) ≠ 0 := by
    intro hz
    have heq : monomialValue (d.mode i) (point b p s) = 1 := sub_eq_zero.mp hz |>.symm
    have := hsmall s hs i
    rw [heq, norm_one] at this
    linarith
  have hmonoAnalytic (n : J → ℕ) :
      AnalyticOnNhd ℂ (fun s => monomialValue n (point b p s)) {s : ℂ | ε < s.re} := by
    intro s hs
    apply Finset.analyticAt_fun_prod
    intro j _
    apply AnalyticAt.pow
    apply AnalyticAt.cexp'
    exact ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)
  constructor
  · apply AnalyticOnNhd.mul
    · exact (analyticOnNhd_const.add (Finset.analyticOnNhd_fun_sum _ fun j _ =>
        analyticOnNhd_const.mul (by
          intro s hs
          exact ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).cexp'))).add (hR p)
    · apply Finset.analyticOnNhd_fun_prod
      intro i _
      exact (analyticOnNhd_const.sub (hmonoAnalytic (d.mode i))).zpow (fun s hs => hne s hs i)
  · intro s hs
    have hnum : ‖d.numerator (point b p s)‖ ≤ U := by
      rw [Data.numerator, norm_prod]
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        rw [norm_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (hsmall s hs i) 1)
    have hden : V ≤ ‖d.denominator (point b p s)‖ := by
      rw [Data.denominator, norm_prod]
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        rw [norm_pow]
        apply pow_le_pow_left₀ (by linarith : 0 ≤ 1 - q)
        have := norm_sub_norm_le (1 : ℂ) (monomialValue (d.mode i) (point b p s))
        simp only [norm_one] at this
        linarith [hsmall s hs i]
    have hden0 : d.denominator (point b p s) ≠ 0 :=
      norm_pos_iff.mp (hV.trans_le hden)
    have htailbound : ‖d.tail (point b p s)‖ ≤ D / (p : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ t, ‖(d.tailCoeff t : ℂ) * monomialValue (d.tailMode t) (point b p s)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ t, ‖(d.tailCoeff t : ℂ)‖ * (1 / (p : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro t _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (tail_monomial_norm_le _ _ _ _ _ _ _ hm hb hε hs (htail t) hcut) (norm_nonneg _)
        _ = D / (p : ℝ) ^ 2 := by simp only [D, mul_one_div, Finset.sum_div]
    have hsplit : (∏ i, (1 - monomialValue (d.mode i) (point b p s)) ^ d.power i) =
        d.numerator (point b p s) / d.denominator (point b p s) := by
      simp only [integer_power_split, Finset.prod_div_distrib, Data.numerator, Data.denominator]
    have hid : d.corrected b R p s - 1 =
        (d.tail (point b p s) + R p s * d.numerator (point b p s)) /
          d.denominator (point b p s) := by
      rw [Data.corrected, hsplit]
      have hc := hcert (point b p s)
      field_simp
      linear_combination hc
    rw [hid, norm_div]
    have hp0 : (0 : ℝ) < (p : ℝ) ^ 2 := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
      positivity
    calc
      _ ≤ (D / (p : ℝ) ^ 2 + (A / (p : ℝ) ^ 2) * U) / V := by
        apply div_le_div₀ (by positivity) _ hV hden
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add htailbound (mul_le_mul (hbound p s hs) hnum (norm_nonneg _) (by positivity))
      _ = ((D + A * U) / V) / (p : ℝ) ^ 2 := by ring

end

end D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
