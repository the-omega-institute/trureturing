/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterShortGapFinite
   generality: S
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Bernstein coefficients for the scalar short-gap series. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.NumberTheory.Bernoulli

/-! # Finite Bernstein certificate for the scalar short-gap series -/

open Finset Polynomial
open scoped Polynomial

namespace RefinedBMV.PositiveCenter.ShortGapFinite

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

private def rangeSum {R : Type*} [AddMonoid R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => rangeSum f n + f n

private theorem rangeSum_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    rangeSum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => rw [rangeSum, ih, sum_range_succ]

private theorem rangeSum_congr {a b : ℕ → ℚ} {n : ℕ}
    (heq : ∀ i < n, a i = b i) : rangeSum a n = rangeSum b n := by
  simp only [rangeSum_eq]
  exact sum_congr rfl fun i hi ↦ heq i (mem_range.mp hi)

private def choose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private theorem choose_eq (n k : ℕ) : choose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- Ascending power coefficients in the variable `y = 11h/3`. -/
abbrev Coefficients := List ℚ

private def add (a b : Coefficients) : Coefficients :=
  List.zipWithAll (fun x y => x.getD 0 + y.getD 0) a b

private def sub (a b : Coefficients) : Coefficients :=
  List.zipWithAll (fun x y => x.getD 0 - y.getD 0) a b

private def scale (c : ℚ) (a : Coefficients) : Coefficients :=
  a.map (c * ·)

private def mul (a b : Coefficients) : Coefficients :=
  match a with
  | [] => []
  | c :: cs => add (scale c b) (0 :: mul cs b)

private def pow (a : Coefficients) : ℕ → Coefficients
  | 0 => [1]
  | n + 1 => mul (pow a n) a

/-- Polynomial represented by the executable ascending coefficient list. -/
noncomputable def polynomial (a : Coefficients) : ℚ[X] := ofCoeffList a

private theorem polynomial_add (a b : Coefficients) :
    polynomial (add a b) = polynomial a + polynomial b :=
  ofCoeffList_zipWithAll_add a b

private theorem polynomial_sub (a b : Coefficients) :
    polynomial (sub a b) = polynomial a - polynomial b :=
  ofCoeffList_zipWithAll_sub a b

private theorem polynomial_scale (c : ℚ) (a : Coefficients) :
    polynomial (scale c a) = C c * polynomial a :=
  ofCoeffList_map_mul c a

private theorem polynomial_mul (a b : Coefficients) :
    polynomial (mul a b) = polynomial a * polynomial b := by
  induction a with
  | nil => simp [mul, polynomial]
  | cons c cs ih =>
    rw [mul, polynomial_add, polynomial_scale, show polynomial (0 :: mul cs b) =
      X * polynomial (mul cs b) from ofCoeffList_zero_cons _, ih]
    simp only [polynomial, ofCoeffList_cons, add_mul, mul_assoc]

private theorem polynomial_pow (a : Coefficients) (n : ℕ) :
    polynomial (pow a n) = polynomial a ^ n := by
  induction n with
  | zero => simp [pow, polynomial, ofCoeffList_cons]
  | succ n ih => rw [pow, polynomial_mul, ih, pow_succ]

private def sumCoeffs (f : ℕ → Coefficients) : ℕ → Coefficients
  | 0 => []
  | n + 1 => add (sumCoeffs f n) (f n)

private theorem polynomial_sum (f : ℕ → Coefficients) (n : ℕ) :
    polynomial (sumCoeffs f n) = ∑ i ∈ range n, polynomial (f i) := by
  induction n with
  | zero => simp [sumCoeffs, polynomial]
  | succ n ih => rw [sumCoeffs, polynomial_add, ih, sum_range_succ]

private def h : Coefficients := [0, 3 / 11]
private def gridSize : Coefficients := [3, 3 / 11]
private def c : Coefficients := scale (1 / 2) (mul gridSize [3, 6 / 11])

/-- The grid moments in the replay's Faulhaber convention `B₁ = 1/2`. -/
def moment : ℕ → Coefficients
  | 0 => gridSize
  | n + 1 =>
    (List.range (n + 2)).map fun k =>
      (choose (n + 2) k : ℚ) * bernoulli' k * 3 ^ (n + 2 - k) *
        (3 / 11 : ℚ) ^ k / (n + 2 : ℕ)

private theorem polynomial_range (f : ℕ → ℚ) (n : ℕ) :
    polynomial ((List.range n).map f) = ∑ k ∈ range n, monomial k (f k) := by
  ext k
  simp only [polynomial, coeff_ofCoeffList, finsetSum_coeff, coeff_monomial]
  by_cases hk : k < n
  · rw [Finset.sum_eq_single_of_mem k (mem_range.mpr hk)]
    · simp [List.getD_eq_getElem?_getD, hk]
    · intro b _ hne
      simp [hne]
  · rw [Finset.sum_eq_zero]
    · simp [List.getD_eq_getElem?_getD, hk]
    · intro b hb
      have hne : b ≠ k := fun h => hk (h ▸ mem_range.mp hb)
      simp [hne]

/-- The moment polynomial uses exactly the replay's power coefficients. -/
theorem moment_succ_polynomial (n : ℕ) :
    polynomial (moment (n + 1)) = ∑ k ∈ range (n + 2),
      monomial k ((Nat.choose (n + 2) k : ℚ) * bernoulli' k * 3 ^ (n + 2 - k) *
        (3 / 11 : ℚ) ^ k / (n + 2 : ℕ)) := by
  simp only [moment, polynomial_range, choose_eq]

/-- At the normalized integer grids the moment polynomial evaluates to the Faulhaber sum. -/
theorem moment_eval_grid {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (polynomial (moment n)).eval (11 / (p : ℚ)) =
      (3 / (p : ℚ)) * ∑ i ∈ range (p + 1), ((3 / (p : ℚ)) * i) ^ n := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  let q : ℚ := 3 / (p : ℚ)
  have hqp : q * p = 3 := div_mul_cancel₀ 3 hpq
  have hq : (3 / 11 : ℚ) * (11 / (p : ℚ)) = q := by dsimp [q]; ring
  cases n with
  | zero =>
    suffices 3 + (3 / 11 : ℚ) * (11 / (p : ℚ)) = q * ((p : ℚ) + 1) by
      simpa [moment, gridSize, polynomial, ofCoeffList_cons, Nat.cast_add] using this
    rw [hq]
    rw [mul_add, hqp, mul_one]
  | succ n =>
    rw [moment_succ_polynomial, eval_finsetSum]
    simp_rw [eval_monomial]
    have hpows : (∑ i ∈ range (p + 1), (q * (i : ℚ)) ^ (n + 1)) =
        q ^ (n + 1) * ∑ i ∈ range (p + 1), (i : ℚ) ^ (n + 1) := by
      simp only [mul_pow, Finset.mul_sum]
    have hsum : (∑ i ∈ Ico 1 (p + 1), (i : ℚ) ^ (n + 1)) =
        ∑ i ∈ range (p + 1), (i : ℚ) ^ (n + 1) := by
      rw [sum_Ico_eq_sub _ (show 1 ≤ p + 1 by omega)]
      simp
    change (∑ k ∈ range (n + 2), _) = q * ∑ i ∈ range (p + 1), (q * (i : ℚ)) ^ (n + 1)
    rw [hpows, ← mul_assoc, ← pow_succ', ← hsum, sum_Ico_pow, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n + 2 := (mem_range.mp hk).le
    have hpow : q ^ (n + 2) * (p : ℚ) ^ (n + 2 - k) = q ^ k * 3 ^ (n + 2 - k) := by
      rw [← hqp, mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hk']
    calc
      _ = (↑((n + 2).choose k) : ℚ) * bernoulli' k * 3 ^ (n + 2 - k) * q ^ k / (n + 2 : ℕ) := by
        rw [← hq, mul_pow]
        ring
      _ = (↑((n + 2).choose k) : ℚ) * bernoulli' k *
          (q ^ k * 3 ^ (n + 2 - k)) / (n + 2 : ℕ) := by ring
      _ = _ := by rw [← hpow]; push_cast; ring

/-- Coefficients of `U` in the coordinate `x = t/2`. -/
def u (n : ℕ) : Coefficients :=
  scale ((2 : ℚ) ^ n / (n + 2).factorial)
    (sub (sub (mul gridSize (moment (n + 2))) (moment (n + 3))) c)

/-- Coefficients of `T` in the coordinate `x = t/2`. -/
def t (n : ℕ) : Coefficients :=
  scale (1 / (n.factorial : ℚ))
    (sub (sumCoeffs (fun k => scale ((choose n k : ℚ) * (-3) ^ (n - k) * 2 ^ k)
      (moment k)) (n + 1)) (scale (1 / 4) (pow (sub [-3] (scale 2 h)) n)))

/-- The marginal coefficients at the integer grid, with their composition weights. -/
theorem u_eval_grid {p : ℕ} (hp : 0 < p) (n : ℕ) :
    let q : ℚ := 3 / (p : ℚ)
    (polynomial (u n)).eval (11 / (p : ℚ)) =
      (2 : ℚ) ^ n / (n + 2).factorial *
        (q * (∑ i ∈ range (p + 1), (3 + q - q * i) * (q * i) ^ (n + 2)) -
          (3 + q) * (3 + 2 * q) / 2) := by
  let q : ℚ := 3 / (p : ℚ)
  let y : ℚ := 11 / (p : ℚ)
  have hsize : (polynomial gridSize).eval y = 3 + q := by
    simp [gridSize, polynomial, ofCoeffList_cons, y, q]
    <;> ring
  have hc : (polynomial c).eval y = (3 + q) * (3 + 2 * q) / 2 := by
    rw [c, polynomial_scale, polynomial_mul, eval_mul, eval_mul, eval_C, hsize]
    simp [polynomial, ofCoeffList_cons, y, q]
    <;> ring
  have hmoment (k : ℕ) : (polynomial (moment k)).eval y =
      q * ∑ i ∈ range (p + 1), (q * i) ^ k := moment_eval_grid hp k
  change (polynomial (u n)).eval y = _
  simp only [u, polynomial_scale, polynomial_sub, polynomial_mul, eval_mul, eval_C, eval_sub,
    hsize, hc, hmoment]
  have hsum :
      (3 + q) * (q * ∑ i ∈ range (p + 1), (q * i) ^ (n + 2)) -
          q * ∑ i ∈ range (p + 1), (q * i) ^ (n + 3) =
        q * ∑ i ∈ range (p + 1), (3 + q - q * i) * (q * i) ^ (n + 2) := by
    have hnext : (∑ i ∈ range (p + 1), (q * i) ^ (n + 3)) =
        ∑ i ∈ range (p + 1), (q * i) * (q * i) ^ (n + 2) :=
      Finset.sum_congr rfl fun i _ ↦ pow_succ' (q * i) (n + 2)
    rw [hnext]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]

/-- The geometric coefficients at the integer grid, in the coordinate `x = t/2`. -/
theorem t_eval_grid {p : ℕ} (hp : 0 < p) (n : ℕ) :
    let q : ℚ := 3 / (p : ℚ)
    (polynomial (t n)).eval (11 / (p : ℚ)) =
      (q * (∑ i ∈ range (p + 1), (2 * (q * i) - 3) ^ n) -
        (-3 - 2 * q) ^ n / 4) / n.factorial := by
  let q : ℚ := 3 / (p : ℚ)
  let y : ℚ := 11 / (p : ℚ)
  have hspacing : (polynomial h).eval y = q := by
    simp [h, polynomial, ofCoeffList_cons, y, q]
    <;> ring
  have hconstant : (polynomial [-3]).eval y = -3 := by
    simp [polynomial, ofCoeffList_cons]
  have hmoment (k : ℕ) : (polynomial (moment k)).eval y =
      q * ∑ i ∈ range (p + 1), (q * i) ^ k := moment_eval_grid hp k
  change (polynomial (t n)).eval y = _
  simp only [t, polynomial_scale, polynomial_sub, polynomial_sum, polynomial_pow, eval_mul,
    eval_C, eval_sub, eval_finsetSum, eval_pow, hconstant, hspacing, choose_eq, hmoment]
  have hsum :
      (∑ k ∈ range (n + 1), (n.choose k : ℚ) * (-3) ^ (n - k) * 2 ^ k *
          (q * ∑ i ∈ range (p + 1), (q * i) ^ k)) =
        q * ∑ i ∈ range (p + 1), (2 * (q * i) - 3) ^ n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_pow]
    ring
  rw [hsum]
  ring

/-- Ordinary coefficient convolution in `x`. -/
def product (a b : ℕ → Coefficients) (n : ℕ) : Coefficients :=
  sumCoeffs (fun k => mul (a k) (b (n - k))) (n + 1)

theorem product_polynomial (a b : ℕ → Coefficients) (n : ℕ) :
    polynomial (product a b n) =
      ∑ k ∈ range (n + 1), polynomial (a k) * polynomial (b (n - k)) := by
  simp only [product, polynomial_sum, polynomial_mul]

private def derivative (a : ℕ → Coefficients) (order n : ℕ) : Coefficients :=
  scale (((n + order).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ order)) (a (n + order))

/-- The Bernstein coefficient of a given degree, with power coefficients padded by zero. -/
def bernstein (a : Coefficients) (degree i : ℕ) : ℚ :=
  rangeSum (fun k => a.getD k 0 * (choose i k : ℚ) / (choose degree k : ℚ)) (degree + 1)

theorem bernstein_eq (a : Coefficients) (degree i : ℕ) :
    (bernstein a degree i : ℂ) =
      bernsteinCoefficient degree i ((polynomial a).map (Rat.castHom ℂ)) := by
  simp only [bernstein, bernsteinCoefficient, rangeSum_eq, choose_eq, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, coeff_map, polynomial, coeff_ofCoeffList,
    Rat.coe_castHom]

namespace Revised

/-- The five physical-time jets, expressed in the coordinate x = t/2. -/
inductive Jet where
  | value | first | second | corrected | slope
  deriving DecidableEq

private def jetFrom (U T : ℕ → Coefficients) (g : Jet) (n : ℕ) : Coefficients :=
  match g with
  | .value => U n
  | .first => derivative U 1 n
  | .second => derivative U 2 n
  | .corrected => if n = 0 then sub (derivative T 2 n) [1 / 200] else derivative T 2 n
  | .slope => derivative T 1 n

/-- Full spacing coefficients of the jet's Taylor row. -/
def fullJet (g : Jet) (n : ℕ) : Coefficients := jetFrom u t g n

/-- Polynomial interpretation of the coefficient formulas for the five jets. -/
theorem fullJet_polynomial (g : Jet) (n : ℕ) :
    let slope (a : ℕ → Coefficients) (k : ℕ) :=
      C (((n + k).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ k)) * polynomial (a (n + k))
    polynomial (fullJet g n) = match g with
      | .value => polynomial (u n)
      | .first => slope u 1
      | .second => slope u 2
      | .corrected => slope t 2 - C (if n = 0 then 1 / 200 else 0)
      | .slope => slope t 1 := by
  cases g <;> simp only [fullJet, jetFrom, derivative, polynomial_scale]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos hn, polynomial_sub, polynomial_scale]
    simp [polynomial, ofCoeffList_cons]
  · rw [if_neg hn, if_neg hn, polynomial_scale]
    simp

/-- Faulhaber numbers through index 23, in the convention B₁ = 1/2. -/
private def bernoulliData : Coefficients :=
  [1, 1 / 2, 1 / 6, 0, -1 / 30, 0, 1 / 42, 0, -1 / 30, 0, 5 / 66, 0,
    -691 / 2730, 0, 7 / 6, 0, -3617 / 510, 0, 43867 / 798, 0, -174611 / 330, 0,
    854513 / 138, 0]

private def bernoulliAt (n : ℕ) : ℚ := bernoulliData.getD n 0

private def bernoulliStep (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  1 - rangeSum (fun k => (choose n k : ℚ) / (n - k + 1 : ℕ) * b k) n

set_option maxHeartbeats 2000000 in
private theorem bernoulliStep_checked :
    (List.range 24).all (fun n => decide (bernoulliStep bernoulliAt n = bernoulliAt n)) =
      true := by decide +kernel

private theorem bernoulliAt_eq (n : ℕ) (hn : n < 24) : bernoulliAt n = bernoulli' n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hstep : bernoulliStep bernoulliAt n = bernoulliAt n := of_decide_eq_true
      ((List.all_eq_true.mp bernoulliStep_checked) n (List.mem_range.mpr hn))
    calc
      bernoulliAt n = bernoulliStep bernoulliAt n := hstep.symm
      _ = bernoulliStep bernoulli' n := by
        unfold bernoulliStep
        congr 1
        exact rangeSum_congr fun k hk => by rw [ih k hk (hk.trans hn)]
      _ = bernoulli' n := by
        rw [bernoulli'_def, bernoulliStep, rangeSum_eq]
        simp only [choose_eq, Nat.cast_add, Nat.cast_one]
        congr 1
        refine sum_congr rfl fun k hk ↦ ?_
        rw [Nat.cast_sub (mem_range.mp hk).le]

private def momentWith (b : ℕ → ℚ) : ℕ → Coefficients
  | 0 => gridSize
  | n + 1 =>
    (List.range (n + 2)).map fun k =>
      (choose (n + 2) k : ℚ) * b k * 3 ^ (n + 2 - k) *
        (3 / 11 : ℚ) ^ k / (n + 2 : ℕ)

private def fastMoment : ℕ → Coefficients := momentWith bernoulliAt

private theorem fastMoment_eq (n : ℕ) (hn : n < 24) : fastMoment n = moment n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [fastMoment, momentWith, moment]
    apply List.map_congr_left
    intro k hk
    rw [bernoulliAt_eq k (by have hk' := List.mem_range.mp hk; omega)]

private theorem sumCoeffs_congr {a b : ℕ → Coefficients} {n : ℕ}
    (heq : ∀ k < n, a k = b k) : sumCoeffs a n = sumCoeffs b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumCoeffs]
    rw [ih (fun k hk => heq k (by omega)), heq n (by omega)]

private def fastU (n : ℕ) : Coefficients :=
  scale ((2 : ℚ) ^ n / (n + 2).factorial)
    (sub (sub (mul gridSize (fastMoment (n + 2))) (fastMoment (n + 3))) c)

private def fastT (n : ℕ) : Coefficients :=
  scale (1 / (n.factorial : ℚ))
    (sub (sumCoeffs (fun k => scale ((choose n k : ℚ) * (-3) ^ (n - k) * 2 ^ k)
      (fastMoment k)) (n + 1)) (scale (1 / 4) (pow (sub [-3] (scale 2 h)) n)))

private theorem fastU_eq (n : ℕ) (hn : n < 21) : fastU n = u n := by
  rw [fastU, u, fastMoment_eq (n + 2) (by omega), fastMoment_eq (n + 3) (by omega)]

private theorem fastT_eq (n : ℕ) (hn : n < 21) : fastT n = t n := by
  have hs : sumCoeffs (fun k => scale ((choose n k : ℚ) * (-3) ^ (n - k) * 2 ^ k)
      (fastMoment k)) (n + 1) =
      sumCoeffs (fun k => scale ((choose n k : ℚ) * (-3) ^ (n - k) * 2 ^ k)
        (moment k)) (n + 1) := by
    apply sumCoeffs_congr
    intro k hk
    rw [fastMoment_eq k (by omega)]
  rw [fastT, t, hs]

private def fastJet : Jet → ℕ → Coefficients := jetFrom fastU fastT

private theorem fastJet_eq (g : Jet) (n : ℕ) (hn : n < 19) : fastJet g n = fullJet g n := by
  have hu₀ := fastU_eq n (by omega)
  have hu₁ := fastU_eq (n + 1) (by omega)
  have hu₂ := fastU_eq (n + 2) (by omega)
  have ht₁ := fastT_eq (n + 1) (by omega)
  have ht₂ := fastT_eq (n + 2) (by omega)
  cases g <;> simp only [fastJet, fullJet, jetFrom, derivative, hu₀, hu₁, hu₂, ht₁, ht₂]

/-- The constant numerator in the jet error budget, in units of 10⁻⁶. -/
def spacingNumerator : Jet → ℕ
  | .value => 14
  | .first => 61
  | .second => 264
  | .corrected => 364
  | .slope => 78

/-- The x¹⁹ numerator in the jet error budget, in units of 10⁻⁶. -/
def tailNumerator : Jet → ℕ
  | .value => 154
  | .first => 419
  | .second => 1146
  | .corrected => 5
  | .slope => 3

/-- The exact spacing projection error summed over n ≤ 18. -/
def spacingL1 (g : Jet) : ℚ :=
  rangeSum (fun n => (((fullJet g n).drop 7).map (fun z => |z|)).sum) 19

theorem spacingL1_eq_sum (g : Jet) : spacingL1 g =
    ∑ n ∈ range 19, (((fullJet g n).drop 7).map (fun z => |z|)).sum := rangeSum_eq _ _

private def fastSpacingL1 (g : Jet) : ℚ :=
  rangeSum (fun n => (((fastJet g n).drop 7).map (fun z => |z|)).sum) 19

private theorem fastSpacingL1_eq (g : Jet) : fastSpacingL1 g = spacingL1 g := by
  unfold fastSpacingL1 spacingL1
  apply rangeSum_congr
  intro n hn
  rw [fastJet_eq g n hn]

/-- The polynomial error budget b_g = (E_g + B_g x¹⁹)/10⁶, by x row. -/
def budgetRow (g : Jet) (n : ℕ) : Coefficients :=
  if n = 0 then [(spacingNumerator g : ℚ) / 1000000]
  else if n = 19 then [(tailNumerator g : ℚ) / 1000000] else []

end Revised
-- Shared projections of the unshifted U and T rows onto y degrees 0 through 6.
namespace Revised

private def uProjection : List Coefficients := [
  [9 / 8,
    27 / 44,
    9 / 88,
    27 / 5324],
  [51 / 20,
    63 / 44,
    123 / 484,
    81 / 5324,
    27 / 146410],
  [33 / 10,
    441 / 220,
    393 / 968,
    81 / 2662,
    243 / 585640,
    -81 / 3221020],
  [111 / 35,
    117 / 55,
    1203 / 2420,
    243 / 5324,
    243 / 292820,
    -243 / 3221020,
    -243 / 124009270],
  [701 / 280,
    1437 / 770,
    1211 / 2420,
    729 / 13310,
    729 / 585640,
    -243 / 1610510,
    -243 / 49603708],
  [239 / 140,
    435 / 308,
    331 / 770,
    729 / 13310,
    2187 / 1464100,
    -729 / 3221020,
    -243 / 24801854],
  [181 / 175,
    291 / 308,
    10931 / 33880,
    2187 / 46585,
    2187 / 1464100,
    -2187 / 8052550,
    -729 / 49603708],
  [1402 / 2475,
    298 / 525,
    32801 / 152460,
    6561 / 186340,
    6561 / 5124350,
    -2187 / 8052550,
    -2187 / 124009270],
  [19661 / 69300,
    7871 / 25410,
    98411 / 762300,
    2187 / 93170,
    19683 / 20497400,
    -6561 / 28183925,
    -2187 / 124009270],
  [59023 / 450450,
    19681 / 127050,
    295241 / 4192650,
    6561 / 465850,
    6561 / 10248700,
    -19683 / 112735700,
    -6561 / 434032445],
  [10627 / 189189,
    354281 / 4954950,
    11503 / 326700,
    19683 / 2562175,
    19683 / 51243500,
    -6561 / 56367850,
    -19683 / 1736129780],
  [531406 / 23648625,
    531434 / 17342325,
    2657201 / 163513350,
    19683 / 5124350,
    59049 / 281839250,
    -19683 / 281839250,
    -6561 / 868064890],
  [1594283 / 189189000,
    1062877 / 86711625,
    7971611 / 1144593450,
    59049 / 33308275,
    59049 / 563678500,
    -59049 / 1550115875,
    -19683 / 4340324450],
  [14348771 / 4824319500,
    4782961 / 1040539500,
    23914841 / 8584450875,
    177147 / 233157925,
    177147 / 3663910250,
    -59049 / 3100231750,
    -59049 / 23871784475],
  [1195738 / 1206079875,
    28697797 / 17689171500,
    71744531 / 68675607000,
    354294 / 1165789625,
    531441 / 25647371750,
    -177147 / 20151506375,
    -59049 / 47743568950],
  [7174444 / 22915517625,
    2391484 / 4422292875,
    19566691 / 53067514500,
    531441 / 4663158500,
    531441 / 64118429375,
    -531441 / 141060544625,
    -177147 / 310333198175],
  [55345757 / 589256167500,
    258280307 / 1512424163250,
    92242973 / 750526276500,
    1594323 / 39636847250,
    1594323 / 512947435000,
    -1062882 / 705302723125,
    -531441 / 2172332387225],
  [387420419 / 14436776103750,
    387420479 / 7562120816250,
    1937102441 / 49909997387250,
    531441 / 39636847250,
    4782969 / 4360053197500,
    -1594323 / 2821210892500,
    -1062882 / 10861661936125],
  [116226139 / 15880453714125,
    774840971 / 52934845713750,
    5811307331 / 499099973872500,
    1594323 / 376550048875,
    1594323 / 4360053197500,
    -4782969 / 23980292586250,
    -1594323 / 43446647744500],
  [418414118 / 219150261254925,
    697356878 / 174684990855375,
    17433922001 / 5240549725661250,
    4782969 / 3765500488750,
    4782969 / 41420505376250,
    -1594323 / 23980292586250,
    -4782969 / 369296505828250],
  [804642547 / 1685771240422500,
    20920706383 / 20088773948368125,
    4754706001 / 5240549725661250,
    4782969 / 13179251710625,
    14348907 / 414205053762500,
    -4782969 / 227812779569375,
    -1594323 / 369296505828250],
]

private def tProjection : List Coefficients := [
  [11 / 4,
    3 / 11],
  [3 / 4,
    3 / 22],
  [27 / 8,
    9 / 11,
    9 / 242],
  [9 / 8,
    27 / 44,
    27 / 242,
    9 / 1331],
  [189 / 160,
    27 / 88,
    -27 / 484,
    -27 / 1331,
    -189 / 146410],
  [81 / 160,
    81 / 176,
    81 / 484,
    81 / 2662,
    81 / 29282,
    81 / 805255],
  [81 / 448,
    0,
    -729 / 9680,
    -81 / 2662,
    -1377 / 292820,
    -243 / 805255,
    -81 / 12400927],
  [243 / 2240,
    243 / 1760,
    729 / 9680,
    243 / 10648,
    243 / 58564,
    729 / 1610510,
    243 / 8857805],
  [243 / 17920,
    -729 / 49280,
    -729 / 27104,
    -729 / 53240,
    -19683 / 5856400,
    -729 / 1610510,
    -4617 / 124009270],
  [243 / 17920,
    2187 / 98560,
    2187 / 135520,
    729 / 106480,
    2187 / 1171280,
    2187 / 6442040,
    729 / 17715610],
  [729 / 1971200,
    -729 / 246400,
    -729 / 154880,
    -2187 / 745360,
    -80919 / 81989600,
    -6561 / 32210200,
    -6561 / 225471400],
  [2187 / 1971200,
    2187 / 985600,
    2187 / 1084160,
    6561 / 5962880,
    6561 / 16397920,
    6561 / 64420400,
    6561 / 354312200],
  [-2187 / 102502400,
    -6561 / 21683200,
    -59049 / 119257600,
    -2187 / 5962880,
    -102789 / 655916800,
    -19683 / 450942800,
    -308367 / 34722595600],
  [6561 / 102502400,
    6561 / 43366400,
    19683 / 119257600,
    6561 / 59628800,
    6561 / 131183360,
    59049 / 3607542400,
    19683 / 4960370800],
  [-19683 / 7175168000,
    -19683 / 986585600,
    -19683 / 563763200,
    -19683 / 655916800,
    -1121931 / 72150848000,
    -19683 / 3607542400,
    -400221 / 277780764800],
  [19683 / 7175168000,
    59049 / 7892684800,
    59049 / 6201395200,
    19683 / 2623667200,
    59049 / 14430169600,
    59049 / 36075424000,
    19683 / 39682966400],
  [-59049 / 390329139200,
    -59049 / 63141478400,
    -59049 / 33392128000,
    -59049 / 34107673600,
    -3956283 / 3751844096000,
    -177147 / 396829664000,
    -177147 / 1222235365120],
  [177147 / 1951645696000,
    177147 / 631414784000,
    177147 / 434097664000,
    177147 / 477507430400,
    177147 / 750368819200,
    177147 / 1587318656000,
    177147 / 4365126304000],
  [-59049 / 10594648064000,
    -177147 / 5367025664000,
    -1594323 / 23614912921600,
    -177147 / 2387537152000,
    -177147 / 3410767360000,
    -531441 / 20635142528000,
    -15766083 / 1588905974656000],
  [177147 / 74162536448000,
    177147 / 21468102656000,
    1594323 / 118074564608000,
    531441 / 38200594432000,
    531441 / 52525817344000,
    1594323 / 288891995392000,
    531441 / 226986567808000],
  [-1594323 / 10382755102720000,
    -531441 / 582705643520000,
    -531441 / 263931379712000,
    -1594323 / 649410105344000,
    -138706101 / 71435111587840000,
    -1594323 / 1444459976960000,
    -54738423 / 111223418225920000],
]

private def curvatureRow25PowerData : Coefficients := [
    79929955596215269383427 / 22318930103500800000000000,
    50761153346510390230745959 / 597069337632768000000000000,
    98484287305530111562081387 / 954012963391488000000000000,
    92227967602648492851491 / 6996095064870912000000000,
    1007308890948806468963 / 193895302881280000000000,
    23976517033246150082943 / 7464969160929280000000000,
    207445834814722264197 / 540228031383040000000000,
    4385818178139768057 / 27011401569152000000000,
    408763477193319 / 25278049596800000000
]

/-- The primitive projection, with the physical-time derivative factors. -/
def jetRow (g : Jet) (n : ℕ) : Coefficients :=
  if n < 19 then jetFrom (fun k => uProjection.getD k [])
    (fun k => tProjection.getD k []) g n else []

end Revised
-- Witnesses, coefficient correspondence, and the representative benchmark.
namespace Revised

/-- Ascending x rows of q. Each row is an ascending list in y. -/
def qRows : List Coefficients :=
  [[1060364, 289300, 8719], [1201564, 346575, 15251], [882548, 320739, 26395],
    [457271, 181003, 14742], [374350, 251002, 50057], [-59873, -84643, -25991],
    [141041, 120222, 28731]].map (scale (1 / 1000000))

/-- Ascending x rows of r. -/
def rRows : List Coefficients := [[1124, 16], [442, 119]].map (scale (1 / 1000))

private def shiftX (a : ℕ → Coefficients) (n : ℕ) : Coefficients :=
  if n = 0 then [] else a (n - 1)

private theorem shiftX_polynomial (a : ℕ → Coefficients) (n : ℕ) :
    polynomial (shiftX a n) = if n = 0 then 0 else polynomial (a (n - 1)) := by
  by_cases hn : n = 0 <;> simp [shiftX, hn, polynomial]

/-- Convolve with a short witness in x using the existing y polynomial multiplication. -/
private def witnessProduct
    (w : List Coefficients) (a : ℕ → Coefficients) (n : ℕ) : Coefficients :=
  sumCoeffs (fun k => mul (w.getD k []) (a (n - k))) (min w.length (n + 1))

private theorem witnessProduct_polynomial
    (w : List Coefficients) (a : ℕ → Coefficients) (n : ℕ) :
    polynomial (witnessProduct w a n) =
      ∑ k ∈ range (n + 1), polynomial (w.getD k []) * polynomial (a (n - k)) := by
  rw [witnessProduct, polynomial_sum]
  simp only [polynomial_mul]
  apply Finset.sum_subset
  · intro k hk
    exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (Nat.min_le_right _ _))
  · intro k hk hout
    have hk' := mem_range.mp hk
    have hout' : ¬ k < min w.length (n + 1) := fun h => hout (mem_range.mpr h)
    have hlen : w.length ≤ k := by omega
    have hget : w[k]? = none := List.getElem?_eq_none hlen
    simp [List.getD_eq_getElem?_getD, hget, polynomial]

/-- x power rows of P₀ − b₀ − q². -/
def sqrtComparison (n : ℕ) : Coefficients :=
  sub (sub (jetRow .value n) (budgetRow .value n))
    (witnessProduct qRows (fun k => qRows.getD k []) n)

/-- x power rows of the second tensor in the order-18 certificate. -/
def curvatureComparison (n : ℕ) : Coefficients :=
  let corrected := witnessProduct qRows
    (fun k => sub (jetRow .corrected k) (budgetRow .corrected k)) n
  let first := sub (jetRow .first n) (shiftX (witnessProduct rRows (jetRow .first)) n)
  let second := shiftX (jetRow .second) n
  let value := scale (1 / 2) (shiftX (witnessProduct rRows
    (witnessProduct rRows (jetRow .value))) n)
  let error := add (add (budgetRow .first n) (budgetRow .second n))
    (scale 2 (budgetRow .value n))
  sub (sub corrected (add (add first second) value)) error

/-- Coefficient identity for the first tensor, with each row interpreted as a polynomial in y. -/
theorem sqrtComparison_row_polynomial (n : ℕ) :
    polynomial (sqrtComparison n) =
      polynomial (jetRow .value n) - polynomial (budgetRow .value n) -
        ∑ k ∈ range (n + 1), polynomial (qRows.getD k []) *
          polynomial (qRows.getD (n - k) []) := by
  simp only [sqrtComparison, polynomial_sub, witnessProduct_polynomial]

/-- Coefficient identity for the second tensor. The three terms guarded by n = 0
have an explicit factor x in the polynomial. All products here are in the y variable. -/
theorem curvatureComparison_row_polynomial (n : ℕ) :
    let P (g : Jet) (k : ℕ) := polynomial (jetRow g k)
    let b (g : Jet) (k : ℕ) := polynomial (budgetRow g k)
    let q (k : ℕ) := polynomial (qRows.getD k [])
    let r (k : ℕ) := polynomial (rRows.getD k [])
    let z := n - 1
    polynomial (curvatureComparison n) =
      (∑ k ∈ range (n + 1), q k * (P .corrected (n - k) - b .corrected (n - k))) -
        ((P .first n - (if n = 0 then 0 else
            ∑ k ∈ range (z + 1), r k * P .first (z - k))) +
          (if n = 0 then 0 else P .second z) +
          C (1 / 2 : ℚ) * (if n = 0 then 0 else
            ∑ k ∈ range (z + 1), r k *
              ∑ l ∈ range (z - k + 1), r l * P .value (z - k - l))) -
        (b .first n + b .second n + C (2 : ℚ) * b .value n) := by
  simp only [curvatureComparison, polynomial_add, polynomial_sub, polynomial_scale,
    shiftX_polynomial, witnessProduct_polynomial]

/-- Evaluate at x = 1, keeping the remaining y coefficients. -/
def atOne (a : ℕ → Coefficients) : Coefficients := sumCoeffs a 20

/-- L at x = 1. -/
def endpointL : Coefficients :=
  scale 2 (sub (add (atOne (jetRow .value)) (atOne (jetRow .first)))
    (add (atOne (budgetRow .value)) (atOne (budgetRow .first))))

/-- M at x = 1. -/
def endpointM : Coefficients := add (atOne (jetRow .value)) (atOne (budgetRow .value))

/-- V at x = 1. -/
def endpointV : Coefficients := atOne (jetRow .slope)

/-- L² − 4M(V + bS(1))², as a polynomial in y. -/
def endpointComparison : Coefficients :=
  let s := add endpointV (atOne (budgetRow .slope))
  sub (mul endpointL endpointL) (scale 4 (mul endpointM (mul s s)))

theorem atOne_polynomial (a : ℕ → Coefficients) :
    polynomial (atOne a) = ∑ k ∈ range 20, polynomial (a k) := polynomial_sum _ _

theorem endpointL_polynomial :
    polynomial endpointL = C (2 : ℚ) *
      ((polynomial (atOne (jetRow .value)) + polynomial (atOne (jetRow .first))) -
        (polynomial (atOne (budgetRow .value)) + polynomial (atOne (budgetRow .first)))) := by
  simp only [endpointL, polynomial_scale, polynomial_sub, polynomial_add]

theorem endpointM_polynomial :
    polynomial endpointM =
      polynomial (atOne (jetRow .value)) + polynomial (atOne (budgetRow .value)) := by
  simp only [endpointM, polynomial_add]

theorem endpointV_polynomial :
    polynomial endpointV = polynomial (atOne (jetRow .slope)) := rfl

theorem endpointComparison_polynomial :
    polynomial endpointComparison = polynomial endpointL ^ 2 -
      C (4 : ℚ) * (polynomial endpointM *
        (polynomial endpointV + polynomial (atOne (budgetRow .slope))) ^ 2) := by
  simp only [endpointComparison, polynomial_sub, polynomial_mul, polynomial_scale,
    polynomial_add, pow_two]

/-- Elevate in x to degree d, retaining each row's y power coefficients. -/
def bernsteinXRow (a : ℕ → Coefficients) (d i : ℕ) : Coefficients :=
  sumCoeffs (fun k => scale ((choose i k : ℚ) / (choose d k : ℚ)) (a k))
    (min (d + 1) (i + 1))

/-- The x row is the coefficientwise Bernstein transform, with y left in the power basis. -/
theorem bernsteinXRow_polynomial (a : ℕ → Coefficients) (d i : ℕ) :
    polynomial (bernsteinXRow a d i) =
      ∑ k ∈ range (d + 1), C ((i.choose k : ℚ) / (d.choose k : ℚ)) * polynomial (a k) := by
  rw [bernsteinXRow, polynomial_sum]
  simp only [polynomial_scale, choose_eq]
  apply Finset.sum_subset
  · intro k hk
    exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (Nat.min_le_left _ _))
  · intro k hk hout
    have hk' := mem_range.mp hk
    have hout' : ¬ k < min (d + 1) (i + 1) := fun h => hout (mem_range.mpr h)
    have hik : i < k := by omega
    simp [Nat.choose_eq_zero_of_lt hik]

/-- The tensor coefficient at (i,j), via two ordinary Bernstein transforms. -/
def tensorBernstein (a : ℕ → Coefficients) (d e i j : ℕ) : ℚ :=
  bernstein (bernsteinXRow a d i) e j

/-- The final y transform is the existing polynomial Bernstein coefficient. -/
theorem tensorBernstein_eq (a : ℕ → Coefficients) (d e i j : ℕ) :
    (tensorBernstein a d e i j : ℂ) =
      bernsteinCoefficient e j
        ((∑ k ∈ range (d + 1), C ((i.choose k : ℚ) / (d.choose k : ℚ)) *
          polynomial (a k)).map (Rat.castHom ℂ)) := by
  rw [tensorBernstein, bernstein_eq, bernsteinXRow_polynomial]

private def strictRow (a : Coefficients) (e : ℕ) (bound : ℚ) : Bool :=
  (List.range (e + 1)).all fun j => decide (bound < bernstein a e j)

private theorem strictRow_sound {a : Coefficients} {e j : ℕ} {bound : ℚ}
    (h : strictRow a e bound = true) (hj : j ≤ e) : bound < bernstein a e j := by
  rw [strictRow, List.all_eq_true] at h
  exact of_decide_eq_true (h j (List.mem_range.mpr (Nat.lt_succ_of_le hj)))

private def sqrtRowCheck (i : ℕ) : Bool := strictRow (bernsteinXRow sqrtComparison 19 i) 6 (3 / 5000)
private def curvatureRowCheck (i : ℕ) : Bool :=
  strictRow (bernsteinXRow curvatureComparison 25 i) 8 (7 / 2000)

-- Isolated first kernel benchmark. This computes the nine y power coefficients once.
set_option maxHeartbeats 2000000 in
set_option profiler true in
set_option profiler.threshold 0 in
private theorem curvatureRow25_power_eq :
    bernsteinXRow curvatureComparison 25 25 = curvatureRow25PowerData := by
  decide +kernel

-- The next benchmark measures just the nine y Bernstein inequalities.
set_option maxHeartbeats 2000000 in
set_option profiler true in
set_option profiler.threshold 0 in
private theorem curvatureRow25_checked : curvatureRowCheck 25 = true := by
  rw [curvatureRowCheck, curvatureRow25_power_eq]
  decide +kernel

/-- The representative row at the right edge of the x rectangle. -/
theorem curvatureBernstein_row25 {j : ℕ} (hj : j ≤ 8) :
    (7 / 2000 : ℚ) < tensorBernstein curvatureComparison 25 8 25 j :=
  strictRow_sound curvatureRow25_checked hj

end Revised

namespace Revised

set_option maxHeartbeats 2000000 in
private theorem uProjection_eq (n : ℕ) (hn : n < 21) :
    uProjection.getD n [] = (fastU n).take 7 := by
  interval_cases n <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem tProjection_eq (n : ℕ) (hn : n < 21) :
    tProjection.getD n [] = (fastT n).take 7 := by
  interval_cases n <;> decide +kernel

private theorem take_scale (z : ℚ) (a : Coefficients) :
    (scale z a).take 7 = scale z (a.take 7) := by
  exact List.map_take.symm

private theorem take_sub_single (a : Coefficients) (z : ℚ) :
    (sub a [z]).take 7 = sub (a.take 7) [z] := by
  cases a with
  | nil => rfl
  | cons a as =>
    simp only [sub, List.take, List.zipWithAll_cons_cons, List.zipWithAll_nil, List.map_take]

/-- Each stored primitive row agrees with the exact Faulhaber row in y degrees 0 through 6. -/
theorem jetRow_eq_take (g : Jet) (n : ℕ) (hn : n < 19) :
    jetRow g n = (fullJet g n).take 7 := by
  have hu₀ := uProjection_eq n (by omega)
  have hu₁ := uProjection_eq (n + 1) (by omega)
  have hu₂ := uProjection_eq (n + 2) (by omega)
  have ht₁ := tProjection_eq (n + 1) (by omega)
  have ht₂ := tProjection_eq (n + 2) (by omega)
  rw [jetRow, if_pos hn, ← fastJet_eq g n hn]
  by_cases hzero : n = 0
  · cases g <;>
      simp only [fastJet, jetFrom, derivative, hu₀, hu₁, hu₂, ht₁, ht₂,
        ← take_scale, ← take_sub_single, if_pos hzero]
  · cases g <;>
    simp only [fastJet, jetFrom, derivative, hu₀, hu₁, hu₂, ht₁, ht₂,
      ← take_scale, if_neg hzero]

set_option maxHeartbeats 2000000 in
/-- All five ℓ¹ bounds for the discarded spacing coefficients. -/
theorem spacingL1_le (g : Jet) :
    spacingL1 g ≤ (spacingNumerator g : ℚ) / 1000000 := by
  rw [← fastSpacingL1_eq]
  cases g <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem sqrtRow_checked (i : ℕ) (hi : i ≤ 19) : sqrtRowCheck i = true := by
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem curvatureRow_checked (i : ℕ) (hi : i ≤ 25) :
    curvatureRowCheck i = true := by
  have hedge : i ≤ 24 ∨ i = 25 := by omega
  rcases hedge with hi' | rfl
  · interval_cases i <;> decide +kernel
  · exact curvatureRow25_checked

/-- All 140 entries of the first tensor exceed the proposed lower bound. -/
theorem sqrtBernstein_checked {i j : ℕ} (hi : i ≤ 19) (hj : j ≤ 6) :
    (3 / 5000 : ℚ) < tensorBernstein sqrtComparison 19 6 i j :=
  strictRow_sound (sqrtRow_checked i hi) hj

/-- All 234 entries of the second tensor exceed the proposed lower bound. -/
theorem curvatureBernstein_checked {i j : ℕ} (hi : i ≤ 25) (hj : j ≤ 8) :
    (7 / 2000 : ℚ) < tensorBernstein curvatureComparison 25 8 i j :=
  strictRow_sound (curvatureRow_checked i hi) hj

set_option maxHeartbeats 2000000 in
private theorem endpointComparison_checked : strictRow endpointComparison 18 446 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private theorem endpointL_checked : strictRow endpointL 6 84 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
private theorem endpointV_checked : strictRow endpointV 6 10 = true := by decide +kernel

/-- The 19 endpoint Bernstein coefficients for the sign comparison. -/
theorem endpointBernstein_checked {j : ℕ} (hj : j ≤ 18) :
    (446 : ℚ) < bernstein endpointComparison 18 j :=
  strictRow_sound endpointComparison_checked hj

/-- The seven endpoint Bernstein coefficients for L. -/
theorem endpointLBernstein_checked {j : ℕ} (hj : j ≤ 6) : (84 : ℚ) < bernstein endpointL 6 j :=
  strictRow_sound endpointL_checked hj

/-- The seven endpoint Bernstein coefficients for V. -/
theorem endpointVBernstein_checked {j : ℕ} (hj : j ≤ 6) : (10 : ℚ) < bernstein endpointV 6 j :=
  strictRow_sound endpointV_checked hj

/-- The row lengths bound the spacing degree used in the Bernstein transform. -/
theorem sqrtBernstein_row_length {i : ℕ} (hi : i ≤ 19) :
    (bernsteinXRow sqrtComparison 19 i).length ≤ 7 := by
  interval_cases i <;> decide +kernel

theorem curvatureBernstein_row_length {i : ℕ} (hi : i ≤ 25) :
    (bernsteinXRow curvatureComparison 25 i).length ≤ 9 := by
  interval_cases i <;> decide +kernel

theorem endpoint_row_lengths : endpointComparison.length ≤ 19 ∧
    endpointL.length ≤ 7 ∧ endpointV.length ≤ 7 := by decide +kernel

#print axioms curvatureBernstein_row25
#print axioms jetRow_eq_take
#print axioms spacingL1_le
#print axioms sqrtBernstein_checked
#print axioms curvatureBernstein_checked
#print axioms endpointBernstein_checked
#print axioms endpointLBernstein_checked
#print axioms endpointVBernstein_checked

end Revised

end RefinedBMV.PositiveCenter.ShortGapFinite
