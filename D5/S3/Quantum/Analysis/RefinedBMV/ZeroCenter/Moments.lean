/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Moments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative Taylor moments for the regularized zero-centered radicand. -/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! The exponential moments of the six-knot regularization. -/

open Finset PowerSeries
open scoped BigOperators

/-- The six rational knots in the order of the forward coefficient recurrence. -/
def RefinedBMV.FourSpectrumLift.regularizingKnotsRat (h : ℚ) : Fin 6 → ℚ :=
  ![1 + 6*h, 1 + 3*h, 1, 3*h, 0, 3 + 6*h]

noncomputable section

namespace RefinedBMV.FourSpectrumLift

/-- The complementary knots in the exponential expansion of the radicand. -/
def radicandKnots (h : ℝ) : Fin 6 → ℝ :=
  ![1 + 6*h, 1 + 3*h, 1, 3*h, 0, 3 + 6*h]

/-- The corresponding signed weights after clearing (2h^2). -/
def radicandWeights (h : ℝ) : Fin 6 → ℝ :=
  ![-(1+h)*(1+2*h), 2*(1+h)*(1+2*h), -(1+h)*(1+2*h),
    -2*h*(1+2*h), 2*h*(1+h), 2*h^2]

private theorem clear_moment_fraction (h : ℝ) :
    (∑ i : Fin 6, C (radicandWeights h i) *
      ∏ j ∈ univ.erase i, (1 - C (radicandKnots h j) * X)) =
    C (2 * h^2 * (27 * (1+h) * (1+2*h) * (1+3*h))) *
      X^4 * (1 - C (1/3 + 2*h) * X) := by
  classical
  have hprod (i : Fin 6) :
      (∏ j ∈ univ.erase i, (1 - C (radicandKnots h j) * X)) =
        ∏ j : Fin 6, if j = i then 1 else (1 - C (radicandKnots h j) * X) := by
    have heq (j : Fin 6) : (if j = i then (1 : ℝ⟦X⟧) else 1 - C (radicandKnots h j) * X) =
        if j ∈ (univ : Finset (Fin 6)).erase i then 1 - C (radicandKnots h j) * X else 1 := by
      by_cases hij : j = i <;> simp [hij]
    simp only [heq, Finset.prod_ite_mem, Finset.univ_inter]
  simp only [hprod, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [radicandWeights, radicandKnots, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, map_sub, map_mul, map_div₀, map_ofNat, map_neg, map_pow]
  have hthird : 3 * C (1 / 3 : ℝ) = (1 : ℝ⟦X⟧) := by
    rw [← map_ofNat C 3, ← map_mul]
    norm_num
  linear_combination
    (18 + 108 * C h + 198 * C h ^ 2 + 108 * C h ^ 3) * C h ^ 2 * X ^ 5 * hthird

private def geom (a : ℝ) : ℝ⟦X⟧ := mk fun n ↦ a ^ n

private theorem geom_mul_factor (a : ℝ) : geom a * (1 - C a * X) = 1 := by
  simpa [geom, rescale_mk, rescale_X] using
    congrArg (rescale a) (mk_one_mul_one_sub_eq_one ℝ)

private theorem geom_product_nonneg {ι : Type*}
    (s : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ s, 0 ≤ d i) (n : ℕ) :
    0 ≤ coeff n (∏ i ∈ s, geom (d i)) := by
  classical
  rw [coeff_prod]
  exact Finset.sum_nonneg fun l _ ↦ Finset.prod_nonneg fun i hi ↦ by
    simpa only [geom, coeff_mk] using pow_nonneg (hd i hi) (l i)

private theorem weighted_geom_factor (h : ℝ) :
    (∑ i : Fin 6, C (radicandWeights h i) * geom (radicandKnots h i)) =
      C (2 * h^2 * (27 * (1+h) * (1+2*h) * (1+3*h))) *
        (X^4 * ((∏ i ∈ univ.erase (5 : Fin 6), geom (radicandKnots h i)) +
          C (4*h + 8/3) * (X * ∏ i : Fin 6, geom (radicandKnots h i)))) := by
  classical
  let D (i : Fin 6) := 1 - C (radicandKnots h i) * X
  let G (i : Fin 6) := geom (radicandKnots h i)
  have hm (i : Fin 6) : D i * G i = 1 := by rw [mul_comm]; exact geom_mul_factor _
  have hcancels (s : Finset (Fin 6)) :
      (∏ i ∈ s, D i) * (∏ i ∈ s, G i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp only [hm, Finset.prod_const_one]
  have hterm (i : Fin 6) :
      (∏ j ∈ univ.erase i, D j) * (∏ j : Fin 6, G j) = G i := by
    rw [← Finset.prod_erase_mul _ G (mem_univ i), ← mul_assoc, hcancels, one_mul]
  have hlast : (D 5) * (∏ j : Fin 6, G j) = ∏ j ∈ univ.erase 5, G j := by
    rw [← Finset.prod_erase_mul _ G (mem_univ (5 : Fin 6))]
    calc
      _ = (∏ j ∈ univ.erase 5, G j) * (D 5 * G 5) := by ring
      _ = _ := by rw [hm, mul_one]
  have hsplit : (1 : ℝ⟦X⟧) - C (1/3 + 2*h) * X = D 5 + C (4*h + 8/3) * X := by
    change _ = 1 - C (radicandKnots h 5) * X + C (4*h + 8/3) * X
    rw [show radicandKnots h 5 = (1/3 + 2*h) + (4*h + 8/3) by
      change 3 + 6*h = _
      ring]
    simp only [map_add]
    ring
  have hclear := congrArg (fun f : ℝ⟦X⟧ ↦ f * ∏ i : Fin 6, G i)
    (clear_moment_fraction h)
  change ((∑ i : Fin 6, C (radicandWeights h i) * ∏ j ∈ univ.erase i, D j) *
    ∏ i : Fin 6, G i) = _ at hclear
  simp only [Finset.sum_mul] at hclear
  simp_rw [mul_assoc, hterm] at hclear
  rw [hsplit, add_mul (D 5), hlast] at hclear
  simpa only [mul_assoc] using hclear

/-- The first four exponential moments vanish. Every later moment is
nonnegative, including at parameters for which knots coincide. -/
theorem radicand_moment_nonneg {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ ∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ n := by
  have hk (i : Fin 6) : 0 ≤ radicandKnots h i := by
    fin_cases i <;> simp [radicandKnots] <;> positivity
  have he := congrArg (coeff n) (weighted_geom_factor h)
  simp only [map_sum, coeff_C_mul, geom, coeff_mk] at he
  rw [he, coeff_X_pow_mul']
  split_ifs with hn
  · rw [map_add, coeff_C_mul]
    apply mul_nonneg (by positivity)
    apply add_nonneg (geom_product_nonneg _ _ (fun i _ ↦ hk i) _)
    apply mul_nonneg (by positivity)
    rw [← pow_one (X : ℝ⟦X⟧), coeff_X_pow_mul']
    split_ifs
    · exact geom_product_nonneg _ _ (fun i _ ↦ hk i) _
    · exact le_rfl
  · simp

/-- The radicand vanishes to order at least four in the exponential expansion. -/
theorem radicand_moment_eq_zero {h : ℝ} {n : ℕ} (hn : n < 4) :
    ∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ n = 0 := by
  have he := congrArg (coeff n) (weighted_geom_factor h)
  simpa only [map_sum, coeff_C_mul, geom, coeff_mk, coeff_X_pow_mul',
    ite_eq_right (Nat.not_le.mpr hn), mul_zero] using he

/-- The radicand of the rationalized zero-centered profile at positive reciprocal degree. -/
def rationalizedRadicand (c h : ℝ) : ℝ :=
  let d := 1 - Real.exp (-3 * h * c)
  let a := (1 + h) / h * d
  let b := (1 + 2*h) / h * d
  1 - Real.exp (-3 * (1+h) * c) * (1+a) - (a*b/2) * Real.exp (-2*c)

private theorem radicand_exp_sum {c h : ℝ} (hh : 0 < h) :
    2*h^2 * Real.exp ((3+6*h)*c) * rationalizedRadicand c h =
      ∑ i : Fin 6, radicandWeights h i * Real.exp (radicandKnots h i * c) := by
  let q := Real.exp (-3 * h * c)
  let z := Real.exp (-3 * (1+h) * c)
  let E := Real.exp (-2*c)
  let T := Real.exp ((3+6*h)*c)
  have h0 : T * E = Real.exp ((1+6*h)*c) := by
    dsimp [T, E]
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : T * q * E = Real.exp ((1+3*h)*c) := by
    dsimp [T, q, E]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : T * q^2 * E = Real.exp c := by
    dsimp [T, q, E]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h3 : T * z = Real.exp (3*h*c) := by
    dsimp [T, z]
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : T * z * q = 1 := by
    dsimp [T, z, q]
    rw [← Real.exp_add, ← Real.exp_add]
    rw [show (3 + 6*h)*c + -3*(1+h)*c + -3*h*c = 0 by ring, Real.exp_zero]
  calc
    _ = 2*h^2*T - 2*h*(1+2*h)*(T*z) + 2*h*(1+h)*(T*z*q) -
        (1+h)*(1+2*h)*(T*E - 2*(T*q*E) + T*q^2*E) := by
      change 2*h^2*T*(1-z*(1+(1+h)/h*(1-q))-
        ((1+h)/h*(1-q)*((1+2*h)/h*(1-q))/2)*E) = _
      field_simp [hh.ne']
      ring
    _ = _ := by
      rw [h0, h1, h2, h4, h3]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [radicandKnots, radicandWeights, Matrix.cons_val_zero, Matrix.cons_val_succ]
      change _ = _ + (_ + (_ + (_ + (_ + 2*h^2*T))))
      ring

private theorem fourth_moment (h : ℝ) :
    (∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ 4) =
      2*h^2 * (27*(1+h)*(1+2*h)*(1+3*h)) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [radicandKnots, radicandWeights, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

private theorem hasSum_radicand_moments (c h : ℝ) :
    HasSum (fun n : ℕ ↦
      (∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ n) * (c ^ n / n.factorial))
      (∑ i : Fin 6, radicandWeights h i * Real.exp (radicandKnots h i * c)) := by
  have hs (i : Fin 6) : HasSum
      (fun n : ℕ ↦ radicandWeights h i * ((radicandKnots h i * c) ^ n / n.factorial))
      (radicandWeights h i * Real.exp (radicandKnots h i * c)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (radicandKnots h i * c)).mul_left _
  convert hasSum_sum (s := (univ : Finset (Fin 6))) (fun i _ ↦ hs i) using 1
  funext n
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_pow, mul_div_assoc, mul_assoc]

/-- The first surviving moment supplies a positive lower bound on the scaled
radicand throughout the positive parameter range. -/
theorem rationalized_radicand_lower {c h : ℝ} (hc : 0 ≤ c) (hh : 0 < h) :
    27 * (1+h) * (1+2*h) * (1+3*h) * c^4 / 24 ≤
      Real.exp ((3+6*h)*c) * rationalizedRadicand c h := by
  have hs := hasSum_radicand_moments c h
  have hl := hs.summable.le_tsum 4 (fun n _ ↦ mul_nonneg (radicand_moment_nonneg hh.le n)
    (div_nonneg (pow_nonneg hc n) (by positivity)))
  rw [hs.tsum_eq, ← radicand_exp_sum hh, fourth_moment] at hl
  norm_num [Nat.factorial] at hl
  apply le_of_mul_le_mul_left _ (show 0 < 2*h^2 by positivity)
  convert hl using 1 <;> ring

/-- Coefficients of the regularizing series after the four vanishing moments
have been removed. Each product is indexed by positions, allowing repeated knots. -/
def regularizingCoefficient (h : ℝ) (n : ℕ) : ℝ :=
  coeff n ((∏ i ∈ univ.erase (5 : Fin 6), geom (radicandKnots h i)) +
    C (4*h + 8/3) * (X * ∏ i : Fin 6, geom (radicandKnots h i))) /
      (n+4).factorial

/-- Termwise cancellation of the factor from the four zero moments. -/
private theorem moment_eq_regularizingCoefficient (h : ℝ) (n : ℕ) :
    (∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ (n+4)) / (n+4).factorial =
      (2 * h^2 * (27 * (1+h) * (1+2*h) * (1+3*h))) * regularizingCoefficient h n := by
  have he := congrArg (coeff (n+4)) (weighted_geom_factor h)
  simp only [map_sum, coeff_C_mul, geom, coeff_mk, coeff_X_pow_mul] at he
  rw [he, regularizingCoefficient, mul_div_assoc]
  rfl

/-- The six-knot regularizing series sums to the radicand after removing
the fourth-order zero and the exponential factor. -/
theorem hasSum_regularizing_series {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    HasSum (fun n : ℕ ↦ regularizingCoefficient h n * c ^ n)
      ((Real.exp ((3+6*h)*c) * rationalizedRadicand c h) /
        ((27 * (1+h) * (1+2*h) * (1+3*h)) * c ^ 4)) := by
  let m (n : ℕ) := (∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ n) *
    (c ^ n / n.factorial)
  have hvanish : (∑ n ∈ range 4, m n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [m, radicand_moment_eq_zero (mem_range.mp hn), zero_mul]
  have hs := (hasSum_nat_add_iff' (f := m) 4).mpr (hasSum_radicand_moments c h)
  rw [hvanish, sub_zero, ← radicand_exp_sum hh] at hs
  let M := 27 * (1+h) * (1+2*h) * (1+3*h)
  let scale := 2*h^2*M*c^4
  have hscale : 0 < scale := by dsimp [scale, M]; positivity
  have hterm (n : ℕ) : m (n+4) = (regularizingCoefficient h n * c ^ n) * scale := by
    dsimp only [m, scale, M]
    rw [show (∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ (n+4)) *
        (c ^ (n+4) / (n+4).factorial) =
      ((∑ i : Fin 6, radicandWeights h i * radicandKnots h i ^ (n+4)) / (n+4).factorial) *
        c ^ (n+4) by ring]
    rw [moment_eq_regularizingCoefficient, pow_add]
    ring
  simp_rw [hterm] at hs
  convert hs.div_const scale using 1
  · ext n
    exact (mul_div_cancel_right₀ _ hscale.ne').symm
  · dsimp [scale, M]
    field_simp [hc.ne', hh.ne']
    <;> ring

/-- All coefficients of the regularization are nonnegative for nonnegative
reciprocal degree, including zero. -/
theorem regularizingCoefficient_nonneg {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ regularizingCoefficient h n := by
  have hk (i : Fin 6) : 0 ≤ radicandKnots h i := by
    fin_cases i <;> simp [radicandKnots] <;> positivity
  unfold regularizingCoefficient
  apply div_nonneg _ (by positivity)
  rw [map_add, coeff_C_mul]
  apply add_nonneg (geom_product_nonneg _ _ (fun i _ ↦ hk i) _)
  apply mul_nonneg (by positivity)
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul]
    exact geom_product_nonneg _ _ (fun i _ ↦ hk i) _

private theorem geom_product_mono {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) (n : ℕ) :
    coeff n (∏ i ∈ s, geom (a i)) ≤ coeff n (∏ i ∈ s, geom (b i)) := by
  classical
  simp only [coeff_prod, geom, coeff_mk]
  exact Finset.sum_le_sum fun l _ ↦
    Finset.prod_le_prod₀ (fun i hi ↦ pow_nonneg (ha i hi) (l i))
      (fun i hi ↦ pow_le_pow_left₀ (ha i hi) (hab i hi) (l i))

/-- Each regularizing coefficient is nondecreasing on nonnegative reciprocal degrees. -/
theorem regularizingCoefficient_mono {h k : ℝ} (hh : 0 ≤ h) (hk : h ≤ k) (n : ℕ) :
    regularizingCoefficient h n ≤ regularizingCoefficient k n := by
  have hk₀ : 0 ≤ k := hh.trans hk
  have hknots₀ (i : Fin 6) : 0 ≤ radicandKnots h i := by
    fin_cases i <;> simp [radicandKnots] <;> positivity
  have hknots (i : Fin 6) : radicandKnots h i ≤ radicandKnots k i := by
    fin_cases i <;> simp [radicandKnots] <;> linarith
  unfold regularizingCoefficient
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [(coeff (R := ℝ) n).map_add, coeff_C_mul]
  apply add_le_add (geom_product_mono _ _ _ (fun i _ ↦ hknots₀ i) (fun i _ ↦ hknots i) _)
  cases n with
  | zero => simp only [coeff_zero_X_mul, mul_zero, le_refl]
  | succ n =>
    simp only [coeff_succ_X_mul]
    exact mul_le_mul (by linarith)
      (geom_product_mono _ _ _ (fun i _ ↦ hknots₀ i) (fun i _ ↦ hknots i) n)
      (geom_product_nonneg _ _ (fun i _ ↦ hknots₀ i) n) (by positivity)

private theorem coeff_mul_geom (f : ℝ⟦X⟧) (d : ℝ) :
    coeff 0 (f * geom d) = coeff 0 f ∧
      ∀ n : ℕ, coeff (n+1) (f * geom d) = coeff (n+1) f + d * coeff n (f * geom d) := by
  have hcancel : (1 - C d * X) * (f * geom d) = f := calc
    _ = f * (geom d * (1 - C d * X)) := by ac_rfl
    _ = f := by rw [geom_mul_factor, mul_one]
  rw [sub_mul, one_mul, mul_assoc] at hcancel
  have h := sub_eq_iff_eq_add.mp hcancel
  refine ⟨?_, fun n ↦ ?_⟩
  · simpa only [map_add, coeff_C_mul, coeff_zero_X_mul, mul_zero, add_zero] using
      congrArg (coeff 0) h
  · simpa only [map_add, coeff_C_mul, coeff_succ_X_mul] using congrArg (coeff (n+1)) h

private theorem cast_eq_coeff_mul_geom_of_recurrence {N : ℕ} {a b : ℕ → ℚ} {d : ℚ}
    {f : ℝ⟦X⟧} (ha : ∀ n ≤ N, (a n : ℝ) = coeff n f) (hzero : b 0 = a 0)
    (hstep : ∀ n < N, b (n + 1) = a (n + 1) + d * b n) :
    ∀ n ≤ N, (b n : ℝ) = coeff n (f * geom (d : ℝ)) := by
  have hcoeff := coeff_mul_geom f (d : ℝ)
  intro n
  induction n with
  | zero =>
    rw [hzero, hcoeff.1]
    exact fun _ ↦ ha 0 (Nat.zero_le N)
  | succ n ih =>
    intro hn
    have hn' : n < N := Nat.lt_of_succ_le hn
    rw [hstep n hn', Rat.cast_add, Rat.cast_mul, ha (n+1) hn,
      ih (Nat.le_of_lt hn'), hcoeff.2 n]

/-- Rows indexed by the number of processed knots give the exact rational coefficients
through degree `N`. Use row five and add the shifted row six before dividing by
`(n+4)!`. The certificate uses `N = 80`. -/
theorem regularizingCoefficient_eq_of_recurrence (h : ℚ) (N : ℕ) (a : ℕ → ℕ → ℚ)
    (hbase : ∀ n ≤ N, a 0 n = if n = 0 then 1 else 0)
    (hzero : ∀ i : Fin 6, a (i.val+1) 0 = a i.val 0)
    (hstep : ∀ (i : Fin 6) (n : ℕ), n < N →
      a (i.val+1) (n+1) = a i.val (n+1) + regularizingKnotsRat h i * a (i.val+1) n)
    {n : ℕ} (hn : n ≤ N) :
    (((a 5 n + (4*h + 8/3) * (match n with | 0 => 0 | j+1 => a 6 j)) /
      (n+4).factorial : ℚ) : ℝ) = regularizingCoefficient (h : ℝ) n := by
  classical
  have hknots (i : Fin 6) : (regularizingKnotsRat h i : ℝ) = radicandKnots (h : ℝ) i := by
    fin_cases i <;> simp [regularizingKnotsRat, radicandKnots]
  let s (m : ℕ) : Finset (Fin 6) := univ.filter fun i ↦ i.val < m
  let P (m : ℕ) : ℝ⟦X⟧ := ∏ i ∈ s m, geom (radicandKnots (h : ℝ) i)
  have hrow : ∀ m ≤ 6, ∀ j ≤ N, (a m j : ℝ) = coeff j (P m) := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      have hP : P 0 = 1 := by simp [P, s]
      rw [hbase j hj, hP, coeff_one]
      split_ifs <;> simp only [Rat.cast_one, Rat.cast_zero]
    | succ m ih =>
      intro hm
      let i : Fin 6 := ⟨m, Nat.lt_of_succ_le hm⟩
      have hi : i ∉ s m := by simp [s, i]
      have hs : s (m+1) = insert i (s m) := by
        ext j
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        change j.val < m+1 ↔ j.val = m ∨ j.val < m
        omega
      have hP : P (m+1) = P m * geom (regularizingKnotsRat h i : ℝ) := by
        simp only [P, hs, Finset.prod_insert hi, hknots]
        exact mul_comm _ _
      rw [hP]
      exact cast_eq_coeff_mul_geom_of_recurrence (ih (Nat.le_of_succ_le hm)) (hzero i) (hstep i)
  have hs₅ : s 5 = univ.erase (5 : Fin 6) := by
    change (univ.filter fun i : Fin 6 ↦ i.val < 5) = univ.erase (5 : Fin 6)
    decide
  have hs₆ : s 6 = univ := by
    ext i
    simp [s]
  have h₅ := hrow 5 (by decide)
  have h₆ := hrow 6 (by decide)
  simp only [P, hs₅] at h₅
  simp only [P, hs₆] at h₆
  unfold regularizingCoefficient
  rw [map_add, coeff_C_mul]
  cases n with
  | zero =>
    simp only [Rat.cast_div, Rat.cast_natCast, coeff_zero_X_mul, mul_zero, add_zero]
    rw [h₅ 0 hn]
  | succ n =>
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat,
      coeff_succ_X_mul]
    rw [h₅ (n+1) hn, h₆ n (Nat.le_of_lt (Nat.lt_of_succ_le hn))]

private theorem geom_product_le {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i ∧ d i ≤ 9) (n : ℕ) :
    coeff n (∏ i ∈ s, geom (d i)) ≤ ((s.card+n-1).choose n : ℝ) * 9^n := by
  classical
  rw [coeff_prod, ← Finset.card_finsuppAntidiag_nat_eq_choose]
  calc
    _ ≤ ∑ l ∈ s.finsuppAntidiag n, (9 : ℝ)^n := by
      apply Finset.sum_le_sum
      intro l hl
      rw [← (mem_finsuppAntidiag.mp hl).1, ← Finset.prod_pow_eq_pow_sum]
      simp only [geom, coeff_mk]
      apply Finset.prod_le_prod₀
      · intro i hi
        exact pow_nonneg (hd i hi).1 _
      · intro i hi
        exact pow_le_pow_left₀ (hd i hi).1 (hd i hi).2 _
    _ = _ := by simp

private theorem choose_div_factorial (n k : ℕ) :
    ((n+k).choose n : ℝ) / (n+k).factorial =
      1 / ((n.factorial : ℝ) * k.factorial) := by
  rw [Nat.cast_add_choose]
  field_simp

/-- A degree-independent majorant on the compact reciprocal-degree interval. -/
theorem regularizingCoefficient_le {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1) (n : ℕ) :
    regularizingCoefficient h n ≤ (n + 1 : ℝ) * 9^n / n.factorial := by
  have hk (i : Fin 6) : 0 ≤ radicandKnots h i ∧ radicandKnots h i ≤ 9 := by
    fin_cases i <;> norm_num [radicandKnots] <;> constructor <;> linarith
  let s : Finset (Fin 6) := univ.erase 5
  have hs : s.card = 5 := by decide
  have h5 : coeff n (∏ i ∈ s, geom (radicandKnots h i)) ≤
      ((n+4).choose n : ℝ) * 9^n := by
    have hh₅ := geom_product_le s (radicandKnots h) (fun i _ ↦ hk i) n
    rwa [hs, show 5+n-1 = n+4 by omega] at hh₅
  have h5' : coeff n (∏ i ∈ s, geom (radicandKnots h i)) / (n+4).factorial ≤
      9^n / (24 * (n.factorial : ℝ)) := by
    refine (div_le_div_of_nonneg_right h5 (by positivity)).trans_eq ?_
    rw [mul_comm _ (9^n : ℝ), mul_div_assoc, choose_div_factorial]
    norm_num [Nat.factorial]
    ring
  have hkappa : 4*h + 8/3 ≤ 7 := by linarith
  have hshift : coeff n (C (4*h + 8/3) * (X * ∏ i : Fin 6, geom (radicandKnots h i))) /
      (n+4).factorial ≤ (n : ℝ) * 9^n / (n.factorial : ℝ) := by
    cases n with
    | zero => simp
    | succ m =>
      rw [coeff_C_mul, coeff_succ_X_mul]
      have h6 := geom_product_le (univ : Finset (Fin 6)) (radicandKnots h) (fun i _ ↦ hk i) m
      simp only [Finset.card_univ, Fintype.card_fin, show 6+m-1 = m+5 by omega] at h6
      have h6' := mul_le_mul hkappa h6
        (geom_product_nonneg _ _ (fun i _ ↦ (hk i).1) _) (by norm_num : (0 : ℝ) ≤ 7)
      rw [show m+1+4 = m+5 by omega]
      refine (div_le_div_of_nonneg_right h6' (by positivity)).trans ?_
      rw [show (7 : ℝ) * (((m+5).choose m : ℝ) * 9^m) = (7 * 9^m) * ((m+5).choose m : ℝ) by ring,
        mul_div_assoc, choose_div_factorial]
      calc
        _ = (7/120 : ℝ) * (9^m / (m.factorial : ℝ)) := by norm_num [Nat.factorial]; ring
        _ ≤ 9 * ((9 : ℝ)^m / (m.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by
          rw [pow_succ, Nat.factorial_succ]
          push_cast
          field_simp
          <;> ring
  unfold regularizingCoefficient
  rw [map_add, add_div]
  apply (add_le_add h5' hshift).trans
  have h₀ : 0 ≤ (9 : ℝ)^n / (n.factorial : ℝ) := by positivity
  calc
    _ = (((9 : ℝ)^n / (n.factorial : ℝ)) / 24) + n * (9^n / (n.factorial : ℝ)) := by ring
    _ ≤ ((9 : ℝ)^n / (n.factorial : ℝ)) + n * (9^n / (n.factorial : ℝ)) := by linarith
    _ = _ := by ring

/-- The principal part of the rationalized profile has uniform curvature on the tail.
The curvature of the correction term is a separate premise of the tail argument. -/
theorem tail_principal_curvature {c h : ℝ} (hc : 32 ≤ c) (hh : 0 < h) (hh' : h ≤ 1) :
    let b (x : ℝ) := ((1+2*h)/h) * (1 - Real.exp (-3*h*x))
    1/32 < (deriv^[2] b c - deriv b c + b c / 4) / 4 := by
  let b (x : ℝ) := ((1+2*h)/h) * (1 - Real.exp (-3*h*x))
  let k : ℝ := -3*h
  let A : ℝ := (1+2*h)/h
  have hexp (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp (k*y)) (Real.exp (k*x)*k) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul k).exp
  have hb₁ (x : ℝ) : deriv b x = A * (0 - Real.exp (k*x)*k) :=
    (((hasDerivAt_const x (1 : ℝ)).sub (hexp x)).const_mul A).deriv
  have hb₂ : deriv (deriv b) c = A * (0 - Real.exp (k*c)*k*k) := by
    rw [funext hb₁]
    exact (((hasDerivAt_const c (0 : ℝ)).sub ((hexp c).mul_const k)).const_mul A).deriv
  have hformula : (deriv^[2] b c - deriv b c + b c / 4) / 4 =
      (1+2*h)/(16*h) * (1 - (1+6*h)^2 * Real.exp (-3*h*c)) := by
    change (deriv (deriv b) c - deriv b c + b c / 4) / 4 = _
    rw [hb₂, hb₁]
    dsimp [A, b, k]
    field_simp [hh.ne']
    ring
  have hsquare : (1+6*h)^2 ≤ Real.exp (12*h) := by
    have he := Real.add_one_le_exp (6*h)
    calc
      _ ≤ Real.exp (6*h)^2 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  let t := 3*c - 12
  have ht : 2 < t := by dsimp [t]; linarith
  have he : Real.exp (-t) < 1/2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp t]
  have hj := convexOn_exp.2 (Set.mem_univ (-t)) (Set.mem_univ (0 : ℝ))
    hh.le (sub_nonneg.mpr hh') (show h + (1-h) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hj
  have hproduct : (1+6*h)^2 * Real.exp (-3*h*c) ≤ Real.exp (h*(-t)) := by
    calc
      _ ≤ Real.exp (12*h) * Real.exp (-3*h*c) :=
        mul_le_mul_of_nonneg_right hsquare (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hbound : h/2 < 1 - (1+6*h)^2 * Real.exp (-3*h*c) := by
    have hsmall := mul_lt_mul_of_pos_left he hh
    linarith
  change 1/32 < (deriv^[2] b c - deriv b c + b c / 4) / 4
  rw [hformula]
  have ha : h/2 ≤ (1+2*h) * (h/2) := by nlinarith [sq_nonneg h]
  have hb' : (1+2*h) * (h/2) < (1+2*h) *
      (1 - (1+6*h)^2 * Real.exp (-3*h*c)) := mul_lt_mul_of_pos_left hbound (by positivity)
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : 0 < 16*h)]
  linarith [ha.trans_lt hb']

private def remainderMajorant (n : ℕ) : ℝ :=
  (n : ℝ)^4 * (n+1 : ℝ) * 9^n / n.factorial

private theorem remainderMajorant_succ {n : ℕ} (hn : 81 ≤ n) :
    remainderMajorant (n+1) ≤ remainderMajorant n / 2 := by
  have hnr : (81 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsq : ((n : ℝ)+1)^2 ≤ ((3/2 : ℝ)*n)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hprod : 18*((n : ℝ)+1)^2*((n : ℝ)+2) ≤ (n : ℝ)^4 := by
    calc
      _ ≤ 18*(((3/2 : ℝ)*n)^2)*((3/2 : ℝ)*n) := by
        apply mul_le_mul
        · gcongr
        · linarith
        · positivity
        · positivity
      _ = (243/4 : ℝ)*(n : ℝ)^3 := by ring
      _ ≤ (n : ℝ) * (n : ℝ)^3 := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hb : 9*((n : ℝ)+1)^3*((n : ℝ)+2) ≤ (n : ℝ)^4*((n : ℝ)+1)/2 := by
    convert mul_le_mul_of_nonneg_right hprod (show 0 ≤ ((n : ℝ)+1)/2 by positivity) using 1 <;> ring
  calc
    _ = ((9 : ℝ)^n / n.factorial) * (9*((n : ℝ)+1)^3*((n : ℝ)+2)) := by
      unfold remainderMajorant
      rw [pow_succ (9 : ℝ), Nat.factorial_succ]
      push_cast
      field_simp
      <;> ring
    _ ≤ ((9 : ℝ)^n / n.factorial) * ((n : ℝ)^4*((n : ℝ)+1)/2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by unfold remainderMajorant; ring

/-- The common majorant for the discarded terms after degree eighty sums to
less than the rational tolerance used in the compact argument. -/
private theorem compact_series_remainder_majorant :
    Summable (fun n : ℕ ↦ remainderMajorant (n+81)) ∧
      (∑' n : ℕ, remainderMajorant (n+81)) < (2 : ℝ)⁻¹ ^ 100 := by
  let a (n : ℕ) := remainderMajorant (n+81)
  have ha (n : ℕ) : 0 ≤ a n := by dsimp [a, remainderMajorant]; positivity
  have hle (n : ℕ) : a n ≤ a 0 * (1/2 : ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ = remainderMajorant (n+81+1) := by rfl
        _ ≤ a n / 2 := remainderMajorant_succ (by omega)
        _ ≤ (a 0 * (1/2 : ℝ)^n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hsum := (summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ) < 1 by norm_num)).mul_left (a 0)
  have has := Summable.of_nonneg_of_le ha hle hsum
  have h := has.tsum_le_tsum hle hsum
  rw [tsum_mul_left, tsum_geometric_two] at h
  refine ⟨has, h.trans_lt ?_⟩
  dsimp [a, remainderMajorant]
  norm_num [Nat.factorial]

/-- On the near-zero rectangle, the omitted series is bounded even with an
additional fourth-power weight on each coefficient. -/
theorem compact_series_weighted_remainder {h c : ℝ}
    (hh : 0 ≤ h) (hh' : h ≤ 1) (hc : 0 ≤ c) (hc' : c ≤ 1) :
    (∑' n : ℕ, ((n+81 : ℕ) : ℝ)^4 * regularizingCoefficient h (n+81) * c^(n+81)) <
      (2 : ℝ)⁻¹ ^ 100 := by
  let f (n : ℕ) := ((n+81 : ℕ) : ℝ)^4 * regularizingCoefficient h (n+81) * c^(n+81)
  have hf (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (regularizingCoefficient_nonneg hh _)) (pow_nonneg hc _)
  have hle (n : ℕ) : f n ≤ remainderMajorant (n+81) := by
    dsimp only [f]
    have hcoef := regularizingCoefficient_le hh hh' (n+81)
    have hcp : c^(n+81) ≤ 1 := pow_le_one₀ hc hc'
    calc
      _ ≤ ((n+81 : ℕ) : ℝ)^4 * regularizingCoefficient h (n+81) * 1 :=
        mul_le_mul_of_nonneg_left hcp
          (mul_nonneg (by positivity) (regularizingCoefficient_nonneg hh _))
      _ ≤ ((n+81 : ℕ) : ℝ)^4 * (((n+81 : ℕ) : ℝ) + 1) * 9^(n+81) /
          ((n+81).factorial : ℝ) := by
        rw [mul_one]
        have hmul := mul_le_mul_of_nonneg_left hcoef (by positivity :
          0 ≤ ((n+81 : ℕ) : ℝ)^4)
        simpa only [mul_div_assoc, mul_assoc] using hmul
      _ = _ := rfl
  obtain ⟨hs, hbound⟩ := compact_series_remainder_majorant
  exact ((Summable.of_nonneg_of_le hf hle hs).tsum_le_tsum hle hs).trans_lt hbound

#print axioms compact_series_weighted_remainder
#print axioms regularizingCoefficient_le
#print axioms regularizingCoefficient_mono
#print axioms regularizingCoefficient_eq_of_recurrence
#print axioms hasSum_regularizing_series
#print axioms regularizingCoefficient_nonneg
#print axioms tail_principal_curvature
#print axioms rationalized_radicand_lower
#print axioms radicand_moment_nonneg
#print axioms radicand_moment_eq_zero

end RefinedBMV.FourSpectrumLift
