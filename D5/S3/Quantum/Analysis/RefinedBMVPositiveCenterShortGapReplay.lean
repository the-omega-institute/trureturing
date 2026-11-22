/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterShortGapReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify the exact short-gap certificate with the analytic profiles. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapFinite
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapJ
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapProfile
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapSeries

/-! The power coefficients used by the rational certificate are the Taylor
coefficients of the scalar profiles on the actual composition grid. -/

namespace RefinedBMV.PositiveCenter

open Finset Polynomial
open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder (bernsteinCoefficient)
open ShortGapFinite (Coefficients polynomial u t u_eval_grid t_eval_grid bernstein bernstein_eq)
open ShortGapFinite.Revised (Jet bernsteinXRow bernsteinXRow_polynomial tensorBernstein
  fullJet fullJet_polynomial jetRow jetRow_eq_take spacingL1 spacingL1_eq_sum spacingL1_le
  spacingNumerator tailNumerator)

noncomputable section

private def rowEval (y : ℝ) : ℚ[X] →+* ℝ := Polynomial.eval₂RingHom (Rat.castHom ℝ) y

private theorem rowEval_cons (y : ℝ) (a : ℚ) (as : Coefficients) :
    rowEval y (polynomial (a :: as)) = (a : ℝ) + y * rowEval y (polynomial as) := by
  simp [polynomial, ofCoeffList_cons, rowEval, mul_comm, add_comm]

private theorem rowEval_abs_le {y : ℝ} (hy : |y| ≤ 1) (a : Coefficients) :
    |rowEval y (polynomial a)| ≤ (↑(a.map fun z ↦ |z|).sum : ℝ) := by
  induction a with
  | nil => simp [polynomial, rowEval]
  | cons a as ih =>
    rw [rowEval_cons, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_abs]
    refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hy).trans ih

private theorem rowEval_take_error {y : ℝ} (hy : |y| ≤ 1) (a : Coefficients) (n : ℕ) :
    |rowEval y (polynomial a) - rowEval y (polynomial (a.take n))| ≤
      (↑((a.drop n).map fun z ↦ |z|).sum : ℝ) := by
  induction n generalizing a with
  | zero => simpa [polynomial, rowEval] using rowEval_abs_le hy a
  | succ n ih =>
    cases a with
    | nil => simp
    | cons a as =>
      simp only [List.take, List.drop, rowEval_cons, add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hy).trans (ih as)

private def shortGapChartEval (a : ℕ → Coefficients) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ range n, rowEval y (polynomial (a k)) * x ^ k

/-- The certified spacing truncation controls the polynomial difference on the unit square. -/
theorem shortGap_spacing_error (g : Jet) {x y : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    |shortGapChartEval (fullJet g) 19 x y - shortGapChartEval (jetRow g) 19 x y| ≤
      (spacingNumerator g : ℝ) / 10^6 := by
  have hyAbs : |y| ≤ 1 := by rwa [abs_of_nonneg hy]
  unfold shortGapChartEval
  rw [← sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ range 19, (↑(((fullJet g n).drop 7).map fun z ↦ |z|).sum : ℝ) := by
      refine sum_le_sum fun n hn ↦ ?_
      rw [← sub_mul, abs_mul, abs_of_nonneg (pow_nonneg hx _), jetRow_eq_take g n (mem_range.mp hn)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx hx₁)).trans
        (rowEval_take_error hyAbs _ 7)
    _ = (spacingL1 g : ℝ) := by rw [spacingL1_eq_sum, Rat.cast_sum]
    _ ≤ _ := by
      norm_num only [show (10 : ℝ) ^ 6 = 1000000 by norm_num]
      have h : (spacingL1 g : ℝ) ≤ ↑((spacingNumerator g : ℚ) / 1000000) :=
        Rat.cast_le.mpr (spacingL1_le g)
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h

private theorem bernstein_row_lower {a : Coefficients} {n : ℕ} {y : ℝ} {lower : ℚ}
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) (hsize : a.length ≤ n + 1)
    (hcert : ∀ i ≤ n, lower ≤ bernstein a n i) :
    (lower : ℝ) ≤ rowEval y (polynomial a) := by
  have hdeg : ((polynomial a).map (Rat.castHom ℂ)).natDegree ≤ n := by
    refine natDegree_map_le.trans (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_)
    have hlen : a.length ≤ k := hsize.trans (Nat.succ_le_of_lt hk)
    simp [polynomial, coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
  have hab (i : ℕ) (hi : i ≤ n) :
      (lower : ℝ) ≤ (bernsteinCoefficient n i ((polynomial a).map (Rat.castHom ℂ))).re := by
    rw [← bernstein_eq]
    have hb : (lower : ℝ) ≤ (bernstein a n i : ℚ) := by exact_mod_cast hcert i hi
    rwa [← map_ratCast Complex.ofRealHom, show Complex.ofRealHom _ = Complex.ofReal _ from rfl,
      Complex.ofReal_re]
  have h := bernstein_eval_re_lower hdeg hy hy₁ hab
  convert h using 1
  unfold rowEval
  rw [Polynomial.coe_eval₂RingHom, eval_map, eval₂_eq_sum, eval₂_eq_sum]
  simp only [Polynomial.sum, Complex.re_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [show (Rat.castHom ℂ) ((polynomial a).coeff k) =
      Complex.ofReal ((Rat.castHom ℝ) ((polynomial a).coeff k)) by
    exact (map_ratCast Complex.ofRealHom _).symm]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Apply univariate Bernstein bounds in the two coordinates of the gap chart. -/
theorem shortGap_tensor_lower {a : ℕ → Coefficients} {d e : ℕ} {x y : ℝ} {lower : ℚ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1)
    (hsize : ∀ i ≤ d, (bernsteinXRow a d i).length ≤ e + 1)
    (hcert : ∀ i ≤ d, ∀ j ≤ e, lower ≤ tensorBernstein a d e i j) :
    (lower : ℝ) ≤ ∑ k ∈ range (d + 1), rowEval y (polynomial (a k)) * x ^ k := by
  apply bernstein_eval_power_lower _ _ hx hx₁
  intro i hi
  have h := bernstein_row_lower hy hy₁ (hsize i hi) (hcert i hi)
  rw [bernsteinXRow_polynomial, map_sum] at h
  have hconstant (q : ℚ) : rowEval y (C q) = (q : ℝ) := by simp [rowEval]
  simp only [map_mul, hconstant, Rat.cast_div, Rat.cast_natCast] at h
  convert h using 1
  exact sum_congr rfl fun k _ ↦ by ring

open ShortGapFinite.Revised (Jet jetRow budgetRow qRows rRows spacingNumerator tailNumerator
  sqrtComparison sqrtComparison_row_polynomial curvatureComparison curvatureComparison_row_polynomial
  sqrtBernstein_checked sqrtBernstein_row_length curvatureBernstein_checked
  curvatureBernstein_row_length atOne atOne_polynomial endpointL endpointM endpointV
  endpointComparison
  endpointL_polynomial endpointM_polynomial endpointV_polynomial endpointComparison_polynomial)

private abbrev ShortGapXPolynomial := Polynomial (Polynomial ℚ)

private def shortGapRowsX (d : ℕ) (a : ℕ → Coefficients) : ShortGapXPolynomial :=
  ∑ k ∈ range (d + 1), monomial k (polynomial (a k))

private theorem shortGapRowsX_coeff (d : ℕ) (a : ℕ → Coefficients) (n : ℕ) :
    (shortGapRowsX d a).coeff n = if n ≤ d then polynomial (a n) else 0 := by
  simp only [shortGapRowsX, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_range, Nat.lt_succ_iff]

private theorem shortGapRowsX_coeff_of_support (d : ℕ) (a : ℕ → Coefficients)
    (h : ∀ n, d < n → polynomial (a n) = 0) (n : ℕ) :
    (shortGapRowsX d a).coeff n = polynomial (a n) := by
  rw [shortGapRowsX_coeff]
  by_cases hn : n ≤ d
  · rw [if_pos hn]
  · rw [if_neg hn, h n (lt_of_not_ge hn)]

private theorem shortGapRowsX_natDegree (d : ℕ) (a : ℕ → Coefficients) :
    (shortGapRowsX d a).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
  rw [shortGapRowsX_coeff, if_neg (not_le_of_gt hn)]

private theorem shortGapRowsX_list_coeff (d : ℕ) (ws : List Coefficients)
    (hsize : ws.length ≤ d + 1) (n : ℕ) :
    (shortGapRowsX d (fun k ↦ ws.getD k [])).coeff n = polynomial (ws.getD n []) := by
  apply shortGapRowsX_coeff_of_support
  intro k hk
  have hnone : ws[k]? = none := List.getElem?_eq_none (hsize.trans (Nat.succ_le_of_lt hk))
  simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none, polynomial, ofCoeffList_nil]

private def shortGapJetX (g : Jet) : ShortGapXPolynomial := shortGapRowsX 18 (jetRow g)

private def shortGapQX : ShortGapXPolynomial := shortGapRowsX 6 (fun k ↦ qRows.getD k [])

private def shortGapRX : ShortGapXPolynomial := shortGapRowsX 1 (fun k ↦ rRows.getD k [])

private def shortGapBudgetX (g : Jet) : ShortGapXPolynomial :=
  C (C ((spacingNumerator g : ℚ) / 1000000)) +
    monomial 19 (C ((tailNumerator g : ℚ) / 1000000))

private theorem shortGapJetX_coeff (g : Jet) (n : ℕ) :
    (shortGapJetX g).coeff n = polynomial (jetRow g n) := by
  unfold shortGapJetX
  apply shortGapRowsX_coeff_of_support
  intro k hk
  rw [jetRow, if_neg (show ¬k < 19 by omega), polynomial, ofCoeffList_nil]

private theorem shortGapQX_coeff (n : ℕ) :
    shortGapQX.coeff n = polynomial (qRows.getD n []) :=
  shortGapRowsX_list_coeff 6 qRows (by decide) n

private theorem shortGapRX_coeff (n : ℕ) :
    shortGapRX.coeff n = polynomial (rRows.getD n []) :=
  shortGapRowsX_list_coeff 1 rRows (by decide) n

private theorem shortGapBudgetX_coeff (g : Jet) (n : ℕ) :
    (shortGapBudgetX g).coeff n = polynomial (budgetRow g n) := by
  by_cases h₀ : n = 0
  · subst n
    simp [shortGapBudgetX, budgetRow, polynomial, ofCoeffList_cons, coeff_monomial]
  · by_cases h₁₉ : n = 19
    · subst n
      simp [shortGapBudgetX, budgetRow, polynomial, ofCoeffList_cons, coeff_monomial]
    · simp [shortGapBudgetX, budgetRow, polynomial, coeff_C, coeff_monomial,
        h₀, h₁₉, Ne.symm h₁₉]

private theorem shortGapBudgetX_natDegree (g : Jet) : (shortGapBudgetX g).natDegree ≤ 19 := by
  rw [shortGapBudgetX, natDegree_C_add]
  exact natDegree_monomial_le _

private theorem shortGapX_coeff_mul (F G : ShortGapXPolynomial) (n : ℕ) :
    (F * G).coeff n = ∑ k ∈ range (n + 1), F.coeff k * G.coeff (n - k) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem shortGapX_coeff_shift (F : ShortGapXPolynomial) (n : ℕ) :
    (X * F).coeff n = if n = 0 then 0 else F.coeff (n - 1) := by
  cases n with
  | zero => simp [coeff_X_mul_zero]
  | succ n => simp only [coeff_X_mul, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]

private def shortGapSqrtX : ShortGapXPolynomial :=
  shortGapJetX .value - shortGapBudgetX .value - shortGapQX ^ 2

private def shortGapCurvatureX : ShortGapXPolynomial :=
  shortGapQX * (shortGapJetX .corrected - shortGapBudgetX .corrected) -
    ((1 - X * shortGapRX) * shortGapJetX .first + X * shortGapJetX .second +
      C (C (1 / 2 : ℚ)) * (X * (shortGapRX * (shortGapRX * shortGapJetX .value)))) -
    (shortGapBudgetX .first + shortGapBudgetX .second + C (C (2 : ℚ)) * shortGapBudgetX .value)

private theorem shortGapSqrtX_coeff (n : ℕ) :
    shortGapSqrtX.coeff n = polynomial (sqrtComparison n) := by
  rw [sqrtComparison_row_polynomial]
  simp only [shortGapSqrtX, coeff_sub, pow_two, shortGapX_coeff_mul,
    shortGapJetX_coeff, shortGapBudgetX_coeff, shortGapQX_coeff]

private theorem shortGapCurvatureX_coeff (n : ℕ) :
    shortGapCurvatureX.coeff n = polynomial (curvatureComparison n) := by
  have hfirst : (1 - X * shortGapRX) * shortGapJetX .first =
      shortGapJetX .first - X * (shortGapRX * shortGapJetX .first) := by
    rw [sub_mul, one_mul, mul_assoc]
  rw [curvatureComparison_row_polynomial]
  simp only [shortGapCurvatureX, hfirst, coeff_sub, coeff_add, coeff_C_mul, shortGapX_coeff_shift]
  simp only [shortGapX_coeff_mul, coeff_sub, shortGapJetX_coeff, shortGapBudgetX_coeff,
    shortGapQX_coeff, shortGapRX_coeff]

private theorem shortGapSqrtX_natDegree : shortGapSqrtX.natDegree ≤ 19 := by
  have hP : (shortGapJetX .value).natDegree ≤ 18 := shortGapRowsX_natDegree _ _
  have hq : shortGapQX.natDegree ≤ 6 := shortGapRowsX_natDegree _ _
  have hq₂ : (shortGapQX ^ 2).natDegree ≤ 12 := natDegree_pow_le_of_le 2 hq
  exact (natDegree_sub_le_of_le
    (natDegree_sub_le_of_le hP (shortGapBudgetX_natDegree _)) hq₂).trans (by decide)

private theorem shortGapCurvatureX_natDegree : shortGapCurvatureX.natDegree ≤ 25 := by
  have hP (g : Jet) : (shortGapJetX g).natDegree ≤ 18 := shortGapRowsX_natDegree _ _
  have hb := shortGapBudgetX_natDegree
  have hq : shortGapQX.natDegree ≤ 6 := shortGapRowsX_natDegree _ _
  have hr : shortGapRX.natDegree ≤ 1 := shortGapRowsX_natDegree _ _
  have hx : (X : ShortGapXPolynomial).natDegree ≤ 1 := natDegree_X_le
  have h1 : (1 - X * shortGapRX).natDegree ≤ 2 :=
    (natDegree_sub_le_of_le (natDegree_one (R := Polynomial ℚ)).le
      (natDegree_mul_le_of_le hx hr)).trans (by decide)
  have hfirst : ((1 - X * shortGapRX) * shortGapJetX .first).natDegree ≤ 20 :=
    natDegree_mul_le_of_le h1 (hP _)
  have hsecond : (X * shortGapJetX .second).natDegree ≤ 19 :=
    natDegree_mul_le_of_le hx (hP _)
  have hvalue : (C (C (1 / 2 : ℚ)) *
      (X * (shortGapRX * (shortGapRX * shortGapJetX .value)))).natDegree ≤ 21 :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le hx (natDegree_mul_le_of_le hr (natDegree_mul_le_of_le hr (hP _))))
  have hmain : ((1 - X * shortGapRX) * shortGapJetX .first + X * shortGapJetX .second +
      C (C (1 / 2 : ℚ)) * (X * (shortGapRX * (shortGapRX * shortGapJetX .value)))).natDegree ≤ 21 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (hfirst.trans (by decide)) (hsecond.trans (by decide)))
      hvalue
  have herr : (shortGapBudgetX .first + shortGapBudgetX .second +
      C (C (2 : ℚ)) * shortGapBudgetX .value).natDegree ≤ 19 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hb _) (hb _))
      ((natDegree_C_mul_le _ _).trans (hb _))
  have hc : (shortGapQX * (shortGapJetX .corrected - shortGapBudgetX .corrected)).natDegree ≤ 25 :=
    (natDegree_mul_le_of_le hq (natDegree_sub_le_of_le (hP _) (hb _))).trans (by decide)
  exact (natDegree_sub_le_of_le (natDegree_sub_le_of_le hc hmain) herr).trans (by decide)

private def shortGapXEval (x y : ℝ) : ShortGapXPolynomial →+* ℝ :=
  Polynomial.eval₂RingHom (rowEval y) x

private theorem shortGapXEval_eq_chart {F : ShortGapXPolynomial} {a : ℕ → Coefficients} {d : ℕ}
    (hF : F.natDegree ≤ d) (ha : ∀ n, F.coeff n = polynomial (a n)) (x y : ℝ) :
    shortGapXEval x y F = shortGapChartEval a (d + 1) x y := by
  change Polynomial.eval₂ (rowEval y) x F = _
  rw [Polynomial.eval₂_eq_sum_range' (rowEval y) (Nat.lt_succ_of_le hF) x]
  simp only [shortGapChartEval, ha]

private theorem shortGapRowEval_C (y : ℝ) (c : ℚ) : rowEval y (C c) = (c : ℝ) := by
  simp only [rowEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Rat.coe_castHom]

private theorem shortGapXEval_C (x y : ℝ) (c : ℚ) :
    shortGapXEval x y (C (C c)) = (c : ℝ) := by
  simp only [shortGapXEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, shortGapRowEval_C]

private theorem shortGapXEval_X (x y : ℝ) : shortGapXEval x y X = x :=
  Polynomial.eval₂_X _ _

/-- The error budget in the normalized argument, including its degree-19 tail. -/
def shortGapBudgetEval (g : Jet) (x : ℝ) : ℝ :=
  (spacingNumerator g : ℝ) / 10 ^ 6 + (tailNumerator g : ℝ) / 10 ^ 6 * x ^ 19

private theorem shortGapBudgetX_eval (g : Jet) (x y : ℝ) :
    shortGapXEval x y (shortGapBudgetX g) = shortGapBudgetEval g x := by
  have hmono : shortGapXEval x y (monomial 19 (C ((tailNumerator g : ℚ) / 1000000))) =
      rowEval y (C ((tailNumerator g : ℚ) / 1000000)) * x ^ 19 :=
    Polynomial.eval₂_monomial _ _
  have hden : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  simp only [shortGapBudgetX, map_add, shortGapXEval_C, hmono, shortGapRowEval_C,
    shortGapBudgetEval, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, hden]

private theorem shortGapJetX_eval (g : Jet) (x y : ℝ) :
    shortGapXEval x y (shortGapJetX g) = shortGapChartEval (jetRow g) 19 x y :=
  shortGapXEval_eq_chart (shortGapRowsX_natDegree _ _) (shortGapJetX_coeff g) x y

/-- The square-root tensor evaluates to the lower marginal enclosure minus q squared. -/
theorem shortGap_sqrtComparison_eval (x y : ℝ) :
    shortGapChartEval sqrtComparison 20 x y =
      shortGapChartEval (jetRow .value) 19 x y - shortGapBudgetEval .value x -
        shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y ^ 2 := by
  rw [← shortGapXEval_eq_chart shortGapSqrtX_natDegree shortGapSqrtX_coeff x y]
  have hq : shortGapXEval x y shortGapQX = shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y :=
    shortGapXEval_eq_chart (shortGapRowsX_natDegree _ _) shortGapQX_coeff x y
  simp only [shortGapSqrtX, map_sub, map_pow, hq, shortGapJetX_eval, shortGapBudgetX_eval]

/-- The curvature tensor evaluates to the exact margin in the discriminant enclosure. -/
theorem shortGap_curvatureComparison_eval (x y : ℝ) :
    let P (g : Jet) := shortGapChartEval (jetRow g) 19 x y
    let b (g : Jet) := shortGapBudgetEval g x
    let q := shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y
    let r := shortGapChartEval (fun k ↦ rRows.getD k []) 2 x y
    shortGapChartEval curvatureComparison 26 x y =
      (P .corrected - b .corrected) * q -
        ((1 - x * r) * P .first + x * P .second + (x * r ^ 2 / 2) * P .value) -
        (b .first + b .second + 2 * b .value) := by
  dsimp only
  rw [← shortGapXEval_eq_chart shortGapCurvatureX_natDegree shortGapCurvatureX_coeff x y]
  have hq : shortGapXEval x y shortGapQX = shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y :=
    shortGapXEval_eq_chart (shortGapRowsX_natDegree _ _) shortGapQX_coeff x y
  have hr : shortGapXEval x y shortGapRX = shortGapChartEval (fun k ↦ rRows.getD k []) 2 x y :=
    shortGapXEval_eq_chart (shortGapRowsX_natDegree _ _) shortGapRX_coeff x y
  simp only [shortGapCurvatureX, map_sub, map_add, map_mul, map_one, shortGapXEval_C, shortGapXEval_X,
    shortGapJetX_eval, shortGapBudgetX_eval, hq, hr, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

/-- Transfer the checked square-root tensor bound to the factored margin. -/
theorem shortGap_sqrtComparison_lower {x y : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    ((3 / 5000 : ℚ) : ℝ) ≤
      shortGapChartEval (jetRow .value) 19 x y - shortGapBudgetEval .value x -
        shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y ^ 2 := by
  rw [← shortGap_sqrtComparison_eval]
  exact shortGap_tensor_lower (a := sqrtComparison) (d := 19) (e := 6) hx hx₁ hy hy₁
    (fun _ hi ↦ sqrtBernstein_row_length hi) (fun _ hi _ hj ↦ (sqrtBernstein_checked hi hj).le)

/-- Transfer the checked curvature tensor bound to the factored margin. -/
theorem shortGap_curvatureComparison_lower {x y : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    let P (g : Jet) := shortGapChartEval (jetRow g) 19 x y
    let b (g : Jet) := shortGapBudgetEval g x
    let q := shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y
    let r := shortGapChartEval (fun k ↦ rRows.getD k []) 2 x y
    ((7 / 2000 : ℚ) : ℝ) ≤ (P .corrected - b .corrected) * q -
      ((1 - x * r) * P .first + x * P .second + (x * r ^ 2 / 2) * P .value) -
      (b .first + b .second + 2 * b .value) := by
  dsimp only
  rw [← shortGap_curvatureComparison_eval]
  exact shortGap_tensor_lower (a := curvatureComparison) (d := 25) (e := 8) hx hx₁ hy hy₁
    (fun _ hi ↦ curvatureBernstein_row_length hi)
    (fun _ hi _ hj ↦ (curvatureBernstein_checked hi hj).le)

private theorem shortGap_atOne_eval {F : ShortGapXPolynomial} {a : ℕ → Coefficients}
    (hF : F.natDegree ≤ 19) (ha : ∀ n, F.coeff n = polynomial (a n)) (y : ℝ) :
    rowEval y (polynomial (atOne a)) = shortGapXEval 1 y F := by
  rw [shortGapXEval_eq_chart hF ha 1 y]
  simp only [atOne_polynomial, map_sum, shortGapChartEval, one_pow, mul_one]

private theorem shortGap_atOne_jet_eval (g : Jet) (y : ℝ) :
    rowEval y (polynomial (atOne (jetRow g))) = shortGapChartEval (jetRow g) 19 1 y := by
  have hd : (shortGapJetX g).natDegree ≤ 18 := shortGapRowsX_natDegree _ _
  rw [shortGap_atOne_eval (hd.trans (by decide)) (shortGapJetX_coeff g), shortGapJetX_eval]

private theorem shortGap_atOne_budget_eval (g : Jet) (y : ℝ) :
    rowEval y (polynomial (atOne (budgetRow g))) = shortGapBudgetEval g 1 := by
  rw [shortGap_atOne_eval (shortGapBudgetX_natDegree g) (shortGapBudgetX_coeff g),
    shortGapBudgetX_eval]

theorem shortGap_endpointL_eval (y : ℝ) :
    rowEval y (polynomial endpointL) =
      2 * ((shortGapChartEval (jetRow .value) 19 1 y + shortGapChartEval (jetRow .first) 19 1 y) -
        (shortGapBudgetEval .value 1 + shortGapBudgetEval .first 1)) := by
  simp only [endpointL_polynomial, map_mul, map_sub, map_add, shortGapRowEval_C,
    Rat.cast_ofNat, shortGap_atOne_jet_eval, shortGap_atOne_budget_eval]

theorem shortGap_endpointM_eval (y : ℝ) :
    rowEval y (polynomial endpointM) =
      shortGapChartEval (jetRow .value) 19 1 y + shortGapBudgetEval .value 1 := by
  simp only [endpointM_polynomial, map_add, shortGap_atOne_jet_eval, shortGap_atOne_budget_eval]

theorem shortGap_endpointV_eval (y : ℝ) :
    rowEval y (polynomial endpointV) = shortGapChartEval (jetRow .slope) 19 1 y := by
  rw [endpointV_polynomial, shortGap_atOne_jet_eval]

/-- The endpoint comparison uses the slope row with its error budget added. -/
theorem shortGap_endpointComparison_eval (y : ℝ) :
    let L := rowEval y (polynomial endpointL)
    let M := rowEval y (polynomial endpointM)
    let V := rowEval y (polynomial endpointV) + shortGapBudgetEval .slope 1
    rowEval y (polynomial endpointComparison) = L ^ 2 - 4 * M * V ^ 2 := by
  dsimp only
  simp only [endpointComparison_polynomial, map_sub, map_mul, map_pow, map_add, shortGapRowEval_C,
    Rat.cast_ofNat, shortGap_atOne_budget_eval, mul_assoc]

/-- The marginal profile coefficients after the change of variable `t = 2x`. -/
theorem shortGapFinite_u_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (↑((polynomial (u n)).eval (11 / (p : ℚ))) : ℝ) = 2 ^ n * shortGapUCoeff p 0 n := by
  rw [u_eval_grid hp]
  push_cast
  rw [shortGapUCoeff, Nat.add_zero]
  change _ = 2 ^ n * ((3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) / 2 *
    (shortGapRawMoment p (n + 2) - 1) / ((n : ℝ) + 1) / ((n : ℝ) + 2) /
      (n.factorial : ℝ))
  have hmoment := shortGapScaledMoment_grid hp (n + 2)
  dsimp only at hmoment
  rw [hmoment, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [div_div, div_div]
  ring

/-- The geometric profile coefficients after the change of variable `t = 2x`. -/
theorem shortGapFinite_t_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (↑((polynomial (t n)).eval (11 / (p : ℚ))) : ℝ) =
      2 ^ n * geometricCoeff p (3 / (p : ℝ)) 0 n := by
  rw [t_eval_grid hp]
  push_cast
  rw [geometricCoeff, Nat.add_zero]
  have hshift (i : ℕ) : 2 * (3 / (p : ℝ) * i) - 3 = 2 * (3 / (p : ℝ) * i - 3 / 2) := by
    ring
  simp_rw [hshift, show -3 - 2 * (3 / (p : ℝ)) = 2 * (-(3 / 2 + 3 / (p : ℝ))) by ring,
    mul_pow, ← Finset.mul_sum]
  ring

/-- The list coefficients of the differentiated marginal match its real Taylor coefficients. -/
theorem shortGapFinite_u_deriv_eq {p : ℕ} (hp : 0 < p) (k n : ℕ) :
    (↑(((n + k).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ k) *
      (polynomial (u (n + k))).eval (11 / (p : ℚ))) : ℝ) = 2 ^ n * shortGapUCoeff p k n := by
  push_cast
  rw [shortGapFinite_u_eq hp, pow_add]
  simp only [shortGapUCoeff, Nat.add_zero]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn, hk]

/-- The list coefficients of the differentiated geometric profile match its real series. -/
theorem shortGapFinite_t_deriv_eq {p : ℕ} (hp : 0 < p) (k n : ℕ) :
    (↑(((n + k).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ k) *
      (polynomial (t (n + k))).eval (11 / (p : ℚ))) : ℝ) =
      2 ^ n * geometricCoeff p (3 / (p : ℝ)) k n := by
  push_cast
  rw [shortGapFinite_t_eq hp, pow_add]
  simp only [geometricCoeff, Nat.add_zero]
  suffices h : ∀ a : ℝ, ((n + k).factorial : ℝ) / ((n.factorial : ℝ) * 2 ^ k) *
      (2 ^ n * 2 ^ k * (a / ((n + k).factorial : ℝ))) = 2 ^ n * (a / (n.factorial : ℝ)) by
    exact h _
  intro a
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn, hk] <;> ring

private theorem rowEval_grid (p : ℕ) (a : ℚ[X]) :
    rowEval (11 / (p : ℝ)) a = (↑(a.eval (11 / (p : ℚ))) : ℝ) := by
  change a.eval₂ (Rat.castHom ℝ) (11 / (p : ℝ)) = _
  rw [show (11 / (p : ℝ)) = Rat.castHom ℝ (11 / (p : ℚ)) by simp, eval₂_at_apply]
  rfl

private def chartJetCoeff (p : ℕ) (g : Jet) (n : ℕ) : ℝ :=
  match g with
  | .value => 2 ^ n * shortGapUCoeff p 0 n
  | .first => 2 ^ n * shortGapUCoeff p 1 n
  | .second => 2 ^ n * shortGapUCoeff p 2 n
  | .corrected => 2 ^ n * geometricCoeff p (3 / (p : ℝ)) 2 n - (if n = 0 then 1 / 200 else 0)
  | .slope => 2 ^ n * geometricCoeff p (3 / (p : ℝ)) 1 n

/-- Evaluation of the unprojected certificate coefficients on the composition grid. -/
theorem shortGap_fullJet_eq {p : ℕ} (hp : 0 < p) (g : Jet) (n : ℕ) :
    rowEval (11 / (p : ℝ)) (polynomial (fullJet g n)) = chartJetCoeff p g n := by
  have hderiv (a : ℕ → Coefficients) (k : ℕ) :
      rowEval (11 / (p : ℝ))
        (C (((n + k).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ k)) * polynomial (a (n + k))) =
      (↑(((n + k).factorial : ℚ) / ((n.factorial : ℚ) * 2 ^ k) *
        (polynomial (a (n + k))).eval (11 / (p : ℚ))) : ℝ) := by
    rw [rowEval_grid, eval_mul, eval_C]
  rw [fullJet_polynomial]
  cases g
  · rw [rowEval_grid]
    exact shortGapFinite_u_eq hp n
  · rw [hderiv]
    exact shortGapFinite_u_deriv_eq hp 1 n
  · rw [hderiv]
    exact shortGapFinite_u_deriv_eq hp 2 n
  · rw [map_sub, hderiv, shortGapFinite_t_deriv_eq hp, rowEval_grid, eval_C]
    by_cases hn : n = 0 <;> simp [chartJetCoeff, hn]
  · rw [hderiv]
    exact shortGapFinite_t_deriv_eq hp 1 n

/-- The three marginal series in the normalized argument. -/
theorem shortGapU_chart_series {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    let a (k n : ℕ) := 2 ^ n * shortGapUCoeff p k n * x ^ n
    HasSum (a 0) (shortGapProfileU p (2 * x)) ∧
    HasSum (a 1) (deriv (shortGapProfileU p) (2 * x)) ∧
    HasSum (a 2) (deriv (deriv (shortGapProfileU p)) (2 * x)) := by
  dsimp only
  obtain ⟨h₀, h₁, h₂⟩ := shortGapProfileU_series hp (show 0 < 2 * x by positivity)
  refine ⟨h₀.congr_fun fun n ↦ ?_, h₁.congr_fun fun n ↦ ?_, h₂.congr_fun fun n ↦ ?_⟩
  · simp only [shortGapUCoeff, Nat.add_zero, mul_pow, div_div]
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [show ((n : ℝ) + 1 + 1) * (((n : ℝ) + 1) * (n.factorial : ℝ)) =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * (n.factorial : ℝ) by ring]
    ring
  · simp only [shortGapUCoeff, mul_pow, Nat.cast_add, Nat.cast_one, div_div]
    rw [show ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) =
      ((n : ℝ) + 2) * ((n : ℝ) + 3) by ring]
    ring
  · simp only [shortGapUCoeff, mul_pow, Nat.cast_add, Nat.cast_ofNat, div_div]
    rw [show ((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) =
      ((n : ℝ) + 3) * ((n : ℝ) + 4) by ring]
    ring

/-- The geometric slope and curvature series in the normalized argument. -/
theorem shortGapT_chart_series (p : ℕ) (h x : ℝ) :
    let a (k n : ℕ) := 2 ^ n * geometricCoeff p h k n * x ^ n
    HasSum (a 1) (deriv (shortGapProfileT p h) (2 * x)) ∧
    HasSum (a 2) (deriv (deriv (shortGapProfileT p h)) (2 * x)) := by
  obtain ⟨_, h₁, h₂⟩ := shortGapProfileT_series p h (2 * x)
  refine ⟨h₁.congr_fun fun n ↦ ?_, h₂.congr_fun fun n ↦ ?_⟩ <;>
    simp only [geometricCoeff, mul_pow] <;> ring

/-- Analytic truncation errors for the three marginal jets through degree 18. -/
theorem shortGapU_chart_tail {p : ℕ} (hp : 11 ≤ p) {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) :
    let truncation (k : ℕ) := ∑ n ∈ range 19, 2 ^ n * shortGapUCoeff p k n * x ^ n
    |shortGapProfileU p (2 * x) - truncation 0| ≤ 154 / 10^6 * x^19 ∧
    |deriv (shortGapProfileU p) (2 * x) - truncation 1| ≤ 419 / 10^6 * x^19 ∧
    |deriv (deriv (shortGapProfileU p)) (2 * x) - truncation 2| ≤ 1146 / 10^6 * x^19 := by
  let K (k : ℕ) : ℝ := 9 * 3 ^ k / (20 + k) / (21 + k)
  have hp₀ : 0 < p := by omega
  obtain ⟨h₀, h₁, h₂⟩ := shortGapU_chart_series hp₀ hx
  have hb (k n : ℕ) (hn : 19 ≤ n) :
      |2 ^ n * shortGapUCoeff p k n| ≤ K k * 6 ^ n / (n.factorial : ℝ) := calc
    _ = 2 ^ n * |shortGapUCoeff p k n| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)^n)]
    _ ≤ 2 ^ n * (K k * (3 ^ n / (n.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left (shortGapUCoeff_tail_majorant hp k hn) (by positivity)
    _ = _ := by rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]; ring
  have htail (k : ℕ) {value : ℝ}
      (hs : HasSum (fun n ↦ 2 ^ n * shortGapUCoeff p k n * x ^ n) value) :=
    shortGap_factorial_tail hx.le hx₁ (show 0 ≤ K k by dsimp [K]; positivity)
      (by norm_num : (0 : ℝ) ≤ 6) (by norm_num) hs (hb k)
  refine ⟨(htail 0 h₀).trans ?_, (htail 1 h₁).trans ?_, (htail 2 h₂).trans ?_⟩ <;>
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx.le _) <;>
    norm_num [K, Nat.factorial]

/-- Analytic truncation errors for the geometric slope and curvature through degree 18. -/
theorem shortGapT_chart_tail {p : ℕ} {h x : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 3/11)
    (hgrid : h * (p : ℝ) = 3) (hx : 0 ≤ x) (hx₁ : x ≤ 1) :
    let truncation (k : ℕ) := ∑ n ∈ range 19, 2 ^ n * geometricCoeff p h k n * x ^ n
    |deriv (shortGapProfileT p h) (2 * x) - truncation 1| ≤ 3 / 10^6 * x^19 ∧
    |deriv (deriv (shortGapProfileT p h)) (2 * x) - truncation 2| ≤ 5 / 10^6 * x^19 := by
  obtain ⟨h₁, h₂⟩ := shortGapT_chart_series p h x
  have hscale (k n : ℕ) {K : ℝ}
      (hb : |geometricCoeff p h k n| ≤ K * ((9/5)^n / (n.factorial : ℝ))) :
      |2 ^ n * geometricCoeff p h k n| ≤ K * (18/5)^n / (n.factorial : ℝ) := calc
    _ = 2 ^ n * |geometricCoeff p h k n| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)^n)]
    _ ≤ 2 ^ n * (K * ((9/5)^n / (n.factorial : ℝ))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [show (18/5 : ℝ) = 2 * (9/5) by norm_num, mul_pow]; ring
  have htail₁ := shortGap_factorial_tail hx hx₁ (by norm_num : (0 : ℝ) ≤ 6)
    (by norm_num : (0 : ℝ) ≤ 18/5) (by norm_num) h₁
    (fun n _ ↦ hscale 1 n (shortGap_profileT_majorants hh hh₁ hgrid n).1)
  have htail₂ := shortGap_factorial_tail hx hx₁ (by norm_num : (0 : ℝ) ≤ 11)
    (by norm_num : (0 : ℝ) ≤ 18/5) (by norm_num) h₂ (fun n hn ↦ hscale 2 n (by
      have hn₀ : n ≠ 0 := by omega
      simpa only [if_neg hn₀, sub_zero] using (shortGap_profileT_majorants hh hh₁ hgrid n).2))
  refine ⟨htail₁.trans ?_, htail₂.trans ?_⟩ <;>
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx _) <;>
    norm_num [Nat.factorial]

private def chartJetValue (p : ℕ) (g : Jet) (x : ℝ) : ℝ :=
  match g with
  | .value => shortGapProfileU p (2 * x)
  | .first => deriv (shortGapProfileU p) (2 * x)
  | .second => deriv (deriv (shortGapProfileU p)) (2 * x)
  | .corrected => deriv (deriv (shortGapProfileT p (3 / (p : ℝ)))) (2 * x) - 1 / 200
  | .slope => deriv (shortGapProfileT p (3 / (p : ℝ))) (2 * x)

private theorem shortGap_chart_analytic_tail {p : ℕ} (hp : 11 ≤ p) (g : Jet) {x : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) :
    |chartJetValue p g x - ∑ n ∈ range 19, chartJetCoeff p g n * x ^ n| ≤
      (tailNumerator g : ℝ) / 10 ^ 6 * x ^ 19 := by
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hp₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  let h : ℝ := 3 / (p : ℝ)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hh₁ : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁
  have hgrid : h * (p : ℝ) = 3 := div_mul_cancel₀ 3 hpR.ne'
  have hU := shortGapProfileU_contDiff p
  have closeBound {f : ℝ → ℝ} {k : ℕ} {c : ℝ} (hcont : Continuous f)
      (hb : ∀ z ∈ Set.Ioc (0 : ℝ) 1,
        |f (2 * z) - ∑ n ∈ range 19, 2 ^ n * shortGapUCoeff p k n * z ^ n| ≤ c * z ^ 19) :
      |f (2 * x) - ∑ n ∈ range 19, 2 ^ n * shortGapUCoeff p k n * x ^ n| ≤ c * x ^ 19 := by
    let S : Set ℝ := {z | |f (2 * z) - ∑ n ∈ range 19, 2 ^ n * shortGapUCoeff p k n * z ^ n| ≤ c * z ^ 19}
    have hclosed : IsClosed S := isClosed_le (by fun_prop) (by fun_prop)
    have hsub := closure_minimal (show Set.Ioc (0 : ℝ) 1 ⊆ S from hb) hclosed
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hsub
    exact hsub ⟨hx, hx₁⟩
  cases g with
  | value =>
    exact closeBound hU.continuous (fun z hz ↦ (shortGapU_chart_tail hp hz.1 hz.2).1)
  | first =>
    exact closeBound (hU.continuous_deriv (by norm_num))
      (fun z hz ↦ (shortGapU_chart_tail hp hz.1 hz.2).2.1)
  | second =>
    have h₂ : ContDiff ℝ 1 (deriv (shortGapProfileU p)) :=
      (show ContDiff ℝ (1 + 1) (shortGapProfileU p) from hU).deriv'
    exact closeBound (h₂.continuous_deriv (by norm_num))
      (fun z hz ↦ (shortGapU_chart_tail hp hz.1 hz.2).2.2)
  | slope => exact (shortGapT_chart_tail hh hh₁ hgrid hx hx₁).1
  | corrected =>
    have htail := (shortGapT_chart_tail hh hh₁ hgrid hx hx₁).2
    have hone : (∑ n ∈ range 19, (if n = 0 then (1 / 200 : ℝ) else 0) * x ^ n) = 1 / 200 := by
      rw [sum_eq_single_of_mem 0 (by simp)]
      · simp
      · intro n _ hn
        simp [hn]
    simp only [chartJetValue, chartJetCoeff, sub_mul, sum_sub_distrib, hone, tailNumerator]
    convert htail using 2 <;> ring

/-- The five projection polynomials approximate the actual jets on the entire gap interval. -/
theorem shortGap_jet_enclosure {p : ℕ} (hp : 11 ≤ p) (g : Jet) {x : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) :
    |chartJetValue p g x - shortGapChartEval (jetRow g) 19 x (11 / (p : ℝ))| ≤
      (spacingNumerator g : ℝ) / 10 ^ 6 + (tailNumerator g : ℝ) / 10 ^ 6 * x ^ 19 := by
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hp₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hy₁ : 11 / (p : ℝ) ≤ 1 := (div_le_one hpR).mpr hp₁
  have hs := shortGap_spacing_error g hx hx₁ (by positivity) hy₁
  have ht := shortGap_chart_analytic_tail hp g hx hx₁
  have he : shortGapChartEval (fullJet g) 19 x (11 / (p : ℝ)) =
      ∑ n ∈ range 19, chartJetCoeff p g n * x ^ n := by
    simp only [shortGapChartEval, shortGap_fullJet_eq hp₀]
  rw [← he] at ht
  calc
    _ ≤ _ := abs_sub_le _ (shortGapChartEval (fullJet g) 19 x (11 / (p : ℝ))) _
    _ ≤ _ := add_le_add ht hs
    _ = _ := add_comm _ _

/-- A quadratic majorant of the marginal curvature gives the discriminant sign. -/
theorem shortGap_discriminant_of_square {x U U₁ U₂ A q r : ℝ}
    (hx : 0 ≤ x) (hU : 0 < U) (hqU : q ^ 2 ≤ U)
    (hcurv : 0 ≤ 4 * U * U₁ + 2 * x * (2 * U * U₂ - U₁ ^ 2))
    (hupper : (1 - x * r) * U₁ + x * U₂ + (x * r ^ 2 / 2) * U < A * q) :
    0 < 16 * U ^ 3 * A ^ 2 - (4 * U * U₁ + 2 * x * (2 * U * U₂ - U₁ ^ 2)) ^ 2 := by
  let B := 4 * U * U₁ + 2 * x * (2 * U * U₂ - U₁ ^ 2)
  let R := (1 - x * r) * U₁ + x * U₂ + (x * r ^ 2 / 2) * U
  have hfactor : 0 < 4 * U := by positivity
  have hB : B ≤ (4 * U) * R := calc
    _ ≤ B + 2 * x * (U₁ - r * U) ^ 2 := le_add_of_nonneg_right (by positivity)
    _ = _ := by dsimp [B, R]; ring
  have hR : 0 ≤ R := (mul_nonneg_iff_of_pos_left hfactor).mp (hcurv.trans hB)
  have hAq : 0 < A * q := hR.trans_lt hupper
  have hleft : B < (4 * U) * (A * q) := hB.trans_lt (mul_lt_mul_of_pos_left hupper hfactor)
  have hsq : B ^ 2 < ((4 * U) * (A * q)) ^ 2 := by
    apply sq_lt_sq.mpr
    rwa [abs_of_nonneg hcurv, abs_of_pos (mul_pos hfactor hAq)]
  apply sub_pos.mpr
  refine hsq.trans_le ?_
  calc
    _ = (16 * U ^ 2 * A ^ 2) * q ^ 2 := by ring
    _ ≤ (16 * U ^ 2 * A ^ 2) * U := mul_le_mul_of_nonneg_left hqU (by positivity)
    _ = _ := by ring

/-- Replace the marginal and geometric curvature jets by bounded polynomial approximations. -/
theorem shortGap_discriminant_of_enclosures {x U U₁ U₂ A q r P₀ P₁ P₂ P_A b₀ b₁ b₂ b_A : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1) (hr : 0 ≤ r) (hr₂ : r ≤ 2) (hU : 0 < U) (hq : 0 ≤ q)
    (hb₀ : |U - P₀| ≤ b₀) (hb₁ : |U₁ - P₁| ≤ b₁)
    (hb₂ : |U₂ - P₂| ≤ b₂) (hb_A : |A - P_A| ≤ b_A)
    (hcurv : 0 ≤ 4 * U * U₁ + 2 * x * (2 * U * U₂ - U₁ ^ 2))
    (hroot : q ^ 2 ≤ P₀ - b₀)
    (hupper : (1 - x * r) * P₁ + x * P₂ + (x * r ^ 2 / 2) * P₀ + (b₁ + b₂ + 2 * b₀) <
      (P_A - b_A) * q) :
    0 < 16 * U ^ 3 * A ^ 2 - (4 * U * U₁ + 2 * x * (2 * U * U₂ - U₁ ^ 2)) ^ 2 := by
  have hxr : x * r ≤ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hx₁ hr, hr₂]
  have hrSq : x * r ^ 2 / 2 ≤ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hx₁ (sq_nonneg r)
    have h₂ := pow_le_pow_left₀ hr hr₂ 2
    nlinarith only [h₁, h₂]
  have hterm {c a v e k : ℝ} (hc : |c| ≤ k) (hk : 0 ≤ k) (he : |a - v| ≤ e) :
      c * a ≤ c * v + k * e := by
    have h : c * (a - v) ≤ k * e := calc
      _ ≤ |c * (a - v)| := le_abs_self _
      _ = |c| * |a - v| := abs_mul _ _
      _ ≤ _ := mul_le_mul hc he (abs_nonneg _) hk
    linarith only [show c * (a - v) = c * a - c * v by ring, h]
  have h₀ := hterm (c := x * r ^ 2 / 2) (k := 2)
    (by rw [abs_of_nonneg (by positivity)]; exact hrSq) (by norm_num) hb₀
  have h₁ := hterm (c := 1 - x * r) (k := 1)
    (abs_le.mpr ⟨by linarith only [hxr], by linarith only [mul_nonneg hx hr]⟩) (by norm_num) hb₁
  have h₂ := hterm (c := x) (k := 1) (by rwa [abs_of_nonneg hx]) (by norm_num) hb₂
  have hA : (P_A - b_A) * q ≤ A * q :=
    mul_le_mul_of_nonneg_right (by linarith only [(abs_le.mp hb_A).1]) hq
  apply shortGap_discriminant_of_square hx hU (hroot.trans (by linarith only [(abs_le.mp hb₀).1])) hcurv
  calc
    _ ≤ ((1 - x * r) * P₁ + 1 * b₁) + (x * P₂ + 1 * b₂) +
        ((x * r ^ 2 / 2) * P₀ + 2 * b₀) := add_le_add (add_le_add h₁ h₂) h₀
    _ = (1 - x * r) * P₁ + x * P₂ + (x * r ^ 2 / 2) * P₀ + (b₁ + b₂ + 2 * b₀) := by ring
    _ < (P_A - b_A) * q := hupper
    _ ≤ A * q := hA

/-- Lower and upper bounds for the two sides of the endpoint slope comparison. -/
theorem shortGap_endpoint_of_bounds {U U₁ T₁ L M V : ℝ}
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hLbound : L ≤ 2 * U + 2 * U₁)
    (hM : U ≤ M) (hV : |T₁| ≤ V) (hbound : 0 < L ^ 2 - 4 * M * V ^ 2) :
    0 < (2 * U + 2 * U₁) ^ 2 - 4 * U * T₁ ^ 2 := by
  have hV' : T₁ ^ 2 ≤ V ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg T₁) hV 2
  have hlower := pow_le_pow_left₀ hL hLbound 2
  have hupper := mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 4))
    hV' (sq_nonneg T₁) (mul_nonneg (by norm_num) (hU.trans hM))
  exact hbound.trans_le (sub_le_sub hlower hupper)

private theorem shortGapCurvatureBracket_nonneg {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    let U := shortGapProfileU p
    0 ≤ 4 * U t * deriv U t + t * (2 * U t * deriv (deriv U) t - (deriv U t) ^ 2) := by
  have hjets := (sqrtProfile_jets (shortGapProfileU_contDiff p) (shortGapProfileU_pos hp)).2 t
  change 4 * Real.sqrt (shortGapProfileU p t) ^ 3 * deriv (deriv (shortGapJ p)) t = _ at hjets
  have hcurv : 0 ≤ deriv (deriv (shortGapJ p)) t :=
    (div_nonneg (shortGapJ_deriv_pos hp ht).le (by norm_num)).trans
      (shortGapJ_deriv_half_le_second hp ht)
  dsimp only
  rw [← hjets]
  positivity

private theorem shortGap_q_nonneg {x y : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    0 ≤ shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y := by
  have hrow (a b c : ℚ) :
      rowEval y (polynomial [a, b, c]) = (a : ℝ) + b * y + c * y ^ 2 := by
    rw [rowEval_cons, rowEval_cons, rowEval_cons]
    simp [polynomial]
    <;> ring
  have hrows : qRows = [
      [1060364/1000000, 289300/1000000, 8719/1000000],
      [1201564/1000000, 346575/1000000, 15251/1000000],
      [882548/1000000, 320739/1000000, 26395/1000000],
      [457271/1000000, 181003/1000000, 14742/1000000],
      [374350/1000000, 251002/1000000, 50057/1000000],
      [-59873/1000000, -84643/1000000, -25991/1000000],
      [141041/1000000, 120222/1000000, 28731/1000000]] := by decide +kernel
  have hy₂ : y ^ 2 ≤ 1 := pow_le_one₀ hy hy₁
  have hA : (0 : ℝ) ≤ (59873 + 84643*y + 25991*y^2) / 1000000 := by positivity
  have hB : (59873 + 84643*y + 25991*y^2) / 1000000 ≤ (180507/1000000 : ℝ) := by
    linarith only [hy₁, hy₂]
  have hneg : (59873 + 84643*y + 25991*y^2) / 1000000 * x ^ 5 ≤ (180507/1000000 : ℝ) :=
    (mul_le_of_le_one_right hA (pow_le_one₀ hx hx₁)).trans hB
  simp only [shortGapChartEval, hrows]
  norm_num [Finset.sum_range_succ, hrow]
  have h₁ : 0 ≤ (1201564/1000000 + 346575/1000000*y + 15251/1000000*y^2) * x := by positivity
  have h₂ : 0 ≤ (882548/1000000 + 320739/1000000*y + 26395/1000000*y^2) * x^2 := by positivity
  have h₃ : 0 ≤ (457271/1000000 + 181003/1000000*y + 14742/1000000*y^2) * x^3 := by positivity
  have h₄ : 0 ≤ (374350/1000000 + 251002/1000000*y + 50057/1000000*y^2) * x^4 := by positivity
  have h₆ : 0 ≤ (141041/1000000 + 120222/1000000*y + 28731/1000000*y^2) * x^6 := by positivity
  nlinarith only [hneg, h₁, h₂, h₃, h₄, h₆, hy, sq_nonneg y]

private theorem shortGap_r_bounds {x y : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    let r := shortGapChartEval (fun k ↦ rRows.getD k []) 2 x y
    0 ≤ r ∧ r ≤ 2 := by
  have hrows : rRows = [[1124/1000, 16/1000], [442/1000, 119/1000]] := by decide +kernel
  have hrow (a b : ℚ) : rowEval y (polynomial [a, b]) = (a : ℝ) + b * y := by
    rw [rowEval_cons, rowEval_cons]
    simp [polynomial, mul_comm]
  dsimp only
  simp only [shortGapChartEval, hrows]
  norm_num [Finset.sum_range_succ, hrow]
  constructor
  · positivity
  · have hxy : x * y ≤ 1 := (mul_le_of_le_one_left hy hx₁).trans hy₁
    nlinarith only [hx₁, hy₁, hxy]

/-- On the actual composition grid the order-18 certificate proves both scalar signs. -/
theorem shortGap_profile_signs {p : ℕ} (hp : 11 ≤ p) :
    (∀ t ∈ Set.Icc (0 : ℝ) 2,
      0 < shortGapProfileD (shortGapProfileT p (3 / (p : ℝ))) (shortGapProfileU p) t) ∧
    0 < shortGapProfileH (shortGapProfileT p (3 / (p : ℝ))) (shortGapProfileU p) 2 := by
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hp₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  let y : ℝ := 11 / (p : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy₁ : y ≤ 1 := (div_le_one hpR).mpr hp₁
  constructor
  · intro t ht
    let x : ℝ := t / 2
    have hx : 0 ≤ x := div_nonneg ht.1 (by norm_num)
    have hx₁ : x ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using ht.2)
    have htx : 2 * x = t := by dsimp [x]; ring
    let P (g : Jet) := shortGapChartEval (jetRow g) 19 x y
    let b (g : Jet) := shortGapBudgetEval g x
    let q := shortGapChartEval (fun k ↦ qRows.getD k []) 7 x y
    let r := shortGapChartEval (fun k ↦ rRows.getD k []) 2 x y
    have he (g : Jet) : |chartJetValue p g x - P g| ≤ b g := shortGap_jet_enclosure hp g hx hx₁
    have hq : 0 ≤ q := shortGap_q_nonneg hx hx₁ hy hy₁
    obtain ⟨hr, hr₂⟩ : 0 ≤ r ∧ r ≤ 2 := shortGap_r_bounds hx hx₁ hy hy₁
    have hroot : q ^ 2 ≤ P .value - b .value := sub_nonneg.mp
      ((by norm_num : (0 : ℝ) ≤ ((3 / 5000 : ℚ) : ℝ)).trans
        (shortGap_sqrtComparison_lower hx hx₁ hy hy₁))
    have hupper : (1 - x * r) * P .first + x * P .second + (x * r ^ 2 / 2) * P .value +
        (b .first + b .second + 2 * b .value) < (P .corrected - b .corrected) * q := by
      rw [← sub_pos, ← sub_sub]
      exact (by norm_num : (0 : ℝ) < ((7 / 2000 : ℚ) : ℝ)).trans_le
        (shortGap_curvatureComparison_lower hx hx₁ hy hy₁)
    have hcurv := shortGapCurvatureBracket_nonneg hp₀ (t := 2 * x) (by positivity)
    have hsign := shortGap_discriminant_of_enclosures hx hx₁ hr hr₂
      (shortGapProfileU_pos hp₀ (2 * x)) hq (he .value) (he .first) (he .second) (he .corrected)
      hcurv hroot hupper
    simpa only [shortGapProfileD, chartJetValue, htx] using hsign
  · open ShortGapFinite.Revised in
    have hL := bernstein_row_lower (lower := 84) hy hy₁ endpoint_row_lengths.2.1
      (fun _ hi ↦ (endpointLBernstein_checked hi).le)
    have hV := bernstein_row_lower (lower := 10) hy hy₁ endpoint_row_lengths.2.2
      (fun _ hi ↦ (endpointVBernstein_checked hi).le)
    have hcomp := bernstein_row_lower (lower := 446) hy hy₁ endpoint_row_lengths.1
      (fun _ hi ↦ (endpointBernstein_checked hi).le)
    rw [shortGap_endpointComparison_eval] at hcomp
    have he (g : Jet) : |chartJetValue p g 1 - shortGapChartEval (jetRow g) 19 1 y| ≤
        shortGapBudgetEval g 1 := shortGap_jet_enclosure hp g (x := 1) zero_le_one le_rfl
    have h₀ := abs_le.mp (he .value)
    have h₁ := abs_le.mp (he .first)
    have hs := he .slope
    let L := rowEval y (polynomial endpointL)
    let M := rowEval y (polynomial endpointM)
    let V := rowEval y (polynomial endpointV) + shortGapBudgetEval .slope 1
    have hL₀ : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 84).trans hL
    have hLupper : L ≤ 2 * chartJetValue p .value 1 + 2 * chartJetValue p .first 1 := by
      rw [show L = _ from shortGap_endpointL_eval y]
      have hb₀ : shortGapChartEval (jetRow .value) 19 1 y - shortGapBudgetEval .value 1 ≤
          chartJetValue p .value 1 := by linarith only [h₀.1]
      have hb₁ : shortGapChartEval (jetRow .first) 19 1 y - shortGapBudgetEval .first 1 ≤
          chartJetValue p .first 1 := by linarith only [h₁.1]
      linarith only [hb₀, hb₁]
    have hM : chartJetValue p .value 1 ≤ M := by
      rw [show M = _ from shortGap_endpointM_eval y]
      linarith only [h₀.2]
    have hVupper : |chartJetValue p .slope 1| ≤ V := by
      let ps := shortGapChartEval (jetRow .slope) 19 1 y
      have hps : 0 ≤ ps := by
        rw [show ps = shortGapChartEval (jetRow .slope) 19 1 y from rfl, ← shortGap_endpointV_eval]
        exact (by norm_num : (0 : ℝ) ≤ 10).trans hV
      calc
        _ = |chartJetValue p .slope 1 - ps + ps| := by rw [sub_add_cancel]
        _ ≤ |chartJetValue p .slope 1 - ps| + |ps| := abs_add_le _ _
        _ ≤ shortGapBudgetEval .slope 1 + ps := by
          rw [abs_of_nonneg hps]
          exact add_le_add_left hs ps
        _ = V := by dsimp [V, ps]; rw [shortGap_endpointV_eval]; ring
    have hbound : 0 < L ^ 2 - 4 * M * V ^ 2 := (by norm_num : (0 : ℝ) < 446).trans_le hcomp
    have hsign := shortGap_endpoint_of_bounds (shortGapProfileU_pos hp₀ (2 * 1)).le
      hL₀ hLupper hM hVupper hbound
    simpa [shortGapProfileH, chartJetValue, mul_comm (2 : ℝ)] using hsign

end

end RefinedBMV.PositiveCenter
