/- GID: D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/LiteralRationalPrimeTranslationBound
   mirror-E: none(waiver:literal-translation-energy-shift-transfer)
   anchors: []
   utility: none
   digest: Explicit rational coefficient modulus for literal translation energy. -/

import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound

open Set MeasureTheory Polynomial
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open scoped ComplexConjugate

/-- Finite rational coefficient budget at radius `B`. -/
def coefficientBudget (B : Rat) (r : Rat[X]) : Rat :=
  ∑ i ∈ Finset.range (r.natDegree + 1), |r.coeff i| * B ^ i

noncomputable section

private theorem polynomial_value_le_budget (B : Rat)
    (r : Rat[X]) (x : Real) (hx : |x| ≤ (B : Real)) :
    |(aeval x r : Real)| ≤ (coefficientBudget B r : Real) := by
  rw [Polynomial.aeval_eq_sum_range]
  calc
    |∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i • x ^ i| ≤
        ∑ i ∈ Finset.range (r.natDegree + 1), |(r.coeff i : Real) * x ^ i| := by
      simpa [Algebra.smul_def] using
        (Finset.abs_sum_le_sum_abs
          (s := Finset.range (r.natDegree + 1))
          (f := fun i => (r.coeff i : Real) * x ^ i))
    _ ≤ ∑ i ∈ Finset.range (r.natDegree + 1),
        |(r.coeff i : Real)| * (B : Real) ^ i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hx i) (abs_nonneg _)
    _ = (coefficientBudget B r : Real) := by
      simp [coefficientBudget, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs]

private theorem glue_deriv_bound (x : Real) :
    0 ≤ deriv expNegInvGlue x ∧ deriv expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  have hderiv : deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x := by
    have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Real[X]) x).deriv
    simpa using h
  rw [hderiv]
  constructor
  · exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)
  rcases le_or_gt x 0 with hx | hx
  · rw [expNegInvGlue.zero_of_nonpos hx]
    simpa using (Real.exp_nonneg (-2))
  let z : Real := x⁻¹
  have hz : 0 ≤ z := inv_nonneg.mpr hx.le
  have hhalf : z / 2 ≤ Real.exp (z / 2 - 1) := by
    have h := Real.add_one_le_exp (z / 2 - 1)
    linarith
  have hsq : (z / 2) ^ 2 ≤ (Real.exp (z / 2 - 1)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg (Real.exp_nonneg (z / 2 - 1)) (by positivity : 0 ≤ z / 2))]
  have he : (Real.exp (z / 2 - 1)) ^ 2 = Real.exp (z - 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hsq
  have hineq : z ^ 2 ≤ 4 * Real.exp (z - 2) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hineq (Real.exp_nonneg (-z))
  have hproduct : Real.exp (z - 2) * Real.exp (-z) = Real.exp (-2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [expNegInvGlue, if_neg (not_le.mpr hx)]
  dsimp [z] at hmul hproduct
  nlinarith [hmul]

private theorem smoothTransition_deriv_bound (x : Real) :
    0 ≤ deriv Real.smoothTransition x ∧ deriv Real.smoothTransition x ≤ 9 := by
  let a := expNegInvGlue x
  let b := expNegInvGlue (1 - x)
  let da := deriv expNegInvGlue x
  let db := deriv expNegInvGlue (1 - x)
  have hdiff (y : Real) : HasDerivAt expNegInvGlue (deriv expNegInvGlue y) y := by
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Real[X]) y
    have hfun : (fun z : Real => (1 : Real[X]).eval z⁻¹ * expNegInvGlue z) =
        expNegInvGlue := by funext z; simp
    rw [hfun] at h
    exact h.differentiableAt.hasDerivAt
  have hneg : HasDerivAt (fun y : Real => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : Real)
  have hb : HasDerivAt (fun y : Real => expNegInvGlue (1 - y)) (-db) x := by
    have h := (hdiff (1 - x)).comp x hneg
    have hfun : (expNegInvGlue ∘ (fun y : Real => 1 - y)) =
        (fun y : Real => expNegInvGlue (1 - y)) := rfl
    rw [hfun] at h
    have heq : deriv expNegInvGlue (1 - x) * -1 = -db := by dsimp [db]; ring
    rw [heq] at h
    exact h
  have hdenpos : 0 < a + b := Real.smoothTransition.pos_denom x
  have hd : HasDerivAt Real.smoothTransition
      ((da * b + a * db) / (a + b) ^ 2) x := by
    have h := (hdiff x).div ((hdiff x).add hb) hdenpos.ne'
    have hfun : (expNegInvGlue / (expNegInvGlue +
        fun y : Real => expNegInvGlue (1 - y))) = Real.smoothTransition := by
      funext y
      rfl
    rw [hfun] at h
    have heq : (da * b + a * db) / (a + b) ^ 2 =
        (deriv expNegInvGlue x *
          (expNegInvGlue + fun y : Real => expNegInvGlue (1 - y)) x -
          expNegInvGlue x * (deriv expNegInvGlue x + -db)) /
          (expNegInvGlue + fun y : Real => expNegInvGlue (1 - y)) x ^ 2 := by
      dsimp [a, b, da, db]
      ring
    rw [←heq] at h
    exact h
  have hderiv : deriv Real.smoothTransition x =
      (da * b + a * db) / (a + b) ^ 2 := hd.deriv
  rw [hderiv]
  have he : 0 < Real.exp (-2) := Real.exp_pos _
  have hhalf : expNegInvGlue (1 / 2 : Real) = Real.exp (-2) := by
    norm_num [expNegInvGlue]
  have hden : Real.exp (-2) ≤ a + b := by
    rcases le_total (1 / 2 : Real) x with hx | hx
    · have hh := expNegInvGlue.monotone hx
      dsimp [a, b]
      linarith [expNegInvGlue.nonneg (1 - x)]
    · have hh := expNegInvGlue.monotone (show (1 / 2 : Real) ≤ 1 - x by linarith)
      dsimp [a, b]
      linarith [expNegInvGlue.nonneg x]
  have ha : 0 ≤ a := expNegInvGlue.nonneg x
  have hb0 : 0 ≤ b := expNegInvGlue.nonneg (1 - x)
  have hda := glue_deriv_bound x
  have hdb := glue_deriv_bound (1 - x)
  have hnum0 : 0 ≤ da * b + a * db :=
    add_nonneg (mul_nonneg hda.1 hb0) (mul_nonneg ha hdb.1)
  have hnum : da * b + a * db ≤ 4 * Real.exp (-2) * (a + b) := by
    nlinarith [mul_le_mul_of_nonneg_right hda.2 hb0,
      mul_le_mul_of_nonneg_left hdb.2 ha]
  constructor
  · exact div_nonneg hnum0 (sq_nonneg _)
  · apply (div_le_iff₀ (sq_pos_of_pos hdenpos)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hden) hdenpos.le]

private theorem smoothTransition_lipschitz (u v : Real) :
    |Real.smoothTransition u - Real.smoothTransition v| ≤ 9 * |u - v| := by
  have hdiff : Differentiable Real Real.smoothTransition := by
    intro x
    exact (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x
  have hbound (x : Real) : ‖deriv Real.smoothTransition x‖₊ ≤ (9 : NNReal) := by
    have h := smoothTransition_deriv_bound x
    rw [Real.nnnorm_of_nonneg h.1]
    exact_mod_cast h.2
  have h := (lipschitzWith_of_nnnorm_deriv_le hdiff hbound).dist_le_mul u v
  simpa [Real.dist_eq] using h

private theorem polynomial_budget_bounds (B : Rat) (hB : 0 ≤ B) (r : Rat[X]) :
    (∀ x : Real, |x| ≤ (B : Real) →
      |(aeval x r : Real)| ≤ (coefficientBudget B r : Real)) ∧
    (∀ u v : Real, |u| ≤ (B : Real) → |v| ≤ (B : Real) →
      |(aeval u r : Real) - aeval v r| ≤
        (coefficientBudget B r.derivative : Real) * |u - v|) := by
  constructor
  · exact fun x hx => polynomial_value_le_budget B r x hx
  have hnonneg : 0 ≤ (coefficientBudget B r.derivative : Real) := by
    have hh : 0 ≤ coefficientBudget B r.derivative := by
      unfold coefficientBudget
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (abs_nonneg _) (pow_nonneg hB _)
    exact_mod_cast hh
  let C : NNReal := ⟨(coefficientBudget B r.derivative : Real), hnonneg⟩
  have hderiv (y : Real) (hy : y ∈ Icc (-(B : Real)) (B : Real)) :
      ‖deriv (fun z : Real => (aeval z r : Real)) y‖₊ ≤ C := by
    have hh := polynomial_value_le_budget B r.derivative y (abs_le.mpr hy)
    have heq : deriv (fun z : Real => (aeval z r : Real)) y =
        (aeval y r.derivative : Real) := (r.hasDerivAt_aeval y).deriv
    rw [heq]
    exact_mod_cast hh
  have hl : LipschitzOnWith C (fun y : Real => (aeval y r : Real))
      (Icc (-(B : Real)) (B : Real)) :=
    (convex_Icc (-(B : Real)) (B : Real)).lipschitzOnWith_of_nnnorm_deriv_le
      (fun y _ => (r.hasDerivAt_aeval y).differentiableAt)
      hderiv
  intro u v hu hv
  have h := hl.dist_le_mul u (abs_le.mp hu) v (abs_le.mp hv)
  simp only [Real.dist_eq] at h
  change |(aeval u r : Real) - aeval v r| ≤
    (coefficientBudget B r.derivative : Real) * |u - v| at h
  exact h

private theorem evenPolynomial_budget_bounds (B : Rat) (hB : 0 ≤ B)
    (p q : Rat[X]) :
    (∀ y : Real, |y| ≤ (B : Real) →
      ‖rationalEvenPolynomial p q y‖ ≤
        (coefficientBudget B p + coefficientBudget B q : Rat)) ∧
    (∀ u v : Real, |u| ≤ (B : Real) → |v| ≤ (B : Real) →
      ‖rationalEvenPolynomial p q u - rationalEvenPolynomial p q v‖ ≤
        (coefficientBudget B p.derivative + coefficientBudget B q.derivative : Rat) *
          |u - v|) := by
  have hp := polynomial_budget_bounds B hB p
  have hq := polynomial_budget_bounds B hB q
  let avg (r : Rat[X]) (y : Real) : Real :=
    ((aeval y r : Real) + aeval (-y) r) / 2
  have havg (r : Rat[X]) (y : Real) (hy : |y| ≤ (B : Real)) :
      |avg r y| ≤ (coefficientBudget B r : Real) := by
    have hb := (polynomial_budget_bounds B hB r).1
    have hneg : |-y| ≤ (B : Real) := by simpa only [abs_neg] using hy
    have hh := abs_add_le (aeval y r : Real) (aeval (-y) r : Real)
    dsimp [avg]
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    have he := hb y hy
    have he' := hb (-y) hneg
    linarith
  have havgLip (r : Rat[X]) (u v : Real)
      (hu : |u| ≤ (B : Real)) (hv : |v| ≤ (B : Real)) :
      |avg r u - avg r v| ≤
        (coefficientBudget B r.derivative : Real) * |u - v| := by
    have hb := (polynomial_budget_bounds B hB r).2
    have hneg (y : Real) (hy : |y| ≤ (B : Real)) : |-y| ≤ (B : Real) := by
      simpa only [abs_neg] using hy
    have hflip : |(-u) - (-v)| = |u - v| := by
      rw [show (-u) - (-v) = -(u - v) by ring, abs_neg]
    have h1 := hb u v hu hv
    have h2 := hb (-u) (-v) (hneg u hu) (hneg v hv)
    rw [hflip] at h2
    have hh := abs_add_le
      ((aeval u r : Real) - aeval v r)
      ((aeval (-u) r : Real) - aeval (-v) r)
    have heq : avg r u - avg r v =
        (((aeval u r : Real) - aeval v r) +
          ((aeval (-u) r : Real) - aeval (-v) r)) / 2 := by
      dsimp [avg]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    linarith
  have hnorm (a b : Real) : ‖(a : Complex) + Complex.I * (b : Complex)‖ ≤
      |a| + |b| := by
    calc
      _ ≤ ‖(a : Complex)‖ + ‖Complex.I * (b : Complex)‖ := norm_add_le _ _
      _ = |a| + |b| := by simp
  constructor
  · intro y hy
    change ‖(avg p y : Complex) + Complex.I * (avg q y : Complex)‖ ≤ _
    exact (hnorm _ _).trans (by
      simpa only [Rat.cast_add] using
        add_le_add (havg p y hy) (havg q y hy))
  · intro u v hu hv
    have heq : rationalEvenPolynomial p q u - rationalEvenPolynomial p q v =
        ((avg p u - avg p v : Real) : Complex) +
          Complex.I * ((avg q u - avg q v : Real) : Complex) := by
      dsimp [rationalEvenPolynomial, avg]
      push_cast
      ring
    rw [heq]
    calc
      _ ≤ |avg p u - avg p v| + |avg q u - avg q v| := hnorm _ _
      _ ≤ (coefficientBudget B p.derivative : Real) * |u - v| +
          (coefficientBudget B q.derivative : Real) * |u - v| :=
        add_le_add (havgLip p u v hu hv) (havgLip q u v hu hv)
      _ = (coefficientBudget B p.derivative +
          coefficientBudget B q.derivative : Rat) * |u - v| := by push_cast; ring

private theorem literal_cutoff_bounds (R : Nat) (hR : 0 < R) (p q : Rat[X]) :
    let B : Rat := 2 * R
    let A : Rat := coefficientBudget B p + coefficientBudget B q
    let D : Rat := coefficientBudget B p.derivative + coefficientBudget B q.derivative
    let K : Rat := D + (9 / R) * A
    let H : Real → Complex := fun y =>
      ((Real.smoothTransition (2 - |y| / R) : Real) : Complex) *
        rationalEvenPolynomial p q y
    (∀ y : Real, ‖H y‖ ≤ (A : Real)) ∧
      (∀ u v : Real, ‖H u - H v‖ ≤ (K : Real) * |u - v|) := by
  dsimp only
  let B : Rat := 2 * R
  let A : Rat := coefficientBudget B p + coefficientBudget B q
  let D : Rat := coefficientBudget B p.derivative + coefficientBudget B q.derivative
  let K : Rat := D + (9 / R) * A
  let H : Real → Complex := fun y =>
    ((Real.smoothTransition (2 - |y| / R) : Real) : Complex) *
      rationalEvenPolynomial p q y
  let w : Real → Real := fun y => Real.smoothTransition (2 - |y| / R)
  let P : Real → Complex := rationalEvenPolynomial p q
  have hr : 0 < (R : Real) := by exact_mod_cast hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget (r : Rat[X]) : 0 ≤ coefficientBudget B r := by
    unfold coefficientBudget
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hB _)
  have hA : 0 ≤ A := add_nonneg (hbudget p) (hbudget q)
  have hD : 0 ≤ D := add_nonneg (hbudget p.derivative) (hbudget q.derivative)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hD (mul_nonneg (div_nonneg (by norm_num)
      (by exact_mod_cast hR.le)) hA)
  have hBr : (B : Real) = 2 * R := by norm_num [B]
  have hpoly := evenPolynomial_budget_bounds B hB p q
  have hcut (y : Real) : 0 ≤ w y ∧ w y ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hcutlip (u v : Real) : |w u - w v| ≤ (9 / R) * |u - v| := by
    have harg : |(2 - |u| / R) - (2 - |v| / R)| ≤ |u - v| / R := by
      have heq : (2 - |u| / R) - (2 - |v| / R) =
          -((|u| - |v|) / R) := by ring
      rw [heq, abs_neg, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub u v) hr.le
    have h := smoothTransition_lipschitz (2 - |u| / R) (2 - |v| / R)
    have h' := h.trans (mul_le_mul_of_nonneg_left harg (by norm_num : (0 : Real) ≤ 9))
    dsimp [w]
    calc
      _ ≤ 9 * (|u - v| / R) := h'
      _ = (9 / R) * |u - v| := by ring
  have hzero (y : Real) (hy : 2 * (R : Real) ≤ |y|) : H y = 0 := by
    have harg : 2 - |y| / R ≤ 0 := by
      rw [sub_nonpos]
      exact (le_div_iff₀ hr).2 hy
    dsimp [H]
    rw [Real.smoothTransition.zero_of_nonpos harg]
    simp
  have hamp (y : Real) : ‖H y‖ ≤ (A : Real) := by
    by_cases hy : |y| ≤ 2 * (R : Real)
    · have hpy := hpoly.1 y (by simpa only [hBr] using hy)
      change ‖(w y : Complex) * P y‖ ≤ (A : Real)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcut y).1]
      calc
        w y * ‖P y‖ ≤ 1 * (A : Real) :=
          mul_le_mul (hcut y).2 hpy (norm_nonneg _) (by norm_num)
        _ = (A : Real) := by ring
    · have hy' : 2 * (R : Real) ≤ |y| := le_of_lt (lt_of_not_ge hy)
      rw [hzero y hy']
      exact_mod_cast hA
  have hwithin (u v : Real) (hu : |u| ≤ 2 * (R : Real))
      (hv : |v| ≤ 2 * (R : Real)) :
      ‖H u - H v‖ ≤ (K : Real) * |u - v| := by
    have hPu := hpoly.1 u (by simpa only [hBr] using hu)
    have hPuv := hpoly.2 u v
      (by simpa only [hBr] using hu) (by simpa only [hBr] using hv)
    have heq : H u - H v =
        ((w u - w v : Real) : Complex) * P u +
          (w v : Complex) * (P u - P v) := by
      dsimp [H, w, P]
      push_cast
      ring
    rw [heq]
    have hvw : |w v| ≤ 1 := by rw [abs_of_nonneg (hcut v).1]; exact (hcut v).2
    have hc : (9 / (R : Real)) * |u - v| * (A : Real) +
        (D : Real) * |u - v| = (K : Real) * |u - v| := by
      dsimp [K]
      push_cast
      ring
    calc
      ‖((w u - w v : Real) : Complex) * P u +
          (w v : Complex) * (P u - P v)‖ ≤
          |w u - w v| * ‖P u‖ + |w v| * ‖P u - P v‖ := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le
          (((w u - w v : Real) : Complex) * P u)
          ((w v : Complex) * (P u - P v))
      _ ≤ (9 / (R : Real)) * |u - v| * (A : Real) +
          1 * ((D : Real) * |u - v|) := by
        apply add_le_add
        · exact mul_le_mul (hcutlip u v) hPu (norm_nonneg _)
            (mul_nonneg (by positivity) (abs_nonneg _))
        · exact mul_le_mul hvw hPuv (norm_nonneg _)
            (by norm_num)
      _ = (K : Real) * |u - v| := by rw [one_mul, ← hc]
  have hcross (u v : Real) (hu : |u| ≤ 2 * (R : Real))
      (hv : ¬ |v| ≤ 2 * (R : Real)) :
      ‖H u - H v‖ ≤ (K : Real) * |u - v| := by
    have hvlr : v < -(2 * (R : Real)) ∨ 2 * (R : Real) < v := by
      by_contra hh
      push Not at hh
      exact hv (abs_le.mpr hh)
    rcases hvlr with hl | hr'
    · have hz : H (-(2 * (R : Real))) = 0 := hzero _ (by simp [abs_neg])
      have hvz : H v = 0 := hzero _ (by rw [abs_of_neg (by linarith : v < 0)]; linarith)
      have hbound := hwithin u (-(2 * (R : Real))) hu (by simp)
      rw [hz] at hbound
      rw [hvz]
      exact hbound.trans (mul_le_mul_of_nonneg_left (by
        have hlu := (abs_le.mp hu).1
        rw [abs_of_nonneg (by linarith : 0 ≤ u - -(2 * (R : Real))),
          abs_of_nonneg (by linarith : 0 ≤ u - v)]
        linarith) (by exact_mod_cast hK))
    · have hz : H (2 * (R : Real)) = 0 := hzero _ (by simp)
      have hvz : H v = 0 := hzero _ (by rw [abs_of_pos (by linarith : 0 < v)]; linarith)
      have hbound := hwithin u (2 * (R : Real)) hu (by simp)
      rw [hz] at hbound
      rw [hvz]
      exact hbound.trans (mul_le_mul_of_nonneg_left (by
        have hru := (abs_le.mp hu).2
        rw [abs_of_nonpos (by linarith : u - 2 * (R : Real) ≤ 0),
          abs_of_nonpos (by linarith : u - v ≤ 0)]
        linarith) (by exact_mod_cast hK))
  change (∀ y : Real, ‖H y‖ ≤ (A : Real)) ∧
    ∀ u v : Real, ‖H u - H v‖ ≤ (K : Real) * |u - v|
  refine ⟨hamp, ?_⟩
  intro u v
  by_cases hu : |u| ≤ 2 * (R : Real)
  · by_cases hv : |v| ≤ 2 * (R : Real)
    · exact hwithin u v hu hv
    · exact hcross u v hu hv
  · by_cases hv : |v| ≤ 2 * (R : Real)
    · simpa only [norm_sub_rev, abs_sub_comm] using hcross v u hv hu
    · have huz : H u = 0 := hzero u (le_of_lt (lt_of_not_ge hu))
      have hvz : H v = 0 := hzero v (le_of_lt (lt_of_not_ge hv))
      rw [huz, hvz, sub_self, norm_zero]
      exact mul_nonneg (by exact_mod_cast hK) (abs_nonneg _)

private theorem translationEnergy_global_of_bounds
    (R A K : Real) (hR : 0 < R) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (f : WeilTestFunction)
    (hzero : ∀ y : Real, 2 * R < |y| → f y = 0)
    (hamp : ∀ y : Real, ‖f y‖ ≤ A)
    (hlip : ∀ u v : Real, ‖f u - f v‖ ≤ K * |u - v|)
    (s t : Real) :
    |translationEnergy f s - translationEnergy f t| ≤
      32 * R * A * K * |s - t| := by
  let m : Real := ∫ y : Real, Complex.normSq (f y)
  let c : Real → Real := fun w => ∫ y : Real, (f y * conj (f (y - w))).re
  have hnorm : Integrable (fun y : Real => Complex.normSq (f y)) :=
    (Complex.continuous_normSq.comp f.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (by simp))
  have hcorr (w : Real) : Integrable (fun y : Real => (f y * conj (f (y - w))).re) := by
    have hfc : Continuous (f : Real → Complex) := f.continuous
    exact (show Continuous (fun y : Real => (f y * conj (f (y - w))).re) by
      fun_prop).integrable_of_hasCompactSupport
        ((f.hasCompactSupport.mul_right).comp_left (by simp))
  have henergy (w : Real) : translationEnergy f w = 2 * m - 2 * c w := by
    have hshift : Integrable (fun y : Real => Complex.normSq (f (y - w))) := by
      simpa using hnorm.comp_sub_right w
    rw [translationEnergy]
    simp_rw [Complex.normSq_sub]
    calc
      (∫ y : Real, Complex.normSq (f y) + Complex.normSq (f (y - w)) -
          2 * (f y * conj (f (y - w))).re) =
          (∫ y : Real, Complex.normSq (f y)) +
          (∫ y : Real, Complex.normSq (f (y - w))) -
          2 * (∫ y : Real, (f y * conj (f (y - w))).re) := by
        calc
          _ = (∫ y : Real, Complex.normSq (f y) + Complex.normSq (f (y - w))) -
              ∫ y : Real, 2 * (f y * conj (f (y - w))).re :=
            integral_sub (hnorm.add hshift) ((hcorr w).const_mul 2)
          _ = _ := by rw [integral_add hnorm hshift, integral_const_mul]
      _ = 2 * m - 2 * c w := by
        rw [integral_sub_right_eq_self
          (fun y : Real => Complex.normSq (f y)) w]
        dsimp [m, c]
        ring
  have hpoint (y : Real) :
      |(f y * conj (f (y - s))).re - (f y * conj (f (y - t))).re| ≤
        A * K * |s - t| := by
    have hshift : ‖f (y - s) - f (y - t)‖ ≤ K * |s - t| := by
      have h := hlip (y - s) (y - t)
      have heq : (y - s) - (y - t) = t - s := by ring
      rw [heq, abs_sub_comm] at h
      exact h
    have heq : (f y * conj (f (y - s))).re - (f y * conj (f (y - t))).re =
        (f y * conj (f (y - s) - f (y - t))).re := by
      simp only [map_sub, mul_sub, Complex.sub_re]
    rw [heq]
    calc
      |(f y * conj (f (y - s) - f (y - t))).re| ≤
          ‖f y * conj (f (y - s) - f (y - t))‖ := Complex.abs_re_le_norm _
      _ = ‖f y‖ * ‖f (y - s) - f (y - t)‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ A * (K * |s - t|) :=
        mul_le_mul (hamp y) hshift (norm_nonneg _) hA
      _ = A * K * |s - t| := by ring
  let I (w : Real) : Set Real := Icc (w - 2 * R) (w + 2 * R)
  let S : Set Real := I s ∪ I t
  have hshiftout (y w : Real) (hy : y ∉ I w) : 2 * R < |y - w| := by
    dsimp [I] at hy
    simp only [mem_Icc, not_and_or] at hy
    rcases hy with hy | hy
    · have h : y < w - 2 * R := lt_of_not_ge hy
      rw [abs_of_neg (by linarith : y - w < 0)]
      linarith
    · have h : w + 2 * R < y := lt_of_not_ge hy
      rw [abs_of_pos (by linarith : 0 < y - w)]
      linarith
  have hout (y : Real) (hy : y ∉ S) :
      (f y * conj (f (y - s))).re - (f y * conj (f (y - t))).re = 0 := by
    have hs : y ∉ I s := fun h => hy (Or.inl h)
    have ht : y ∉ I t := fun h => hy (Or.inr h)
    rw [hzero (y - s) (hshiftout y s hs), hzero (y - t) (hshiftout y t ht)]
    simp
  have hlocal :
      (∫ y : Real, (f y * conj (f (y - s))).re -
        (f y * conj (f (y - t))).re) =
      ∫ y in S,
        (f y * conj (f (y - s))).re -
          (f y * conj (f (y - t))).re :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
  have hvolume (w : Real) : volume.real (I w) = 4 * R := by
    change (volume (Icc (w - 2 * R) (w + 2 * R))).toReal = 4 * R
    rw [Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith
  have hfinite (w : Real) : volume (I w) < ⊤ := isCompact_Icc.measure_lt_top
  have hSfinite : volume S < ⊤ :=
    (measure_union_le (I s) (I t)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hfinite s, hfinite t⟩)
  have hmeasure : volume.real S ≤ 8 * R := by
    calc
      volume.real S ≤ (volume (I s) + volume (I t)).toReal := by
        exact (ENNReal.toReal_le_toReal
          (ne_of_lt hSfinite)
          (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hfinite s, hfinite t⟩))).2
          (measure_union_le (I s) (I t))
      _ = volume.real (I s) + volume.real (I t) := by
        rw [ENNReal.toReal_add (ne_of_lt (hfinite s)) (ne_of_lt (hfinite t))]
        rfl
      _ = 8 * R := by rw [hvolume s, hvolume t]; ring
  have hnonneg : 0 ≤ A * K * |s - t| := by positivity
  rw [henergy s, henergy t]
  have hcorrsub : c s - c t =
      ∫ y : Real, (f y * conj (f (y - s))).re -
        (f y * conj (f (y - t))).re := by
    exact (integral_sub (hcorr s) (hcorr t)).symm
  rw [show (2 * m - 2 * c s) - (2 * m - 2 * c t) =
    -(2 * (c s - c t)) by ring, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
    hcorrsub, hlocal, ← Real.norm_eq_abs]
  calc
    2 * ‖∫ y in S,
        (f y * conj (f (y - s))).re -
          (f y * conj (f (y - t))).re‖ ≤
        2 * ((A * K * |s - t|) * volume.real S) := by
      gcongr
      exact norm_setIntegral_le_of_norm_le_const
        hSfinite
        (fun y _ => by simpa only [Real.norm_eq_abs] using hpoint y)
    _ ≤ 2 * ((A * K * |s - t|) * (8 * R)) := by
      gcongr
    _ ≤ 32 * R * A * K * |s - t| := by
      nlinarith [mul_nonneg (le_of_lt hR) hnonneg]

/-- The literal rational cutoff has a shift-independent translation-energy modulus. -/
theorem literal_rational_prime_translation_bound
    (R : Nat) (hR : 0 < R) (p q : Rat[X]) (f : WeilTestFunction)
    (hf : ∀ y : Real, f y =
      ((Real.smoothTransition (2 - |y| / R) : Real) : Complex) *
        rationalEvenPolynomial p q y)
    (s t : Real) :
    let B : Rat := 2 * R
    let A : Rat := coefficientBudget B p + coefficientBudget B q
    let D : Rat := coefficientBudget B p.derivative + coefficientBudget B q.derivative
    let K : Rat := D + (9 / R) * A
    |translationEnergy f s - translationEnergy f t| ≤
      (32 * (R : Rat) * A * K : Rat) * |s - t| := by
  dsimp only
  let B : Rat := 2 * R
  let A : Rat := coefficientBudget B p + coefficientBudget B q
  let D : Rat := coefficientBudget B p.derivative + coefficientBudget B q.derivative
  let K : Rat := D + (9 / R) * A
  let H : Real → Complex := fun y =>
    ((Real.smoothTransition (2 - |y| / R) : Real) : Complex) *
      rationalEvenPolynomial p q y
  have hr : 0 < (R : Real) := by exact_mod_cast hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget (r : Rat[X]) : 0 ≤ coefficientBudget B r := by
    unfold coefficientBudget
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hB _)
  have hA : 0 ≤ (A : Real) := by
    exact_mod_cast add_nonneg (hbudget p) (hbudget q)
  have hK : 0 ≤ (K : Real) := by
    have hAr : 0 ≤ A := add_nonneg (hbudget p) (hbudget q)
    have hDr : 0 ≤ D := add_nonneg (hbudget p.derivative) (hbudget q.derivative)
    have hKr : 0 ≤ K := by
      dsimp [K]
      exact add_nonneg hDr (mul_nonneg
        (div_nonneg (by norm_num) (by exact_mod_cast hR.le)) hAr)
    exact_mod_cast hKr
  have hb := literal_cutoff_bounds R hR p q
  change (∀ y : Real, ‖H y‖ ≤ (A : Real)) ∧
    (∀ u v : Real, ‖H u - H v‖ ≤ (K : Real) * |u - v|) at hb
  have hzero (y : Real) (hy : 2 * (R : Real) < |y|) : f y = 0 := by
    rw [hf y]
    have harg : 2 - |y| / R ≤ 0 := by
      rw [sub_nonpos]
      exact (le_div_iff₀ hr).2 hy.le
    rw [Real.smoothTransition.zero_of_nonpos harg]
    simp
  have hamp (y : Real) : ‖f y‖ ≤ (A : Real) := by
    rw [hf y]
    exact hb.1 y
  have hlip (u v : Real) : ‖f u - f v‖ ≤ (K : Real) * |u - v| := by
    rw [hf u, hf v]
    exact hb.2 u v
  have hglobal := translationEnergy_global_of_bounds
    (R : Real) (A : Real) (K : Real) hr hA hK f hzero hamp hlip s t
  have hcast : ((32 * (R : Rat) * A * K : Rat) : Real) =
      (32 * (R : Real) * (A : Real) * (K : Real) : Real) := by
    push_cast
    ring
  exact hcast.symm ▸ hglobal

#print axioms literal_rational_prime_translation_bound

end

end D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound
