/- GID: D5/S3/Weil/TestFunctions/SparseEvenInterpolationJets
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/SparseEvenInterpolationJets
   mirror-E: none(waiver:finite-target-exception-interpolation)
   anchors: []
   digest: Construct actual even interpolants with explicit finite jet budgets using only target-target and target-exception separation, allowing repeated exceptional nodes. -/

import D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Sparse even interpolation with explicit derivative costs

Nonzero data are interpolated only on the target nodes. A separate polynomial
annihilator enforces every exceptional zero value, including repeated nodes.
Only target-target and target-exception gaps enter the denominator budget.
The derivative order includes the annihilator degree. Finite box smoothing
supplies those derivatives without an unknown seed seminorm hypothesis.

References: Gautschi (1962), Section 2, equation (2.1), and Section 3,
Theorem 1, equation (3.1), for the Lagrange product bound; Vergne (2011),
Section 1, for the box-spline derivative/finite-difference identity. The
actual analytic and polynomial APIs used here are the existing repository
owners. No new result about the locations of zeta zeros is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.TestFunctions.SparseEvenInterpolationJets

noncomputable section

open Set MeasureTheory Polynomial Function
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.FiniteBoxWeilMollifier
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.TestFunctions.GautschiEvenInterpolationBounds
open D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets
open scoped BigOperators ContDiff

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Indexed exceptional factors. Repetition of w is permitted. -/
def squaredExceptionPolynomial (w : κ → ℂ) : ℂ[X] :=
  ∏ n, (X - C (w n ^ 2))

/-- The target solve is normalized by the exception polynomial and seed. -/
def sparseEvenPolynomial (z values seed : ι → ℂ) (w : κ → ℂ) : ℂ[X] :=
  squaredExceptionPolynomial w *
    Lagrange.interpolate Finset.univ (fun i => z i ^ 2)
      (fun i => (values i / (squaredExceptionPolynomial w).eval (z i ^ 2)) / seed i)

/-- Arithmetic coefficient bound, separated into target and exceptional costs. -/
def sparseCoefficientBudget (d e : ℕ) (R Y sigma tau V : ℝ) : ℝ :=
  (1 + Y ^ 2) ^ e * interpolationCoefficientBudget d R sigma (V / tau ^ e)

/-- All derivatives through order two have a finite explicit budget. -/
def sparseJetBudget (d e : ℕ) (R Y sigma tau V : ℝ) (s : ℕ) : ℝ :=
  ((d + e : ℕ) + 1 : ℝ) * sparseCoefficientBudget d e R Y sigma tau V *
    interpolationJetScale (d + e) R ^ (2 * (d + e) + s)

/-- Every indexed exception is an exact root, including repeated values. -/
theorem squaredExceptionPolynomial_zero (w : κ → ℂ) (n : κ) :
    (squaredExceptionPolynomial w).eval (w n ^ 2) = 0 := by
  classical
  rw [squaredExceptionPolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ n)
  simp

/-- The product denominator needs only target-to-exception separation. -/
theorem squaredExceptionPolynomial_lower (w : κ → ℂ) (u : ℂ) (tau : ℝ)
    (htau : 0 < tau) (hgap : ∀ n, tau ≤ ‖u - w n ^ 2‖) :
    tau ^ Fintype.card κ ≤ ‖(squaredExceptionPolynomial w).eval u‖ := by
  classical
  simp only [squaredExceptionPolynomial, eval_prod, eval_sub, eval_X, eval_C, norm_prod]
  calc
    _ = ∏ _n : κ, tau := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => htau.le) (fun n _ => hgap n)

/-- The annihilator norm on the unit disk costs only its radius and degree. -/
theorem squaredExceptionPolynomial_unit_disk (w : κ → ℂ) (Y : ℝ)
    (hY : 0 ≤ Y) (hw : ∀ n, ‖w n‖ ≤ Y) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖(squaredExceptionPolynomial w).eval u‖ ≤ (1 + Y ^ 2) ^ Fintype.card κ := by
  classical
  simp only [squaredExceptionPolynomial, eval_prod, eval_sub, eval_X, eval_C, norm_prod]
  calc
    _ ≤ ∏ _n : κ, (1 + Y ^ 2) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro n _
      have hn : ‖w n‖ ^ 2 ≤ Y ^ 2 := by nlinarith [hw n, norm_nonneg (w n)]
      exact (norm_sub_le u (w n ^ 2)).trans
        (by rw [norm_pow]; exact add_le_add hu hn)
    _ = _ := by simp

/-- Actual target interpolation after multiplication by the annihilator. -/
theorem sparseEvenPolynomial_target_value
    (z values seed : ι → ℂ) (w : κ → ℂ)
    (hinj : Function.Injective (fun i => z i ^ 2)) (i : ι)
    (hseed : seed i ≠ 0)
    (hA : (squaredExceptionPolynomial w).eval (z i ^ 2) ≠ 0) :
    (sparseEvenPolynomial z values seed w).eval (z i ^ 2) * seed i = values i := by
  rw [sparseEvenPolynomial, eval_mul,
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)]
  field_simp [hseed, hA]
  <;> ring

/-- The target solve preserves every root of the exception polynomial. -/
theorem sparseEvenPolynomial_exception_value
    (z values seed : ι → ℂ) (w : κ → ℂ) (n : κ) :
    (sparseEvenPolynomial z values seed w).eval (w n ^ 2) = 0 := by
  rw [sparseEvenPolynomial, eval_mul, squaredExceptionPolynomial_zero, zero_mul]

/-- The finite coefficient budget includes no exceptional-to-exceptional gap. -/
theorem sparseEvenPolynomial_coeff_bound
    (z values seed : ι → ℂ) (w : κ → ℂ) (R Y sigma tau V : ℝ)
    (hR : 0 ≤ R) (hY : 0 ≤ Y) (hsigma : 0 < sigma) (htau : 0 < tau) (hV : 0 ≤ V)
    (hz : ∀ i, ‖z i‖ ≤ R) (hw : ∀ n, ‖w n‖ ≤ Y)
    (hv : ∀ i, ‖values i‖ ≤ V) (hseed : ∀ i, (1 / 2 : ℝ) ≤ ‖seed i‖)
    (hgap : ∀ i j, i ≠ j → sigma ≤ ‖z i ^ 2 - z j ^ 2‖)
    (hcross : ∀ i n, tau ≤ ‖z i ^ 2 - w n ^ 2‖) (k : ℕ) :
    ‖(sparseEvenPolynomial z values seed w).coeff k‖ ≤
      sparseCoefficientBudget (Fintype.card ι) (Fintype.card κ) R Y sigma tau V := by
  classical
  let v : ι → ℂ := fun i => values i / (squaredExceptionPolynomial w).eval (z i ^ 2)
  have hV' : 0 ≤ V / tau ^ Fintype.card κ := by positivity
  have hv' (i : ι) : ‖v i‖ ≤ V / tau ^ Fintype.card κ := by
    dsimp [v]
    rw [norm_div]
    exact (div_le_div_of_nonneg_right (hv i) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hV (pow_pos htau _)
        (squaredExceptionPolynomial_lower w (z i ^ 2) tau htau (hcross i)))
  apply polynomial_coeff_norm_le_of_unit_disk
  intro u hu
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < (2 : ℕ))
  have hxn : ‖x‖ ≤ 1 := by
    have heq : ‖x‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hx]
    nlinarith [norm_nonneg x]
  have hq := lagrange_squared_interpolate_norm_le Finset.univ z v seed
    (fun _ => R) (fun _ _ => sigma) 1 (1 / 2) (by norm_num) x hxn
    (fun i _ => hz i) (fun i _ => hseed i)
    (fun _ _ _ _ => hsigma)
    (fun i _ j hj => hgap i j (Finset.mem_erase.mp hj).1.symm)
  have hbudget (i : ι) :
      squaredNodeBudget Finset.univ (fun _ : ι => R) (fun _ _ => sigma) 1 i =
        ((1 + R ^ 2) / sigma) ^ (Fintype.card ι - 1) := by
    simp [squaredNodeBudget]
  have hsum :
      (∑ i : ι, (‖v i‖ / (1 / 2 : ℝ)) *
        squaredNodeBudget Finset.univ (fun _ : ι => R) (fun _ _ => sigma) 1 i) ≤
      interpolationCoefficientBudget (Fintype.card ι) R sigma (V / tau ^ Fintype.card κ) := by
    simp_rw [hbudget]
    calc
      _ ≤ ∑ _i : ι, (2 * (V / tau ^ Fintype.card κ)) *
          ((1 + R ^ 2) / sigma) ^ (Fintype.card ι - 1) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hi := hv' i
        norm_num at ⊢
        nlinarith
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          interpolationCoefficientBudget]
        ring
  have hq' := hq.trans hsum
  rw [hx] at hq'
  rw [sparseEvenPolynomial, eval_mul, norm_mul]
  exact mul_le_mul (squaredExceptionPolynomial_unit_disk w Y hY hw u hu) hq'
    (norm_nonneg _) (by positivity)

/-- Sparse polynomial degree is bounded by target count plus exception count. -/
theorem sparseEvenPolynomial_natDegree_le
    (z values seed : ι → ℂ) (w : κ → ℂ)
    (hinj : Function.Injective (fun i => z i ^ 2)) :
    (sparseEvenPolynomial z values seed w).natDegree ≤ Fintype.card ι + Fintype.card κ := by
  classical
  have hA : (squaredExceptionPolynomial w).natDegree ≤ Fintype.card κ := by
    simpa [squaredExceptionPolynomial] using
      Polynomial.natDegree_prod_le Finset.univ (fun n : κ => X - C (w n ^ 2))
  have hQ := Lagrange.degree_interpolate_lt (s := Finset.univ)
    (fun i => (values i / (squaredExceptionPolynomial w).eval (z i ^ 2)) / seed i)
    hinj.injOn
  have hQ' : (Lagrange.interpolate Finset.univ (fun i => z i ^ 2)
      (fun i => (values i / (squaredExceptionPolynomial w).eval (z i ^ 2)) / seed i)).natDegree ≤
      Fintype.card ι := by
    apply Polynomial.natDegree_le_of_degree_le
    simpa only [Finset.card_univ] using hQ.le
  exact (Polynomial.natDegree_mul_le _ _).trans (by omega)

/-- Construct an actual Weil test with all target values, every exceptional
zero, fixed target-controlled support, and explicit zeroth through second jets.
There is no separation hypothesis between two exceptional nodes. -/
theorem exists_sparse_even_interpolant_with_explicit_jets
    (z values : ι → ℂ) (w : κ → ℂ) (R Y sigma tau V : ℝ)
    (hR : 0 ≤ R) (hY : 0 ≤ Y) (hsigma : 0 < sigma) (htau : 0 < tau) (hV : 0 ≤ V)
    (hz : ∀ i, ‖z i‖ ≤ R) (hw : ∀ n, ‖w n‖ ≤ Y) (hv : ∀ i, ‖values i‖ ≤ V)
    (hgap : ∀ i j, i ≠ j → sigma ≤ ‖z i ^ 2 - z j ^ 2‖)
    (hcross : ∀ i n, tau ≤ ‖z i ^ 2 - w n ^ 2‖) :
    ∃ g : WeilTestFunction,
      (∀ i, fourierLaplace g (z i) = values i) ∧
      (∀ n, fourierLaplace g (w n) = 0) ∧
      tsupport (g : ℝ → ℂ) ⊆
        Icc (-quantitativeSeedRadius R) (quantitativeSeedRadius R) ∧
      ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (g : ℝ → ℂ)) x‖) ≤
          sparseJetBudget (Fintype.card ι) (Fintype.card κ) R Y sigma tau V s := by
  classical
  let d := Fintype.card ι
  let e := Fintype.card κ
  let m := d + e
  let q := 2 * m + 2
  let h := quantitativeSeedRadius R
  have hh : 0 < h := quantitativeSeedRadius_pos R hR
  let psi := finiteBoxSeed h hh q
  let seed : ι → ℂ := fun i => fourierLaplace psi (z i)
  let P := sparseEvenPolynomial z values seed w
  let M := sparseCoefficientBudget d e R Y sigma tau V
  let A := interpolationJetScale m R
  have hM : 0 ≤ M := by dsimp [M, sparseCoefficientBudget, interpolationCoefficientBudget]; positivity
  have hA : 1 ≤ A := by
    dsimp [A, interpolationJetScale]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg hm hR]
  have hfloor (i : ι) : (1 / 2 : ℝ) ≤ ‖seed i‖ :=
    finiteBoxSeed_transform_lower R hR q (z i) (hz i)
  have hinj : Function.Injective (fun i => z i ^ 2) := by
    intro i j hij
    by_contra hne
    have hg := hgap i j hne
    rw [hij, sub_self, norm_zero] at hg
    exact (not_le_of_gt hsigma) hg
  have hcoeff (k : ℕ) : ‖P.coeff k‖ ≤ M :=
    sparseEvenPolynomial_coeff_bound z values seed w R Y sigma tau V
      hR hY hsigma htau hV hz hw hv hfloor hgap hcross k
  have hdeg : P.natDegree ≤ m := sparseEvenPolynomial_natDegree_le z values seed w hinj
  obtain ⟨hsupport, _, _, hjets⟩ := finiteBoxSeed_budget h hh q
  have hscale : 2 * ((q : ℝ) + 1) / h = A := by
    dsimp [q, h, A, quantitativeSeedRadius, interpolationJetScale]
    push_cast
    field_simp [show R + 1 ≠ 0 by positivity]
    <;> ring
  refine ⟨evenPolynomialDifferential P psi, ?_, ?_,
    (evenPolynomialDifferential_tsupport P psi).trans hsupport, ?_⟩
  · intro i
    have hn : seed i ≠ 0 := by
      intro heq
      have hf := hfloor i
      rw [heq, norm_zero] at hf
      norm_num at hf
    have hAn : (squaredExceptionPolynomial w).eval (z i ^ 2) ≠ 0 := by
      intro heq
      have hl := squaredExceptionPolynomial_lower w (z i ^ 2) tau htau (hcross i)
      rw [heq, norm_zero] at hl
      exact (not_le_of_gt (pow_pos htau _)) hl
    rw [fourierLaplace_evenPolynomialDifferential]
    exact sparseEvenPolynomial_target_value z values seed w hinj i hn hAn
  · intro n
    rw [fourierLaplace_evenPolynomialDifferential]
    change (sparseEvenPolynomial z values seed w).eval (w n ^ 2) * _ = 0
    rw [sparseEvenPolynomial_exception_value, zero_mul]
  · intro s hs
    have hsupport' : P.support ⊆ Finset.range (m + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)).trans hdeg))
    have hcard : (P.support.card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast (show P.support.card ≤ m + 1 by
        simpa only [Finset.card_range] using Finset.card_le_card hsupport')
    calc
      _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ *
          (∫ x : ℝ, ‖((deriv^[2 * k + s]) (psi : ℝ → ℂ)) x‖) :=
        evenPolynomialDifferential_L1_le P psi s
      _ ≤ ∑ _k ∈ P.support, M * A ^ (2 * m + s) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkm := (Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hk)).trans hdeg
        have hnq : 2 * k + s ≤ q := by dsimp [q]; omega
        have hj := hjets (2 * k + s) hnq
        rw [hscale] at hj
        have hj' := hj.trans (pow_le_pow_right₀ hA (by omega : 2 * k + s ≤ 2 * m + s))
        exact mul_le_mul (hcoeff k) hj'
          (integral_nonneg fun x => norm_nonneg _) hM
      _ = (P.support.card : ℝ) * (M * A ^ (2 * m + s)) := by simp
      _ ≤ ((m : ℝ) + 1) * (M * A ^ (2 * m + s)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hM (pow_nonneg (by linarith) _))
      _ = _ := by dsimp [sparseJetBudget, d, e, m, M, A]; push_cast; ring

end

open D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets

/-- Executable rational budget for the constructed sparse interpolant. -/
def rationalSparseJetBudget (d e : ℕ) (R Y sigma tau V : ℚ) (s : ℕ) : ℚ :=
  ((d + e : ℕ) + 1 : ℚ) *
    ((1 + Y ^ 2) ^ e *
      (2 * (d : ℚ) * (V / tau ^ e) * ((1 + R ^ 2) / sigma) ^ (d - 1))) *
    (8 * (2 * ((d + e : ℕ) : ℚ) + 3) * (R + 1)) ^ (2 * (d + e) + s)

/-- The rational arithmetic has the real semantics used in the proof. -/
theorem rationalSparseJetBudget_cast (d e : ℕ) (R Y sigma tau V : ℚ) (s : ℕ) :
    (rationalSparseJetBudget d e R Y sigma tau V s : ℝ) =
      sparseJetBudget d e R Y sigma tau V s := by
  unfold rationalSparseJetBudget sparseJetBudget sparseCoefficientBudget
    interpolationCoefficientBudget interpolationJetScale
  push_cast
  rfl

#print axioms sparseEvenPolynomial_coeff_bound
#print axioms sparseEvenPolynomial_natDegree_le
#print axioms exists_sparse_even_interpolant_with_explicit_jets
#print axioms rationalSparseJetBudget_cast

end D5.S3.Weil.TestFunctions.SparseEvenInterpolationJets
