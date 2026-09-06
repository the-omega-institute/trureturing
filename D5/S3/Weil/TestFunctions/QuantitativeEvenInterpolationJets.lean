/- GID: D5/S3/Weil/TestFunctions/QuantitativeEvenInterpolationJets
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/QuantitativeEvenInterpolationJets
   mirror-E: none(waiver:constructed-interpolation-seminorm-budget)
   anchors: []
   digest: Construct actual even interpolants with explicit L1 and second-derivative budgets from finite node radius, squared-node separation and target amplitude. -/

import D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
import D5.S3.Weil.TestFunctions.FiniteBoxWeilMollifier
import D5.S3.Weil.TestFunctions.GautschiEvenInterpolationBounds
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Finite arithmetic budgets for actual interpolation jets

Gautschi's product bound controls the existing Lagrange polynomial on a disk.
Mathlib's polynomial Fourier-coefficient identity then bounds every coefficient.
Finite box smoothing supplies all derivative norms needed by the existing
polynomial differential realization. No unknown bump derivative is an input.

For d nodes, radius R, squared-node gap sigma>0 and target bound V>=0, set
  q = 2d+2, h = 1/(4(R+1)), A = 8(2d+3)(R+1),
  M = 2d V ((1+R^2)/sigma)^(d-1).
An actual interpolant has support in [-h,h] and
  ||D^s g||_1 <= (d+1) M A^(2d+s),  s=0,1,2.
These deliberately coarse constants expose conditioning and are rational
when R, sigma and V are rational. There is no bound uniform as sigma tends to 0.

Sources: W. Gautschi, Numerische Mathematik 4 (1962), 117-123, (2.1),
Theorem 1 (3.1); M. Vergne, Annals of Mathematics 174 (2011), 607-618,
Section 1, derivative/difference identity for box splines. The integration
of those elementary facts with this repository's Weil realization is
repo-derived. No novelty claim for Lagrange interpolation or box smoothing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets

noncomputable section

open Set MeasureTheory Polynomial Function AddCircle
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.FiniteBoxWeilMollifier
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.TestFunctions.GautschiEvenInterpolationBounds
open scoped BigOperators ContDiff

/-- Coarse finite inverse-interpolation coefficient budget. -/
def interpolationCoefficientBudget (d : ℕ) (R sigma V : ℝ) : ℝ :=
  2 * (d : ℝ) * V * ((1 + R ^ 2) / sigma) ^ (d - 1)

/-- Derivative cost per order of the constructed finite-box seed. -/
def interpolationJetScale (d : ℕ) (R : ℝ) : ℝ :=
  8 * (2 * (d : ℝ) + 3) * (R + 1)

/-- An explicit budget for the s-th L1 derivative of the actual interpolant. -/
def interpolationJetBudget (d : ℕ) (R sigma V : ℝ) (s : ℕ) : ℝ :=
  ((d : ℝ) + 1) * interpolationCoefficientBudget d R sigma V *
    interpolationJetScale d R ^ (2 * d + s)

/-- A polynomial coefficient is bounded by its norm on the unit disk.
Reuse the library Fourier-coefficient identity rather than a new Cauchy theory. -/
theorem polynomial_coeff_norm_le_of_unit_disk
    (P : ℂ[X]) (M : ℝ) (hP : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖P.eval z‖ ≤ M) (k : ℕ) :
    ‖P.coeff k‖ ≤ M := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [← Polynomial.fourierCoeff_toAddCircle_natCast P k]
  unfold fourierCoeff
  calc
    _ ≤ ∫ t : AddCircle (2 * Real.pi),
        ‖fourier (-(k : ℤ)) t • P.toAddCircle t‖ ∂haarAddCircle :=
      norm_integral_le_integral_norm _
    _ = ∫ t : AddCircle (2 * Real.pi), ‖P.toAddCircle t‖ ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul]
      have hf : ‖fourier (-(k : ℤ)) t‖ = 1 := Circle.norm_coe _
      rw [hf, one_mul]
    _ ≤ ∫ _t : AddCircle (2 * Real.pi), M ∂haarAddCircle := by
      apply integral_mono (Polynomial.toAddCircle.integrable P).norm integrable_const
      intro t
      simpa [Polynomial.toAddCircle] using hP (t.toCircle : ℂ) (by simp)
    _ = M := by simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gautschi's actual Lagrange disk bound gives an arithmetic coefficient bound.
Only finite nodal enclosures, separation and a seed denominator floor enter. -/
theorem lagrange_coeff_le_explicit_budget
    (z values seed : ι → ℂ) (R sigma V : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (hV : 0 ≤ V)
    (hz : ∀ i, ‖z i‖ ≤ R) (hv : ∀ i, ‖values i‖ ≤ V)
    (hseed : ∀ i, (1 / 2 : ℝ) ≤ ‖seed i‖)
    (hgap : ∀ i j, i ≠ j → sigma ≤ ‖z i ^ 2 - z j ^ 2‖) (k : ℕ) :
    ‖(Lagrange.interpolate Finset.univ (fun i => z i ^ 2)
      (fun i => values i / seed i)).coeff k‖ ≤
      interpolationCoefficientBudget (Fintype.card ι) R sigma V := by
  apply polynomial_coeff_norm_le_of_unit_disk
  intro u hu
  obtain ⟨w, hwSq⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < (2 : ℕ))
  have hw2 : ‖w‖ ^ 2 = ‖u‖ := by
    rw [← norm_pow, hwSq]
  have hw : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
  have h := lagrange_squared_interpolate_norm_le
    Finset.univ z values seed (fun _ => R) (fun _ _ => sigma) 1 (1 / 2)
    (by norm_num) w hw (fun i _ => hz i) (fun i _ => hseed i)
    (fun _ _ _ _ => hsigma)
    (fun i _ j hj => hgap i j (Finset.mem_erase.mp hj).1.symm)
  have hbudget (i : ι) :
      squaredNodeBudget Finset.univ (fun _ : ι => R) (fun _ _ => sigma) 1 i =
        ((1 + R ^ 2) / sigma) ^ (Fintype.card ι - 1) := by
    simp [squaredNodeBudget]
  have hsum :
      (∑ i : ι, (‖values i‖ / (1 / 2 : ℝ)) *
        squaredNodeBudget Finset.univ (fun _ : ι => R) (fun _ _ => sigma) 1 i) ≤
      interpolationCoefficientBudget (Fintype.card ι) R sigma V := by
    simp_rw [hbudget]
    calc
      _ ≤ ∑ _i : ι, (2 * V) *
          ((1 + R ^ 2) / sigma) ^ (Fintype.card ι - 1) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hi := hv i
        norm_num at ⊢
        nlinarith
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          interpolationCoefficientBudget]
        ring
  have hfinal := h.trans hsum
  simpa only [hwSq] using hfinal

private theorem iterate_compact (psi : WeilTestFunction) (n : ℕ) :
    HasCompactSupport ((deriv^[n]) (psi : ℝ → ℂ)) := by
  induction n with
  | zero => exact psi.hasCompactSupport
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

private theorem iterate_integrable (psi : WeilTestFunction) (n : ℕ) :
    Integrable ((deriv^[n]) (psi : ℝ → ℂ)) :=
  (ContDiff.iterate_deriv n psi.contDiff).continuous.integrable_of_hasCompactSupport
    (iterate_compact psi n)

/-- Differentiate the existing polynomial realization, retaining every term. -/
theorem evenPolynomialDifferential_iterate_deriv
    (P : ℂ[X]) (psi : WeilTestFunction) (s : ℕ) (x : ℝ) :
    ((deriv^[s]) (evenPolynomialDifferential P psi : ℝ → ℂ)) x =
      ∑ k ∈ P.support, P.coeff k * (-Complex.I) ^ (2 * k) *
        ((deriv^[2 * k + s]) (psi : ℝ → ℂ)) x := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
      rw [Function.iterate_succ_apply']
      have heq : (deriv^[s]) (evenPolynomialDifferential P psi : ℝ → ℂ) =
          fun y => ∑ k ∈ P.support, P.coeff k * (-Complex.I) ^ (2 * k) *
            ((deriv^[2 * k + s]) (psi : ℝ → ℂ)) y := funext ih
      rw [heq]
      apply HasDerivAt.deriv
      apply HasDerivAt.fun_sum
      intro k _
      have hd := ((ContDiff.iterate_deriv (2 * k + s) psi.contDiff)
        .differentiable (by simp) x).hasDerivAt.const_mul
          (P.coeff k * (-Complex.I) ^ (2 * k))
      simpa only [Function.iterate_succ_apply', Nat.add_assoc] using hd

/-- Actual L1 seminorm of the existing differential test is controlled by
its polynomial coefficients and the finite list of seed derivatives it uses. -/
theorem evenPolynomialDifferential_L1_le
    (P : ℂ[X]) (psi : WeilTestFunction) (s : ℕ) :
    (∫ x : ℝ, ‖((deriv^[s]) (evenPolynomialDifferential P psi : ℝ → ℂ)) x‖) ≤
      ∑ k ∈ P.support, ‖P.coeff k‖ *
        (∫ x : ℝ, ‖((deriv^[2 * k + s]) (psi : ℝ → ℂ)) x‖) := by
  let term : ℕ → ℝ → ℂ := fun k x =>
    P.coeff k * (-Complex.I) ^ (2 * k) *
      ((deriv^[2 * k + s]) (psi : ℝ → ℂ)) x
  have ht (k : ℕ) : Integrable (term k) :=
    (iterate_integrable psi (2 * k + s)).const_mul _
  have hsum : Integrable (fun x : ℝ => ∑ k ∈ P.support, ‖term k x‖) := by
    simpa only [Finset.sum_apply] using
      integrable_finsetSum' P.support (fun k _ => (ht k).norm)
  calc
    _ ≤ ∫ x : ℝ, ∑ k ∈ P.support, ‖term k x‖ := by
      apply integral_mono (iterate_integrable (evenPolynomialDifferential P psi) s).norm hsum
      intro x
      rw [evenPolynomialDifferential_iterate_deriv]
      exact norm_sum_le _ _
    _ = _ := by
      rw [integral_finsetSum _ (fun k _ => (ht k).norm)]
      apply Finset.sum_congr rfl
      intro k _
      simp only [term, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one]
      rw [integral_const_mul]

private theorem differential_L1_of_finite_bounds
    (P : ℂ[X]) (psi : WeilTestFunction) (d s : ℕ) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hdegree : ∀ k ∈ P.support, k ≤ d)
    (hcoeff : ∀ k, ‖P.coeff k‖ ≤ M)
    (hjet : ∀ n : ℕ, n ≤ 2 * d + s →
      (∫ x : ℝ, ‖((deriv^[n]) (psi : ℝ → ℂ)) x‖) ≤ A ^ n) :
    (∫ x : ℝ, ‖((deriv^[s]) (evenPolynomialDifferential P psi : ℝ → ℂ)) x‖) ≤
      ((d : ℝ) + 1) * M * A ^ (2 * d + s) := by
  have hs : P.support ⊆ Finset.range (d + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdegree k hk))
  have hcard : (P.support.card : ℝ) ≤ (d : ℝ) + 1 := by
    exact_mod_cast (show P.support.card ≤ d + 1 by
      simpa only [Finset.card_range] using Finset.card_le_card hs)
  calc
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ *
        (∫ x : ℝ, ‖((deriv^[2 * k + s]) (psi : ℝ → ℂ)) x‖) :=
      evenPolynomialDifferential_L1_le P psi s
    _ ≤ ∑ _k ∈ P.support, M * A ^ (2 * d + s) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkd := hdegree k hk
      have hj := (hjet (2 * k + s) (by omega)).trans
        (pow_le_pow_right₀ hA (by omega : 2 * k + s ≤ 2 * d + s))
      exact mul_le_mul (hcoeff k) hj
        (integral_nonneg fun x => norm_nonneg _) hM
    _ = (P.support.card : ℝ) * (M * A ^ (2 * d + s)) := by simp
    _ ≤ ((d : ℝ) + 1) * (M * A ^ (2 * d + s)) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hM (pow_nonneg (by linarith) _))
    _ = _ := by ring

/-- Construct an actual interpolant with specified support and explicit
zeroth, first and second derivative budgets. No jet certificate is assumed. -/
theorem exists_even_interpolant_with_explicit_jets
    (z values : ι → ℂ) (R sigma V : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (hV : 0 ≤ V)
    (hz : ∀ i, ‖z i‖ ≤ R) (hv : ∀ i, ‖values i‖ ≤ V)
    (hgap : ∀ i j, i ≠ j → sigma ≤ ‖z i ^ 2 - z j ^ 2‖) :
    ∃ g : WeilTestFunction,
      (∀ i, fourierLaplace g (z i) = values i) ∧
      tsupport (g : ℝ → ℂ) ⊆
        Icc (-(quantitativeSeedRadius R)) (quantitativeSeedRadius R) ∧
      ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (g : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (Fintype.card ι) R sigma V s := by
  let d := Fintype.card ι
  let q := 2 * d + 2
  let h := quantitativeSeedRadius R
  have hh : 0 < h := quantitativeSeedRadius_pos R hR
  let psi := finiteBoxSeed h hh q
  let P : ℂ[X] := Lagrange.interpolate Finset.univ (fun i => z i ^ 2)
    (fun i => values i / fourierLaplace psi (z i))
  have hfloor (i : ι) : (1 / 2 : ℝ) ≤ ‖fourierLaplace psi (z i)‖ :=
    finiteBoxSeed_transform_lower R hR q (z i) (hz i)
  have hne (i : ι) : fourierLaplace psi (z i) ≠ 0 := by
    intro heq
    have hi := hfloor i
    rw [heq, norm_zero] at hi
    norm_num at hi
  have hinj : Function.Injective (fun i => z i ^ 2) := by
    intro i j hij
    by_contra hnot
    have hi := hgap i j hnot
    rw [hij, sub_self, norm_zero] at hi
    exact (not_le_of_gt hsigma) hi
  have hdegree : ∀ k ∈ P.support, k ≤ d := by
    intro k hk
    have hdeg : P.degree < (d : WithBot ℕ) := by
      simpa only [P, d, Finset.card_univ] using
        Lagrange.degree_interpolate_lt
          (fun i => values i / fourierLaplace psi (z i)) hinj.injOn
    have hkdeg := Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    have hkd : (k : WithBot ℕ) < (d : WithBot ℕ) := lt_of_le_of_lt hkdeg hdeg
    have hkNat : k < d := by exact_mod_cast hkd
    exact hkNat.le
  have hcoeff (k : ℕ) : ‖P.coeff k‖ ≤ interpolationCoefficientBudget d R sigma V :=
    lagrange_coeff_le_explicit_budget z values (fun i => fourierLaplace psi (z i))
      R sigma V hR hsigma hV hz hv hfloor hgap k
  obtain ⟨hsupport, _, _, hjets⟩ := finiteBoxSeed_budget h hh q
  have hscale : 2 * ((q : ℝ) + 1) / h = interpolationJetScale d R := by
    dsimp [q, h, quantitativeSeedRadius, interpolationJetScale]
    push_cast
    field_simp [show R + 1 ≠ 0 by positivity]
    <;> ring
  have hA : 1 ≤ interpolationJetScale d R := by
    unfold interpolationJetScale
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hcross := mul_nonneg hd hR
    nlinarith
  have hM : 0 ≤ interpolationCoefficientBudget d R sigma V := by
    unfold interpolationCoefficientBudget
    positivity
  refine ⟨evenPolynomialDifferential P psi, ?_,
    (evenPolynomialDifferential_tsupport P psi).trans hsupport, ?_⟩
  · intro i
    have hPi : P.eval (z i ^ 2) = values i / fourierLaplace psi (z i) :=
      Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)
    rw [fourierLaplace_evenPolynomialDifferential, hPi]
    exact div_mul_cancel₀ _ (hne i)
  · intro s hs
    apply differential_L1_of_finite_bounds P psi d s
      (interpolationCoefficientBudget d R sigma V) (interpolationJetScale d R)
      hM hA hdegree hcoeff
    intro n hn
    have hnq : n ≤ q := by dsimp [q]; omega
    have hj := hjets n hnq
    rw [hscale] at hj
    exact hj

end

/-- Executable rational arithmetic for the same interpolant budget. Its
semantic theorem requires R,V>=0 and a strictly positive certified gap. -/
def rationalInterpolationJetBudget (d : ℕ) (R sigma V : ℚ) (s : ℕ) : ℚ :=
  ((d : ℚ) + 1) *
    (2 * (d : ℚ) * V * ((1 + R ^ 2) / sigma) ^ (d - 1)) *
    (8 * (2 * (d : ℚ) + 3) * (R + 1)) ^ (2 * d + s)

/-- The executable rational budget has exactly the proved real semantics. -/
theorem rationalInterpolationJetBudget_cast
    (d : ℕ) (R sigma V : ℚ) (s : ℕ) :
    (rationalInterpolationJetBudget d R sigma V s : ℝ) =
      interpolationJetBudget d R sigma V s := by
  unfold rationalInterpolationJetBudget interpolationJetBudget
    interpolationCoefficientBudget interpolationJetScale
  push_cast
  rfl

#print axioms polynomial_coeff_norm_le_of_unit_disk
#print axioms lagrange_coeff_le_explicit_budget
#print axioms evenPolynomialDifferential_L1_le
#print axioms exists_even_interpolant_with_explicit_jets
#print axioms rationalInterpolationJetBudget_cast

end D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets
