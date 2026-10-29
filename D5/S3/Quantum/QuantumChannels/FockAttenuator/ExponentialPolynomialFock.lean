/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial summability and genuine Fock realization of arbitrary polynomial-exponential blocks. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
import D5.S3.Analytic.Entire.ExponentialPolynomial
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-! Factorial estimates reconstruct entire exponential polynomials as completed Fock vectors. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter D5.S3.Analytic.Entire

/-- A factorial comparison with a complete exponential series, uniformly
valid for every nonnegative parameter; no numerical radius is selected. -/
theorem shifted_factorial_bound (m k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((k + m).factorial : ℝ) * R ^ k / (k.factorial : ℝ) ^ 2 ≤
      (m.factorial : ℝ) * 2 ^ m * ((2 * R) ^ k / (k.factorial : ℝ)) := by
  have hchoose : ((k + m).choose m : ℝ) ≤ (2 : ℝ) ^ (k + m) := by
    exact_mod_cast Nat.choose_le_two_pow (k + m) m
  have hfac : ((k + m).factorial : ℝ) =
      ((k + m).choose m : ℝ) * (k.factorial : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial k m).symm
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  calc
    ((k + m).factorial : ℝ) * R ^ k / (k.factorial : ℝ) ^ 2 =
        (((k + m).choose m : ℝ) * (k.factorial : ℝ) * (m.factorial : ℝ)) * R ^ k /
          (k.factorial : ℝ) ^ 2 := by rw [hfac]
    _ ≤ ((2 : ℝ) ^ (k + m) * (k.factorial : ℝ) * (m.factorial : ℝ)) * R ^ k /
          (k.factorial : ℝ) ^ 2 := by gcongr
    _ = _ := by
      rw [pow_add, mul_pow]
      field_simp
      <;> ring

theorem summable_shifted_factorial (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun k : ℕ => ((k + m).factorial : ℝ) * R ^ k / (k.factorial : ℝ) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => shifted_factorial_bound m k hR)
  exact (Real.summable_pow_div_factorial (2 * R)).mul_left ((m.factorial : ℝ) * 2 ^ m)

/-- Factorial-normalized coefficients of z^m exp(α z). -/
def monomialExponentialCoeff (m : ℕ) (α : ℂ) (n : ℕ) : ℂ :=
  if m ≤ n then
    (Real.sqrt (n.factorial : ℝ) : ℂ) * α ^ (n - m) / ((n - m).factorial : ℂ)
  else 0

theorem monomial_exponential_square_summable (m : ℕ) (α : ℂ) :
    Summable (fun n => ‖monomialExponentialCoeff m α n‖ ^ 2) := by
  apply (summable_nat_add_iff m).mp
  convert summable_shifted_factorial m (sq_nonneg ‖α‖) using 1
  ext k
  simp only [monomialExponentialCoeff, if_pos (Nat.le_add_left m k),
    Nat.add_sub_cancel, norm_div, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_natCast,
    div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), pow_right_comm ‖α‖ k 2]

/-- A genuine completed Hilbert vector, constructed from a proved square sum. -/
def monomialExponentialVector (m : ℕ) (α : ℂ) : Fock :=
  ⟨monomialExponentialCoeff m α, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      monomial_exponential_square_summable m α⟩

theorem transform_monomial_exponential (m : ℕ) (α z : ℂ) :
    transform (monomialExponentialVector m α) z = z ^ m * Complex.exp (α * z) := by
  let term : ℕ → ℂ := fun n => monomialExponentialCoeff m α n * z ^ n /
    (Real.sqrt (n.factorial : ℝ) : ℂ)
  have hshift : HasSum (fun k => term (k + m)) (z ^ m * Complex.exp (α * z)) := by
    have hs : HasSum (fun k : ℕ => z ^ m * ((α*z)^k / (k.factorial : ℂ)))
        (z ^ m * Complex.exp (α*z)) := by
      simpa only [← Complex.exp_eq_exp_ℂ] using
        (NormedSpace.expSeries_div_hasSum_exp (α * z)).mul_left (z ^ m)
    convert hs using 1
    ext k
    have hs : (Real.sqrt ((k + m).factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < ((k + m).factorial : ℝ))).ne'
    dsimp only [term]
    rw [monomialExponentialCoeff, if_pos (Nat.le_add_left m k), Nat.add_sub_cancel]
    rw [mul_pow, pow_add]
    field_simp
    <;> ring
  have hprefix : ∑ n ∈ Finset.range m, term n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [term, monomialExponentialCoeff,
      if_neg (Nat.not_le.mpr (Finset.mem_range.mp hn)), zero_mul, zero_div]
  have hfull := (hasSum_nat_add_iff m).mp hshift
  rw [hprefix, add_zero] at hfull
  exact (has_sum (monomialExponentialVector m α) z).unique hfull

/-- Explicit Fock reconstruction for a whole polynomial-exponential block. -/
def polynomialExponentialVector (α : ℂ) (p : Polynomial ℂ) : Fock :=
  ∑ n ∈ p.support, p.coeff n • monomialExponentialVector n α

theorem transform_polynomial_exponential (α : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    transform (polynomialExponentialVector α p) z = Complex.exp (α * z) * p.eval z := by
  simp only [polynomialExponentialVector, transform, inner_sum, inner_smul_right]
  change (∑ n ∈ p.support, p.coeff n * transform (monomialExponentialVector n α) z) = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  simp only [transform_monomial_exponential, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Every exponential polynomial admits a unique Fock preimage, with no
claim that arbitrary entire functions do. -/
theorem exponential_polynomial_reconstruction {f : ℂ → ℂ}
    (hf : ExponentialPolynomial f) : ∃! a : Fock, transform a = f := by
  obtain ⟨n, α, p, hf⟩ := hf
  let a : Fock := ∑ i : Fin n, polynomialExponentialVector (α i) (p i)
  have ha : transform a = f := by
    funext z
    simp only [a, transform, inner_sum]
    change (∑ i : Fin n, transform (polynomialExponentialVector (α i) (p i)) z) = _
    simp only [transform_polynomial_exponential, hf]
  exact ⟨a, ha, fun b hb => injective (hb.trans ha.symm)⟩

#print axioms monomial_exponential_square_summable
#print axioms exponential_polynomial_reconstruction

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
