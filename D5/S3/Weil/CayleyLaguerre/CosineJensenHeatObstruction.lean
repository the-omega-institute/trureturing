/- GID: D5/S3/Weil/CayleyLaguerre/CosineJensenHeatObstruction
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/CosineJensenHeatObstruction
   mirror-E: none(waiver:analytic-family-counterexample)
   anchors: []
   utility: none
   digest: Positive-degree shifted Jensen tests need not detect nonreal heat-flow zeros. -/

import OmegaMath.Analysis.ConjugatePowerZeros
import D5.S3.Zeros.Jensen.JensenPolynomialObstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Full Taylor Jensen rows of the cosine backward heat family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction

open Polynomial
open D5.S3.Zeros.Jensen.JensenPolynomialObstruction

/-- The entire cosine heat family, with complex time as an analytic extension. -/
def cosineHeat (c : ℝ) (t z : ℂ) : ℂ := Complex.exp t * Complex.cos z + c

/-- The actual real Taylor derivatives at the origin, with no even-square reindexing. -/
def cosineHeatJet (c t : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k (fun x : ℝ => Real.exp t * Real.cos x + c) 0

private theorem phase_even (m : ℕ) : (Complex.I ^ (2 * m)).re = (-1 : ℝ) ^ m := by
  have hp : Complex.I ^ (2 * m) = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    rw [pow_mul, Complex.I_sq]
    norm_cast
  rw [hp, Complex.ofReal_re]

private theorem phase_odd (m : ℕ) : (Complex.I ^ (2 * m + 1)).re = 0 := by
  have hp : (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by norm_cast
  rw [pow_add, pow_mul, Complex.I_sq, hp]
  simp only [pow_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self]

private theorem cosine_derivative_zero (k : ℕ) :
    iteratedDeriv k Real.cos 0 = (Complex.I ^ k).re := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hk : k = 2 * m := by omega
    rw [hk, Real.iteratedDeriv_even_cos]
    simp [phase_even]
  · have hk : k = 2 * m + 1 := by omega
    rw [hk, Real.iteratedDeriv_odd_cos]
    simp [phase_odd]

private theorem positive_jet (c t : ℝ) (k : ℕ) (hk : 0 < k) :
    cosineHeatJet c t k = Real.exp t * (Complex.I ^ k).re := by
  unfold cosineHeatJet
  have hf : (fun x : ℝ => Real.exp t * Real.cos x + c) =
      (fun x : ℝ => c + Real.exp t * Real.cos x) := by funext x; ring
  rw [hf, iteratedDeriv_const_add hk c, iteratedDeriv_const_mul_field,
    cosine_derivative_zero]

private theorem binomial_power (w : ℂ) (d : ℕ) :
    (1 + w) ^ d = ∑ k ∈ Finset.range (d + 1), (d.choose k : ℂ) * w ^ k := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp [mul_comm]

private theorem jensen_cosine_eval (c t : ℝ) (d n : ℕ) (hn : 0 < n) (z : ℂ) :
    2 * ((jensenPolynomial (cosineHeatJet c t) d n).map (algebraMap ℝ ℂ)).eval z =
      (Real.exp t : ℂ) *
        (Complex.I ^ n * (1 + Complex.I * z) ^ d +
          (-Complex.I) ^ n * (1 - Complex.I * z) ^ d) := by
  have hc (k : ℕ) : (algebraMap ℝ ℂ) (cosineHeatJet c t (n + k)) =
      (Real.exp t : ℂ) *
        (Complex.I ^ (n + k) + (-Complex.I) ^ (n + k)) / 2 := by
    change (cosineHeatJet c t (n + k) : ℂ) = _
    rw [positive_jet c t (n + k) (by omega), Complex.ofReal_mul,
      Complex.re_eq_add_conj]
    simp only [map_pow, Complex.conj_I]
    ring
  simp only [jensenPolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    eval_mul, eval_finsetSum, eval_C, eval_pow, eval_X,
    map_mul, hc]
  rw [binomial_power, show 1 - Complex.I * z = 1 + (-Complex.I) * z by ring,
    binomial_power]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  simp only [pow_add, mul_pow]
  ring

private theorem positive_shifts_hyperbolic (c t : ℝ) (d n : ℕ)
    (hd : 0 < d) (hn : 0 < n) :
    PolynomialHyperbolic (jensenPolynomial (cosineHeatJet c t) d n) := by
  intro z hz
  have he := jensen_cosine_eval c t d n hn z
  rw [hz, mul_zero] at he
  have hphase : Complex.I ^ n * (1 + Complex.I * z) ^ d +
      (-Complex.I) ^ n * (1 - Complex.I * z) ^ d = 0 := by
    exact (mul_eq_zero.mp he.symm).resolve_left
      (by exact_mod_cast Real.exp_ne_zero t)
  exact Omega.conjugate_power_sum_root_real _ _ z d
    (pow_ne_zero n Complex.I_ne_zero) (by simp) (Nat.ne_of_gt hd) hphase

private theorem positive_shift_classification (c t : ℝ) (d n : ℕ) (hn : 0 < n) :
    PolynomialHyperbolic (jensenPolynomial (cosineHeatJet c t) d n) ↔
      0 < d ∨ Even n := by
  by_cases hd : 0 < d
  · exact iff_of_true (positive_shifts_hyperbolic c t d n hd hn) (Or.inl hd)
  have hd0 : d = 0 := by omega
  subst d
  simp only [hd, false_or]
  rcases Nat.even_or_odd n with he | ho
  · rcases he with ⟨m, hm⟩
    have hp : cosineHeatJet c t n ≠ 0 := by
      rw [positive_jet c t n hn, show n = 2 * m by omega, phase_even]
      exact mul_ne_zero (Real.exp_ne_zero t) (pow_ne_zero m (by norm_num))
    refine iff_of_true ?_ ⟨m, hm⟩
    intro z hz
    have hh : (cosineHeatJet c t n : ℂ) = 0 := by
      simpa [jensenPolynomial] using hz
    exact False.elim (hp (Complex.ofReal_eq_zero.mp hh))
  · have hp : cosineHeatJet c t n = 0 := by
      rcases ho with ⟨m, hm⟩
      rw [positive_jet c t n hn, show n = 2 * m + 1 by omega, phase_odd, mul_zero]
    have hne : ¬ Even n := by
      rintro ⟨j, hj⟩
      rcases ho with ⟨m, hm⟩
      omega
    refine iff_of_false ?_ hne
    intro h
    have hh := h Complex.I (by simp [jensenPolynomial, hp])
    norm_num at hh

private theorem cosine_heat_equation (c : ℝ) (t z : ℂ) :
    deriv (fun u : ℂ => cosineHeat c u z) t =
      -deriv (deriv (cosineHeat c t)) z := by
  have ht := (((Complex.hasDerivAt_exp t).mul_const (Complex.cos z)).add_const
    (c : ℂ)).deriv
  have hx : deriv (cosineHeat c t) =
      fun w : ℂ => -(Complex.exp t) * Complex.sin w := by
    funext w
    have hw := (((Complex.hasDerivAt_cos w).const_mul (Complex.exp t)).add_const
      (c : ℂ)).deriv
    change deriv (fun z : ℂ => Complex.exp t * Complex.cos z + c) w = _
    rw [hw]
    ring
  rw [hx]
  change deriv (fun u : ℂ => Complex.exp u * Complex.cos z + c) t = _
  rw [ht, ((Complex.hasDerivAt_sin z).const_mul (-Complex.exp t)).deriv]
  ring

/-- A backward heat family can have every positive-degree, positive-shift Jensen
row hyperbolic at every real time, yet have a specified nonreal zero at any chosen
time. The full classification also accounts for degree-zero rows. This refutes
the sufficiency of positive-shift hyperbolicity alone for real source zeros. -/
theorem positive_shift_heat_counterexample (t y : ℝ) (hy : y ≠ 0) :
    let c := Real.exp t * Real.cosh y
    (∀ u z : ℂ, deriv (fun s : ℂ => cosineHeat c s z) u =
      -deriv (deriv (cosineHeat c u)) z) ∧
    (∀ (u : ℝ) (d n : ℕ), 0 < n →
      (PolynomialHyperbolic (jensenPolynomial (cosineHeatJet c u) d n) ↔
        0 < d ∨ Even n)) ∧
    cosineHeat c (t : ℂ) ((Real.pi : ℂ) + (y : ℂ) * Complex.I) = 0 ∧
    ((Real.pi : ℂ) + (y : ℂ) * Complex.I).im ≠ 0 := by
  dsimp only
  refine ⟨cosine_heat_equation _, positive_shift_classification _, ?_, ?_⟩
  · simp [cosineHeat, Complex.cos_add_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, Real.cos_pi, Real.sin_pi,
      ← Complex.ofReal_exp]
  · simpa using hy

#print axioms positive_shift_heat_counterexample

end D5.S3.Weil.CayleyLaguerre.CosineJensenHeatObstruction
