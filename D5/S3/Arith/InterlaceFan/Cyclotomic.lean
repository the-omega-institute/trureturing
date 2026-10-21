/- GID: D5/S3/Arith/InterlaceFan/Cyclotomic
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Cyclotomic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.NumberTheory.Cyclotomic.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.Cyclotomic.Roots, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cosine evaluation, order-class propagation, and Ramanujan witnesses for the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

noncomputable section

open Finset Polynomial
open scoped BigOperators Nat Real

namespace D5.S3.Arith.InterlaceFan.Cyclotomic

open D5.S3.Arith.InterlaceFan.Defs
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

/- The real evaluation of the palindromic Fourier polynomial at the j-th
   root.  Writing it as a real sum keeps the sigma-coordinate convention
   explicit and avoids a hidden choice of the middle coefficient. -/
def evalCos (n j : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  ∑ k : Fin (n / 2), 2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k

/- The factor two in `evalCos` is the pair of reciprocal monomials; `I` is
   the negative half of this real evaluation. -/
theorem I_eq_eval (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    I n j x = -(1 / 2 : ℝ) * evalCos n j x := by
  simp only [I, evalCos]
  change (∑ k : Fin (n / 2),
      -Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k) =
    (-(1 / 2 : ℝ)) • ∑ k : Fin (n / 2),
      2 * Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k
  rw [Finset.smul_sum (s := (Finset.univ : Finset (Fin (n / 2))))]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring


/-- The reciprocal polynomial in the pinned sigma coordinates. -/
def sigmaPoly {R : Type*} [CommRing R] (n : ℕ) (x : Fin (n / 2) → R) : R[X] :=
  ∑ k : Fin (n / 2), Polynomial.C (x k) *
    (Polynomial.X ^ ((k : ℕ) + 1) + Polynomial.X ^ (n - ((k : ℕ) + 1)))

/-- The standard primitive root of unity. -/
def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

private lemma zeta_pow (n j m : ℕ) :
    (zeta n ^ j) ^ m = Complex.exp
      ((2 * Real.pi * j * m / n : ℝ) * Complex.I) := by
  simp only [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma reciprocal_pair (n j m : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    (zeta n ^ j) ^ m + (zeta n ^ j) ^ (n - m) =
      (2 * Real.cos (2 * Real.pi * j * m / n) : ℝ) := by
  have hz := Complex.isPrimitiveRoot_exp n hn.ne'
  have hz0 : zeta n ^ j ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hzn : (zeta n ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm j n, pow_mul]
    simpa [zeta] using congrArg (fun z : ℂ => z ^ j) hz.pow_eq_one
  rw [pow_sub₀ _ hz0 hm, hzn, one_mul, zeta_pow, ← Complex.exp_neg]
  have hc := Complex.two_cos ((2 * Real.pi * j * m / n : ℝ) : ℂ)
  push_cast at hc ⊢
  rw [show -((2 * (Real.pi : ℂ) * j * m / n) * Complex.I) =
    -(2 * (Real.pi : ℂ) * j * m / n) * Complex.I by ring]
  simpa using hc.symm

/-- Evaluation of the reciprocal polynomial is the real cosine sum. -/
theorem I_eq_eval_poly (n j : ℕ) (x : Fin (n / 2) → ℝ) :
    ((sigmaPoly n x).map Complex.ofRealHom).eval (zeta n ^ j) =
      (evalCos n j x : ℂ) := by
  classical
  simp only [sigmaPoly, Polynomial.map_sum, Polynomial.eval_finsetSum,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, evalCos,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := k.isLt
  rw [reciprocal_pair n j ((k : ℕ) + 1) (by omega) (by omega)]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

private lemma primitive_orderClass (n d j : ℕ) (hn : 0 < n)
    (hj : j ∈ orderClass n d) : IsPrimitiveRoot (zeta n ^ j) d := by
  have hd := (Finset.mem_filter.mp hj).2
  rw [← hd]
  exact (Complex.isPrimitiveRoot_exp n hn.ne').pow_div_gcd j
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left j hn))

/-- Rational values propagate across every primitive-root order class. -/
theorem rational_const_on_orderClass (n d : ℕ) (hn : 0 < n) (hd : d ∣ n)
    (x : Fin (n / 2) → ℝ) (hx : IsRationalPt x) (c : ℚ)
    (s t : ℕ) (hs : s ∈ orderClass n d) (ht : t ∈ orderClass n d)
    (hcs : I n s x = (c : ℝ)) : I n t x = (c : ℝ) := by
  classical
  choose q hq using hx
  have hpmap : (sigmaPoly n q).map (algebraMap ℚ ℂ) =
      (sigmaPoly n x).map Complex.ofRealHom := by
    simp only [sigmaPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hq k]
    simp
  have he (j : ℕ) : aeval (zeta n ^ j) (sigmaPoly n q) =
      (evalCos n j x : ℂ) := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpmap]
    exact I_eq_eval_poly n j x
  have hEs : evalCos n s x = -2 * (c : ℝ) := by
    have := I_eq_eval n s x
    linarith
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hdiv : cyclotomic d ℚ ∣ sigmaPoly n q - Polynomial.C (-2 * c) := by
    rw [cyclotomic_eq_minpoly_rat (primitive_orderClass n d s hn hs) hdpos]
    apply minpoly.dvd ℚ (zeta n ^ s)
    simp [he, hEs]
  have hroot : aeval (zeta n ^ t) (cyclotomic d ℚ) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact (primitive_orderClass n d t hn ht).isRoot_cyclotomic hdpos
  have hz := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hroot
  rw [map_sub, he] at hz
  have hEt : evalCos n t x = -2 * (c : ℝ) := by
    have hreal := congrArg Complex.re hz
    have hr : evalCos n t x + 2 * (c : ℝ) = 0 := by simpa using hreal
    linarith
  rw [I_eq_eval, hEt]
  ring

end D5.S3.Arith.InterlaceFan.Cyclotomic
