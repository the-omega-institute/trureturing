/- GID: D5/S3/Analytic/PolynomialL2Derivative
   generality: G
   mirror-B: D5/B/S3/Analytic/PolynomialL2Derivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.ShiftedLegendre, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta]
   utility: none
   digest: The derivative L2 energy of a complex polynomial on [0,1] is bounded by d^4 times its L2 energy when its degree is below d. -/

import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Complex polynomial derivative energy on the unit interval

Shifted Legendre polynomials give an orthogonal basis with squared norms
`1 / (2n + 1)`. Rodrigues' formula and integration by parts establish
orthogonality; the beta integral gives normalization. Endpoint values give
derivative energies `2n(n + 1)`. Parseval and weighted Cauchy–Schwarz then
bound derivative energy by `d²(d² - 1)` times polynomial energy, hence by
`d⁴`. Coefficients are complex throughout, with conjugation explicit in
Parseval. The degree formulation includes the zero-dimensional case.
-/

noncomputable section

open Polynomial MeasureTheory Set
open scoped Interval ComplexConjugate

namespace D5.S3.Analytic.PolynomialL2Derivative

/-- The actual upstream integer shifted Legendre polynomial, mapped to ℂ. -/
private def legendreC (n : ℕ) : ℂ[X] :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℂ)

private def rod (n : ℕ) : ℂ[X] := X ^ n * (1 - X) ^ n

/-- A bilinear moment. Conjugation will be supplied explicitly by mapping
the coefficients of the second polynomial. -/
private def moment (p q : ℂ[X]) : ℂ :=
  ∫ x : ℝ in 0..1, p.eval (x : ℂ) * q.eval (x : ℂ)

private lemma eval_continuous (p : ℂ[X]) :
    Continuous (fun x : ℝ => p.eval (x : ℂ)) :=
  p.continuous.comp Complex.continuous_ofReal

private lemma eval_integrable (p : ℂ[X]) :
    IntervalIntegrable (fun x : ℝ => p.eval (x : ℂ)) volume 0 1 :=
  (eval_continuous p).intervalIntegrable 0 1

private lemma moment_zero_right (p : ℂ[X]) : moment p 0 = 0 := by
  simp [moment]

private lemma moment_zero_left (q : ℂ[X]) : moment 0 q = 0 := by
  simp [moment]

private lemma moment_C_mul_left (a : ℂ) (p q : ℂ[X]) :
    moment (C a * p) q = a * moment p q := by
  simp only [moment, eval_mul, eval_C, mul_assoc,
    intervalIntegral.integral_const_mul]

private lemma moment_C_right (p : ℂ[X]) (a : ℂ) :
    moment p (C a) = (∫ x : ℝ in 0..1, p.eval (x : ℂ)) * a := by
  simp only [moment, eval_C, intervalIntegral.integral_mul_const]

private lemma moment_comm (p q : ℂ[X]) : moment p q = moment q p := by
  simp only [moment, mul_comm]

/-- A single integration by parts, with all analytic hypotheses supplied
by continuity of polynomial evaluations on the real interval. -/
private lemma moment_derivative (p q : ℂ[X]) :
    moment p.derivative q =
      p.eval 1 * q.eval 1 - p.eval 0 * q.eval 0 - moment p q.derivative := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (u := fun x : ℝ => q.eval (x : ℂ))
    (v := fun x : ℝ => p.eval (x : ℂ))
    (u' := fun x : ℝ => q.derivative.eval (x : ℂ))
    (v' := fun x : ℝ => p.derivative.eval (x : ℂ))
    (eval_continuous q).continuousOn (eval_continuous p).continuousOn
    (fun x _ => (q.hasDerivAt (x : ℂ)).comp_ofReal)
    (fun x _ => (p.hasDerivAt (x : ℂ)).comp_ofReal)
    (eval_integrable q.derivative) (eval_integrable p.derivative)
  simpa only [moment, Complex.ofReal_zero, Complex.ofReal_one, mul_comm] using h

private lemma moment_derivative_of_endpoints (p q : ℂ[X])
    (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    moment p.derivative q = -moment p q.derivative := by
  rw [moment_derivative, h0, h1]
  simp

/-- Finite repeated integration by parts. This proof uses exactly the
endpoint derivatives below the order being transferred. -/
private lemma moment_iterate_derivative (m : ℕ) (p q : ℂ[X])
    (h0 : ∀ k < m, (derivative^[k] p).eval 0 = 0)
    (h1 : ∀ k < m, (derivative^[k] p).eval 1 = 0) :
    moment (derivative^[m] p) q =
      (-1 : ℂ) ^ m * moment p (derivative^[m] q) := by
  revert q h0 h1
  induction m with
  | zero =>
    intro q h0 h1
    simp
  | succ m ih =>
    intro q h0 h1
    calc
      moment (derivative^[m + 1] p) q =
          -moment (derivative^[m] p) q.derivative := by
        rw [Function.iterate_succ_apply']
        exact moment_derivative_of_endpoints _ _
          (h0 m (Nat.lt_succ_self m)) (h1 m (Nat.lt_succ_self m))
      _ = -((-1 : ℂ) ^ m * moment p (derivative^[m] q.derivative)) := by
        rw [ih q.derivative
          (fun k hk => h0 k (Nat.lt_trans hk (Nat.lt_succ_self m)))
          (fun k hk => h1 k (Nat.lt_trans hk (Nat.lt_succ_self m)))]
      _ = (-1 : ℂ) ^ (m + 1) * moment p (derivative^[m + 1] q) := by
        rw [Function.iterate_succ_apply, pow_succ]
        ring

/-- Each derivative of the Rodrigues primitive below order n vanishes at
0. The divisor remains X^(n-k), whose exponent is strictly positive. -/
private lemma rod_derivative_eval_zero {n k : ℕ} (hk : k < n) :
    (derivative^[k] (rod n)).eval 0 = 0 := by
  have hd : (X : ℂ[X]) ^ (n - k) ∣ derivative^[k] (rod n) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k
      (show (X : ℂ[X]) ^ n ∣ rod n from dvd_mul_right _ _)
  obtain ⟨q, hq⟩ := hd
  rw [hq, eval_mul, eval_pow, eval_X,
    zero_pow (Nat.sub_ne_zero_of_lt hk), zero_mul]

/-- At 1 we use the divisor (1-X)^(n-k); no multiplicity assertion for the
zero polynomial and no endpoint regularity premise is needed. -/
private lemma rod_derivative_eval_one {n k : ℕ} (hk : k < n) :
    (derivative^[k] (rod n)).eval 1 = 0 := by
  have hd : (1 - (X : ℂ[X])) ^ (n - k) ∣ derivative^[k] (rod n) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k
      (show (1 - (X : ℂ[X])) ^ n ∣ rod n from dvd_mul_left _ _)
  obtain ⟨q, hq⟩ := hd
  rw [hq, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self,
    zero_pow (Nat.sub_ne_zero_of_lt hk), zero_mul]

/-- Rodrigues' formula is transported from the actual ℤ-polynomial
identity, using the pinned derivative/map commutation theorem. -/
private lemma rodrigues (n : ℕ) :
    (n.factorial : ℂ[X]) * legendreC n = derivative^[n] (rod n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  simp only [Polynomial.map_mul, Polynomial.map_natCast] at h
  rw [← Polynomial.iterate_derivative_map
    ((X : ℤ[X]) ^ n * (1 - X) ^ n) (Int.castRingHom ℂ) n] at h
  simpa only [legendreC, rod, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X] using h

private lemma factorial_ne_zero_complex (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

/-- The full Rodrigues transfer identity, before imposing any degree
bound on the test polynomial. -/
private theorem shiftedLegendre_rodrigues_transfer (n : ℕ) (p : ℂ[X]) :
    (n.factorial : ℂ) *
        (∫ x : ℝ in 0..1, (legendreC n).eval (x : ℂ) * p.eval (x : ℂ)) =
      (-1 : ℂ) ^ n *
        (∫ x : ℝ in 0..1,
          (x : ℂ) ^ n * (1 - (x : ℂ)) ^ n *
            (derivative^[n] p).eval (x : ℂ)) := by
  calc
    (n.factorial : ℂ) * moment (legendreC n) p =
        moment ((n.factorial : ℂ[X]) * legendreC n) p := by
      simpa only [C_eq_natCast] using
        (moment_C_mul_left (n.factorial : ℂ) (legendreC n) p).symm
    _ = moment (derivative^[n] (rod n)) p := by rw [rodrigues]
    _ = (-1 : ℂ) ^ n * moment (rod n) (derivative^[n] p) :=
      moment_iterate_derivative n (rod n) p
        (fun _ hk => rod_derivative_eval_zero hk)
        (fun _ hk => rod_derivative_eval_one hk)
    _ = _ := by simp only [moment, rod, eval_mul, eval_pow, eval_X, eval_sub, eval_one]

/-- Bilinear lower-degree orthogonality, including n=0 with p=0 under
the WithBot-valued degree formulation. -/
private theorem shiftedLegendre_mul_integral_eq_zero (n : ℕ) (p : ℂ[X])
    (hp : p.degree < (n : WithBot ℕ)) :
    (∫ x : ℝ in 0..1, (legendreC n).eval (x : ℂ) * p.eval (x : ℂ)) = 0 := by
  have h := shiftedLegendre_rodrigues_transfer n p
  rw [Polynomial.iterate_derivative_eq_zero_of_degree_lt hp] at h
  simp only [eval_zero, mul_zero, intervalIntegral.integral_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (factorial_ne_zero_complex n)

/-- Conjugating coefficients really conjugates polynomial values at real
arguments; this explicitly retains arbitrary complex coefficients. -/
private lemma eval_map_conj (p : ℂ[X]) (x : ℝ) :
    (p.map (starRingEnd ℂ)).eval (x : ℂ) = conj (p.eval (x : ℂ)) := by
  simpa only [Complex.conj_ofReal] using
    (Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) (x : ℂ))

/-- The requested complex Rodrigues orthogonality theorem. Its only
substantive hypothesis is the actual degree bound on the test polynomial. -/
private theorem shiftedLegendre_mul_conj_integral_eq_zero (n : ℕ) (p : ℂ[X])
    (hp : p.degree < (n : WithBot ℕ)) :
    (∫ x : ℝ in 0..1,
      (legendreC n).eval (x : ℂ) * conj (p.eval (x : ℂ))) = 0 := by
  have hdeg : (p.map (starRingEnd ℂ)).degree < (n : WithBot ℕ) :=
    Polynomial.degree_map_le.trans_lt hp
  have h := shiftedLegendre_mul_integral_eq_zero n (p.map (starRingEnd ℂ)) hdeg
  simpa only [eval_map_conj] using h

/-- The natDegree version used by dimension-bounded complex polynomials.
In particular p=0 is allowed whenever n≥1. -/
private theorem shiftedLegendre_mul_conj_integral_eq_zero_of_natDegree
    (n : ℕ) (p : ℂ[X]) (hp : p.natDegree < n) :
    (∫ x : ℝ in 0..1,
      ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℂ)).eval (x : ℂ) *
        conj (p.eval (x : ℂ))) = 0 := by
  apply shiftedLegendre_mul_conj_integral_eq_zero n p
  exact Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr hp)

/-- The zero-polynomial boundary case, also at n=0. -/
private theorem shiftedLegendre_mul_conj_zero (n : ℕ) :
    (∫ x : ℝ in 0..1,
      (legendreC n).eval (x : ℂ) * conj ((0 : ℂ[X]).eval (x : ℂ))) = 0 := by
  simp

private lemma coeff_legendreC (n k : ℕ) :
    (legendreC n).coeff k =
      (-1 : ℂ) ^ k * (n.choose k : ℂ) * ((n + k).choose n : ℂ) := by
  simp [legendreC, Polynomial.coeff_shiftedLegendre]

private lemma degree_legendreC (n : ℕ) : (legendreC n).degree = n := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := by
    intro a b h
    change (a : ℂ) = (b : ℂ) at h
    exact Int.cast_injective h
  exact (Polynomial.degree_map_eq_of_injective hinj _).trans
    (Polynomial.degree_shiftedLegendre n)

private lemma natDegree_legendreC (n : ℕ) : (legendreC n).natDegree = n :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_legendreC n)

private lemma legendreC_map_conj (n : ℕ) :
    (legendreC n).map (starRingEnd ℂ) = legendreC n := by
  unfold legendreC
  rw [Polynomial.map_map]
  apply congrArg (fun f : ℤ →+* ℂ => (Polynomial.shiftedLegendre n).map f)
  exact RingHom.ext (fun z => by simp)

private lemma legendreC_eval_conj (n : ℕ) (x : ℝ) :
    conj ((legendreC n).eval (x : ℂ)) = (legendreC n).eval (x : ℂ) := by
  have h := eval_map_conj (legendreC n) x
  rw [legendreC_map_conj] at h
  exact h.symm

/-- The complex bilinear moments are zero for distinct indices. -/
private theorem shiftedLegendre_pairwise_moment_zero {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ in 0..1,
      (legendreC m).eval (x : ℂ) * (legendreC n).eval (x : ℂ)) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [show (∫ x : ℝ in 0..1,
        (legendreC m).eval (x : ℂ) * (legendreC n).eval (x : ℂ)) =
        moment (legendreC n) (legendreC m) from moment_comm _ _]
    apply shiftedLegendre_mul_integral_eq_zero n (legendreC m)
    rw [degree_legendreC]
    exact WithBot.coe_lt_coe.mpr h
  · apply shiftedLegendre_mul_integral_eq_zero m (legendreC n)
    rw [degree_legendreC]
    exact WithBot.coe_lt_coe.mpr h

private lemma iterate_derivative_eq_C_top (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree ≤ n) :
    derivative^[n] p = C ((n.factorial : ℂ) * p.coeff n) := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
    simp only [coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
      nsmul_eq_mul, coeff_C_zero]
  | succ k =>
    have hc : p.coeff (k + 1 + n) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [coeff_iterate_derivative, hc]
    simp

private lemma moment_legendreC_top (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree ≤ n) :
    moment (legendreC n) p =
      (-1 : ℂ) ^ n * p.coeff n *
        (∫ x : ℝ in 0..1, (rod n).eval (x : ℂ)) := by
  have h : (n.factorial : ℂ) * moment (legendreC n) p =
      (-1 : ℂ) ^ n * moment (rod n) (derivative^[n] p) := by
    simpa only [moment, rod, eval_mul, eval_pow, eval_X, eval_sub, eval_one] using
      shiftedLegendre_rodrigues_transfer n p
  rw [iterate_derivative_eq_C_top n p hp, moment_C_right] at h
  apply mul_left_cancel₀ (factorial_ne_zero_complex n)
  calc
    (n.factorial : ℂ) * moment (legendreC n) p =
        (-1 : ℂ) ^ n *
          ((∫ x : ℝ in 0..1, (rod n).eval (x : ℂ)) *
            ((n.factorial : ℂ) * p.coeff n)) := h
    _ = _ := by ring

/-- The primitive's beta-power integral, using the actual pinned complex
Beta/Gamma identities and their positivity hypotheses. -/
private lemma integral_rod (n : ℕ) :
    (∫ x : ℝ in 0..1, (rod n).eval (x : ℂ)) =
      (n.factorial : ℂ) * (n.factorial : ℂ) / ((2 * n + 1).factorial : ℂ) := by
  have hn : 0 < ((n : ℂ) + 1).re := by
    simpa using (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have hsum : ((n : ℂ) + 1) + ((n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  calc
    (∫ x : ℝ in 0..1, (rod n).eval (x : ℂ)) =
        Complex.betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1) := by
      simp only [rod, eval_mul, eval_pow, eval_X, eval_sub, eval_one,
        Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hn hn, hsum]
      simp only [Complex.Gamma_nat_eq_factorial]

private lemma sign_mul_sign (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

/-- Exact normalization as a complex bilinear moment. -/
private theorem shiftedLegendre_square_integral (n : ℕ) :
    (∫ x : ℝ in 0..1,
      (legendreC n).eval (x : ℂ) * (legendreC n).eval (x : ℂ)) =
        (1 : ℂ) / (2 * (n : ℂ) + 1) := by
  have ht := moment_legendreC_top n (legendreC n) (natDegree_legendreC n).le
  have hc : ((n + n).choose n : ℂ) * (n.factorial : ℂ) * (n.factorial : ℂ) =
      ((n + n).factorial : ℂ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
  have hfac : ((2 * n + 1).factorial : ℂ) =
      (2 * (n : ℂ) + 1) * ((n + n).factorial : ℂ) := by
    rw [show 2 * n + 1 = (n + n) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have ha : 2 * (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  have hf := factorial_ne_zero_complex (n + n)
  calc
    moment (legendreC n) (legendreC n) =
        (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * ((n + n).choose n : ℂ)) *
          (∫ x : ℝ in 0..1, (rod n).eval (x : ℂ)) := by
      simpa only [coeff_legendreC, Nat.choose_self, Nat.cast_one, mul_one] using ht
    _ = ((n + n).choose n : ℂ) *
        ((n.factorial : ℂ) * (n.factorial : ℂ) / ((2 * n + 1).factorial : ℂ)) := by
      rw [integral_rod]
      calc
        _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
            (((n + n).choose n : ℂ) *
              ((n.factorial : ℂ) * (n.factorial : ℂ) /
                ((2 * n + 1).factorial : ℂ))) := by ring
        _ = _ := by rw [sign_mul_sign, one_mul]
    _ = (((n + n).choose n : ℂ) * (n.factorial : ℂ) * (n.factorial : ℂ)) /
        ((2 * (n : ℂ) + 1) * ((n + n).factorial : ℂ)) := by rw [hfac]; ring
    _ = ((n + n).factorial : ℂ) /
        ((2 * (n : ℂ) + 1) * ((n + n).factorial : ℂ)) := by rw [hc]
    _ = (1 : ℂ) / (2 * (n : ℂ) + 1) := by field_simp [ha, hf]

private lemma norm_sq_integral_eq_moment (p : ℂ[X]) :
    ((∫ x : ℝ in 0..1, ‖p.eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      moment p (p.map (starRingEnd ℂ)) := by
  calc
    ((∫ x : ℝ in 0..1, ‖p.eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∫ x : ℝ in 0..1, ((‖p.eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) :=
      (intervalIntegral.integral_ofReal
        (f := fun x : ℝ => ‖p.eval (x : ℂ)‖ ^ 2)).symm
    _ = _ := by
      unfold moment
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [eval_map_conj, Complex.sq_norm, Complex.mul_conj]

/-- Exact squared L2 norm. This also includes the constant n=0 member. -/
private theorem shiftedLegendre_norm_sq_integral (n : ℕ) :
    (∫ x : ℝ in 0..1, ‖(legendreC n).eval (x : ℂ)‖ ^ 2) =
      (1 : ℝ) / (2 * (n : ℝ) + 1) := by
  have h : ((∫ x : ℝ in 0..1, ‖(legendreC n).eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      (1 : ℂ) / (2 * (n : ℂ) + 1) := by
    rw [norm_sq_integral_eq_moment, legendreC_map_conj]
    exact shiftedLegendre_square_integral n
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast] using h

private lemma legendreC_eval_zero (n : ℕ) : (legendreC n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_legendreC]
  simp

private lemma legendreC_derivative_eval_zero (n : ℕ) :
    (legendreC n).derivative.eval 0 = -(n : ℂ) * ((n : ℂ) + 1) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_derivative, coeff_legendreC]
  simp only [zero_add, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
  ring

private lemma legendreC_reflection (n : ℕ) :
    C ((-1 : ℂ) ^ n) * (legendreC n).comp (1 - X) = legendreC n := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ))
    (Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n)
  have hc : (C ((-1 : ℂ) ^ n) : ℂ[X]) = (-1) ^ n := by simp
  rw [hc]
  simpa [legendreC, Polynomial.map_comp] using h

private lemma legendreC_eval_one (n : ℕ) :
    (legendreC n).eval 1 = (-1 : ℂ) ^ n := by
  have h : (-1 : ℂ) ^ n * (legendreC n).eval 1 = 1 := by
    simpa only [eval_mul, eval_C, eval_comp, eval_sub, eval_one, eval_X,
      sub_zero, legendreC_eval_zero] using
      congrArg (fun p : ℂ[X] => p.eval 0) (legendreC_reflection n)
  calc
    (legendreC n).eval 1 =
        ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (legendreC n).eval 1 := by
      rw [sign_mul_sign, one_mul]
    _ = (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * (legendreC n).eval 1) := by ring
    _ = (-1 : ℂ) ^ n := by rw [h, mul_one]

private lemma legendreC_derivative_eval_one (n : ℕ) :
    (legendreC n).derivative.eval 1 =
      (-1 : ℂ) ^ n * (n : ℂ) * ((n : ℂ) + 1) := by
  have h : (-1 : ℂ) ^ n * (-(legendreC n).derivative.eval 1) =
      -(n : ℂ) * ((n : ℂ) + 1) := by
    simpa only [Polynomial.derivative_C_mul, Polynomial.derivative_comp_one_sub_X,
      eval_mul, eval_C, eval_neg, eval_comp, eval_sub, eval_one, eval_X,
      sub_zero, legendreC_derivative_eval_zero] using
      congrArg (fun p : ℂ[X] => p.derivative.eval 0) (legendreC_reflection n)
  have hs := sign_mul_sign n
  linear_combination (-((-1 : ℂ) ^ n)) * h -
    (legendreC n).derivative.eval 1 * hs

private lemma legendreC_derivative_map_conj (n : ℕ) :
    (legendreC n).derivative.map (starRingEnd ℂ) = (legendreC n).derivative := by
  rw [← Polynomial.derivative_map (legendreC n) (starRingEnd ℂ), legendreC_map_conj]

/-- The derivative energy is paid by the actual endpoint values. The
remaining integral contains L_n'' and vanishes by the proved orthogonality. -/
private theorem shiftedLegendre_derivative_square_integral (n : ℕ) :
    (∫ x : ℝ in 0..1,
      (legendreC n).derivative.eval (x : ℂ) *
        (legendreC n).derivative.eval (x : ℂ)) =
      2 * (n : ℂ) * ((n : ℂ) + 1) := by
  by_cases hn : n = 0
  · subst n
    have hd : (legendreC 0).derivative = 0 :=
      Polynomial.derivative_of_natDegree_zero (natDegree_legendreC 0)
    simp [hd]
  have hnd : (legendreC n).derivative.derivative.natDegree ≤ n - 1 - 1 :=
    (Polynomial.natDegree_derivative_le _).trans
      (Nat.sub_le_sub_right
        ((Polynomial.natDegree_derivative_le _).trans_eq
          (congrArg (fun k : ℕ => k - 1) (natDegree_legendreC n))) 1)
  have hsmall : (legendreC n).derivative.derivative.natDegree < n := by omega
  have hlow : (legendreC n).derivative.derivative.degree < (n : WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hsmall)
  have hz : moment (legendreC n) (legendreC n).derivative.derivative = 0 :=
    shiftedLegendre_mul_integral_eq_zero n _ hlow
  calc
    moment (legendreC n).derivative (legendreC n).derivative =
        (legendreC n).eval 1 * (legendreC n).derivative.eval 1 -
          (legendreC n).eval 0 * (legendreC n).derivative.eval 0 -
            moment (legendreC n) (legendreC n).derivative.derivative :=
      moment_derivative _ _
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (n : ℂ) * ((n : ℂ) + 1) +
        (n : ℂ) * ((n : ℂ) + 1) := by
      rw [legendreC_eval_one, legendreC_derivative_eval_one,
        legendreC_eval_zero, legendreC_derivative_eval_zero, hz]
      ring
    _ = 2 * (n : ℂ) * ((n : ℂ) + 1) := by rw [sign_mul_sign]; ring

private theorem shiftedLegendre_derivative_norm_sq_integral (n : ℕ) :
    (∫ x : ℝ in 0..1, ‖(legendreC n).derivative.eval (x : ℂ)‖ ^ 2) =
      2 * (n : ℝ) * ((n : ℝ) + 1) := by
  have h : ((∫ x : ℝ in 0..1,
      ‖(legendreC n).derivative.eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        2 * (n : ℂ) * ((n : ℂ) + 1) := by
    rw [norm_sq_integral_eq_moment, legendreC_derivative_map_conj]
    exact shiftedLegendre_derivative_square_integral n
  exact_mod_cast h

private def legendreSequence : Polynomial.Sequence ℂ where
  elems' := legendreC
  degree_eq' := degree_legendreC

private lemma legendreC_leadingCoeff_isUnit (n : ℕ) :
    IsUnit (legendreC n).leadingCoeff :=
  isUnit_iff_ne_zero.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (legendreSequence.ne_zero n))

private def expansion (d : ℕ) (a : ℕ → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range d, C (a k) * legendreC k

/-- All polynomials in degree < d are actually represented in the first d
members of this family, using the pinned polynomial-sequence spanning API. -/
private lemma exists_expansion (d : ℕ) (p : ℂ[X])
    (hp : p.degree < (d : WithBot ℕ)) :
    ∃ a : ℕ → ℂ, expansion d a = p := by
  have hs : p ∈ Submodule.span ℂ (legendreC '' (↑(Finset.range d) : Set ℕ)) := by
    change p ∈ Submodule.span ℂ
      (legendreSequence '' (↑(Finset.range d) : Set ℕ))
    rw [show (↑(Finset.range d) : Set ℕ) = Set.Iio d by ext k; simp]
    rw [legendreSequence.span_degreeLT (fun i _ => legendreC_leadingCoeff_isUnit i)]
    exact Polynomial.mem_degreeLT.mpr hp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℂ).mp hs
  exact ⟨a, by simpa only [expansion, Polynomial.smul_eq_C_mul] using ha⟩

private lemma moment_C_mul_right (a : ℂ) (p q : ℂ[X]) :
    moment p (C a * q) = a * moment p q := by
  rw [moment_comm, moment_C_mul_left, moment_comm q p]

private lemma moment_sum_left (s : Finset ℕ) (p : ℕ → ℂ[X]) (q : ℂ[X]) :
    moment (∑ i ∈ s, p i) q = ∑ i ∈ s, moment (p i) q := by
  unfold moment
  simp only [Polynomial.eval_finsetSum, Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum
    (fun i _ => ((eval_continuous (p i)).mul (eval_continuous q)).intervalIntegrable 0 1)

private lemma moment_sum_right (p : ℂ[X]) (s : Finset ℕ) (q : ℕ → ℂ[X]) :
    moment p (∑ i ∈ s, q i) = ∑ i ∈ s, moment p (q i) := by
  unfold moment
  simp only [Polynomial.eval_finsetSum, Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum
    (fun i _ => ((eval_continuous p).mul (eval_continuous (q i))).intervalIntegrable 0 1)

private lemma expansion_map_conj (d : ℕ) (a : ℕ → ℂ) :
    (expansion d a).map (starRingEnd ℂ) = expansion d (fun i => conj (a i)) := by
  simp only [expansion, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, legendreC_map_conj]

private lemma moment_expansion_row (d i : ℕ) (a : ℕ → ℂ)
    (hi : i ∈ Finset.range d) :
    moment (legendreC i) (expansion d (fun j => conj (a j))) =
      conj (a i) / (2 * (i : ℂ) + 1) := by
  unfold expansion
  rw [moment_sum_right, Finset.sum_eq_single i]
  · rw [moment_C_mul_right]
    change conj (a i) * (∫ x : ℝ in 0..1,
      (legendreC i).eval (x : ℂ) * (legendreC i).eval (x : ℂ)) = _
    rw [shiftedLegendre_square_integral]
    ring
  · intro j _ hji
    rw [moment_C_mul_right]
    have hz : moment (legendreC i) (legendreC j) = 0 :=
      shiftedLegendre_pairwise_moment_zero hji.symm
    rw [hz, mul_zero]
  · intro hnot
    exact (hnot hi).elim

private def weight (k : ℕ) : ℝ := 2 * (k : ℝ) + 1

private lemma weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity

private def coefficientEnergy (d : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range d, ‖a i‖ ^ 2 / weight i

private lemma coefficientEnergy_nonneg (d : ℕ) (a : ℕ → ℂ) :
    0 ≤ coefficientEnergy d a := by
  unfold coefficientEnergy
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (weight_pos i).le

/-- Exact integral Parseval identity for arbitrary complex coefficients. -/
private lemma expansion_parseval (d : ℕ) (a : ℕ → ℂ) :
    (∫ x : ℝ in 0..1, ‖(expansion d a).eval (x : ℂ)‖ ^ 2) =
      coefficientEnergy d a := by
  have h : ((∫ x : ℝ in 0..1,
      ‖(expansion d a).eval (x : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ Finset.range d, ((‖a i‖ ^ 2 : ℝ) : ℂ) / (2 * (i : ℂ) + 1) := by
    rw [norm_sq_integral_eq_moment, expansion_map_conj]
    change moment (∑ i ∈ Finset.range d, C (a i) * legendreC i)
      (expansion d (fun i => conj (a i))) = _
    rw [moment_sum_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [moment_C_mul_left, moment_expansion_row d i a hi]
    calc
      a i * (conj (a i) / (2 * (i : ℂ) + 1)) =
          (a i * conj (a i)) / (2 * (i : ℂ) + 1) := by ring
      _ = _ := by rw [Complex.mul_conj, Complex.sq_norm]
  have hcast : ((coefficientEnergy d a : ℝ) : ℂ) =
      ∑ i ∈ Finset.range d, ((‖a i‖ ^ 2 : ℝ) : ℂ) / (2 * (i : ℂ) + 1) := by
    change Complex.ofRealHom
      (∑ i ∈ Finset.range d, ‖a i‖ ^ 2 / weight i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.ofRealHom_eq_coe, weight, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_one, Complex.ofReal_natCast]
  exact Complex.ofReal_injective (h.trans hcast.symm)

private def derivativeDensity (d : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d,
    weight i * ‖(legendreC i).derivative.eval (x : ℂ)‖ ^ 2

private lemma derivativeDensity_continuous (d : ℕ) :
    Continuous (derivativeDensity d) := by
  unfold derivativeDensity
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul ((eval_continuous (legendreC i).derivative).norm.pow 2))

private lemma sum_derivative_budget (d : ℕ) :
    (∑ i ∈ Finset.range d,
      (2 * (i : ℝ) + 1) * (2 * (i : ℝ) * ((i : ℝ) + 1))) =
        (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma derivativeDensity_integral (d : ℕ) :
    (∫ x : ℝ in 0..1, derivativeDensity d x) =
      (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) := by
  calc
    (∫ x : ℝ in 0..1, derivativeDensity d x) =
        ∑ i ∈ Finset.range d, ∫ x : ℝ in 0..1,
          weight i * ‖(legendreC i).derivative.eval (x : ℂ)‖ ^ 2 := by
      unfold derivativeDensity
      exact intervalIntegral.integral_finsetSum (fun i _ =>
        (continuous_const.mul
          ((eval_continuous (legendreC i).derivative).norm.pow 2)).intervalIntegrable 0 1)
    _ = ∑ i ∈ Finset.range d,
        (2 * (i : ℝ) + 1) * (2 * (i : ℝ) * ((i : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_const_mul,
        shiftedLegendre_derivative_norm_sq_integral]
      rfl
    _ = _ := sum_derivative_budget d

private lemma expansion_derivative_eval (d : ℕ) (a : ℕ → ℂ) (x : ℝ) :
    (expansion d a).derivative.eval (x : ℂ) =
      ∑ i ∈ Finset.range d, a i * (legendreC i).derivative.eval (x : ℂ) := by
  simp only [expansion, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
    Polynomial.eval_finsetSum, eval_mul, eval_C]

/-- Weighted finite Cauchy--Schwarz. The weights are exactly the reciprocal
norms already proved above; no coefficient exponential is introduced. -/
private lemma expansion_derivative_pointwise (d : ℕ) (a : ℕ → ℂ) (x : ℝ) :
    ‖(expansion d a).derivative.eval (x : ℂ)‖ ^ 2 ≤
      coefficientEnergy d a * derivativeDensity d x := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.range d)
    (r := fun i => ‖a i * (legendreC i).derivative.eval (x : ℂ)‖)
    (f := fun i => ‖a i‖ ^ 2 / weight i)
    (g := fun i => weight i * ‖(legendreC i).derivative.eval (x : ℂ)‖ ^ 2)
    (fun i _ => div_nonneg (sq_nonneg _) (weight_pos i).le)
    (fun i _ => mul_nonneg (weight_pos i).le (sq_nonneg _))
    (fun i _ => by
      have heq : (‖a i‖ ^ 2 / weight i) *
          (weight i * ‖(legendreC i).derivative.eval (x : ℂ)‖ ^ 2) =
            ‖a i * (legendreC i).derivative.eval (x : ℂ)‖ ^ 2 := by
        rw [← mul_assoc, div_mul_cancel₀ _ (weight_pos i).ne', norm_mul, mul_pow]
      exact heq.symm.le)
  have hnorm :
      ‖∑ i ∈ Finset.range d, a i * (legendreC i).derivative.eval (x : ℂ)‖ ≤
        ∑ i ∈ Finset.range d, ‖a i * (legendreC i).derivative.eval (x : ℂ)‖ :=
    norm_sum_le _ _
  have hn : 0 ≤
      ‖∑ i ∈ Finset.range d, a i * (legendreC i).derivative.eval (x : ℂ)‖ :=
    norm_nonneg _
  have hs : 0 ≤ ∑ i ∈ Finset.range d,
      ‖a i * (legendreC i).derivative.eval (x : ℂ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    ‖(expansion d a).derivative.eval (x : ℂ)‖ ^ 2 =
        ‖∑ i ∈ Finset.range d, a i * (legendreC i).derivative.eval (x : ℂ)‖ ^ 2 := by
      rw [expansion_derivative_eval]
    _ ≤ (∑ i ∈ Finset.range d,
        ‖a i * (legendreC i).derivative.eval (x : ℂ)‖) ^ 2 :=
      (sq_le_sq₀ hn hs).mpr hnorm
    _ ≤ coefficientEnergy d a * derivativeDensity d x := hcs

private lemma expansion_derivative_integral_le (d : ℕ) (a : ℕ → ℂ) :
    (∫ x : ℝ in 0..1, ‖(expansion d a).derivative.eval (x : ℂ)‖ ^ 2) ≤
      (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖(expansion d a).eval (x : ℂ)‖ ^ 2) := by
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun x : ℝ => ‖(expansion d a).derivative.eval (x : ℂ)‖ ^ 2)
    (g := fun x : ℝ => coefficientEnergy d a * derivativeDensity d x)
    (by norm_num : (0 : ℝ) ≤ 1)
    (((eval_continuous (expansion d a).derivative).norm.pow 2).intervalIntegrable 0 1)
    ((continuous_const.mul (derivativeDensity_continuous d)).intervalIntegrable 0 1)
    (fun x _ => expansion_derivative_pointwise d a x)
  have hbudget : (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) ≤ (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    (∫ x : ℝ in 0..1, ‖(expansion d a).derivative.eval (x : ℂ)‖ ^ 2) ≤
        ∫ x : ℝ in 0..1, coefficientEnergy d a * derivativeDensity d x := hmono
    _ = coefficientEnergy d a * ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1)) := by
      rw [intervalIntegral.integral_const_mul, derivativeDensity_integral]
    _ ≤ (d : ℝ) ^ 4 * coefficientEnergy d a := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hbudget (coefficientEnergy_nonneg d a)
    _ = (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖(expansion d a).eval (x : ℂ)‖ ^ 2) := by
      rw [expansion_parseval]

/-- The complete polynomial L2 derivative inequality, stated with degree
so that d=0, p=0 is included as well. -/
theorem complex_polynomial_derivative_l2_of_degree (d : ℕ) (p : ℂ[X])
    (hp : p.degree < (d : WithBot ℕ)) :
    (∫ x : ℝ in 0..1, ‖p.derivative.eval (x : ℂ)‖ ^ 2) ≤
      (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖p.eval (x : ℂ)‖ ^ 2) := by
  obtain ⟨a, ha⟩ := exists_expansion d p hp
  simpa only [ha] using expansion_derivative_integral_le d a

/-- The exact requested d≥1, natDegree<d statement. Coefficients are
arbitrary complex numbers; no nonzero-polynomial assumption is made. -/
theorem complex_polynomial_derivative_l2 (d : ℕ) (_hd : 1 ≤ d) (p : ℂ[X])
    (hp : p.natDegree < d) :
    (∫ x : ℝ in 0..1, ‖p.derivative.eval (x : ℂ)‖ ^ 2) ≤
      (d : ℝ) ^ 4 * (∫ x : ℝ in 0..1, ‖p.eval (x : ℂ)‖ ^ 2) := by
  apply complex_polynomial_derivative_l2_of_degree d p
  exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hp)

end D5.S3.Analytic.PolynomialL2Derivative
