/- GID: D5/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual physical product Hermite integrals with all positive parameters and zero modes. -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0; see docs/reports/hermite-suppliers/tauceti-LICENSE.txt.
Adapted from TauCetiProject/TauCeti at f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd:
RingTheory/Polynomial/Hermite/Derivative.lean,
Analysis/SpecialFunctions/Hermite/Orthogonality.lean,
Analysis/SpecialFunctions/Hermite/Function/Orthonormal.lean.
Only the live lowering and weighted integration-by-parts constructions are used.
The physical rescalings and product-volume transport are proved for the displayed functions.
No research originality is claimed for the donor construction.
-/
import D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory MeasureTheory.Measure Polynomial Complex Filter WithLp
open scoped Topology ENNReal NNReal
open D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Analysis.Hermite.PhysicalProductOrthonormality

/-- The actual all-parameter physical product Hermites have Kronecker inner integrals. -/
theorem physical_product_orthonormal_integral (d : ℕ) (hbar : ℝ)
    (mass frequency : Fin d → ℝ) (hhbar : 0 < hbar)
    (hmass : ∀ j, 0 < mass j) (hfrequency : ∀ j, 0 < frequency j)
    (alpha beta : Fin d → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      physicalHermite d hbar mass frequency alpha x *
      physicalHermite d hbar mass frequency beta x) = if alpha = beta then 1 else 0 := by
  classical
  have poly_integrable (q : Polynomial ℝ) :
      Integrable (fun x : ℝ => q.eval x * Real.exp (-(x ^ 2 / 2))) := by
    have monomial (n : ℕ) : Integrable (fun x : ℝ => x ^ n * Real.exp (-(x ^ 2 / 2))) := by
      have hi := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
        (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
      simp only [Real.rpow_natCast] at hi
      convert hi using 1
      funext x
      congr 1
      ring
    have hs := integrable_finsetSum q.support (fun n _ => (monomial n).const_mul (q.coeff n))
    convert hs using 1 <;> try rfl
    funext x
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc]
  have ipoly (p : Polynomial ℤ) :
      Integrable (fun x : ℝ => aeval x p * Real.exp (-(x ^ 2 / 2))) := by
    convert poly_integrable (p.map (Int.castRingHom ℝ)) using 1
    simp only [Polynomial.eval_map, Polynomial.aeval_def]
    rfl
  have ipair (p q : Polynomial ℤ) :
      Integrable (fun x : ℝ => aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2))) := by
    convert ipoly (p * q) using 1
    simp only [map_mul]
  have lowering (n : ℕ) : derivative (Polynomial.hermite (n + 1)) =
      (n + 1) • Polynomial.hermite n := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          derivative (Polynomial.hermite (n + 1 + 1)) =
              derivative (Polynomial.X * Polynomial.hermite (n + 1) -
                derivative (Polynomial.hermite (n + 1))) := by rw [Polynomial.hermite_succ]
          _ = Polynomial.hermite (n + 1) + Polynomial.X * ((n + 1) • Polynomial.hermite n) -
                derivative ((n + 1) • Polynomial.hermite n) := by
                  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
                    Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_smul]
          _ = (n + 1 + 1) • Polynomial.hermite (n + 1) := by
                rw [Polynomial.hermite_succ n]
                simp only [Polynomial.derivative_smul]
                ring_nf
  have deriv_h (n : ℕ) : derivative (Polynomial.hermite n) =
      n • Polynomial.hermite (n - 1) := by
    cases n with
    | zero => simp [Polynomial.hermite_zero]
    | succ n => simpa using lowering n
  have iter_h (n k : ℕ) : derivative^[k] (Polynomial.hermite n) =
      n.descFactorial k • Polynomial.hermite (n - k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Polynomial.derivative_smul, deriv_h,
          smul_smul, Nat.descFactorial_succ, Nat.sub_sub, mul_comm]
  have pair_step (p : Polynomial ℤ) (n : ℕ) :
      (∫ x : ℝ, aeval x p * aeval x (Polynomial.hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))) =
      ∫ x : ℝ, aeval x (derivative p) * aeval x (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2)) := by
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => aeval x p * aeval x (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2)))
        (aeval x (derivative p) * aeval x (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2)) -
          aeval x p * aeval x (Polynomial.hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))) x := by
      intro x
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
        have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-(2 * x / 2)) x := (hsq.div_const 2).neg
        rwa [show -(2 * x / 2) = -x from by ring] at h2
      have hw' : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
          (Real.exp (-(x ^ 2 / 2)) * -x) x := h1.exp
      have hbase := ((p.hasDerivAt_aeval x).mul ((Polynomial.hermite n).hasDerivAt_aeval x)).mul hw'
      have hval : aeval x (derivative p) * aeval x (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2)) -
          aeval x p * aeval x (Polynomial.hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)) =
          (aeval x (derivative p) * aeval x (Polynomial.hermite n) +
            aeval x p * aeval x (derivative (Polynomial.hermite n))) * Real.exp (-(x ^ 2 / 2)) +
            aeval x p * aeval x (Polynomial.hermite n) * (Real.exp (-(x ^ 2 / 2)) * -x) := by
        rw [Polynomial.hermite_succ]
        simp only [map_sub, map_mul, Polynomial.aeval_X]
        ring
      rw [hval]
      exact hbase
    have ht1 := ipair (derivative p) (Polynomial.hermite n)
    have ht2 := ipair p (Polynomial.hermite (n + 1))
    have hf := ipair p (Polynomial.hermite n)
    have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (ht1.sub ht2) hf
    rw [integral_sub ht1 ht2] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have pair_iter (p : Polynomial ℤ) (n : ℕ) :
      (∫ x : ℝ, aeval x p * aeval x (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2))) =
      ∫ x : ℝ, aeval x (derivative^[n] p) * Real.exp (-(x ^ 2 / 2)) := by
    induction n generalizing p with
    | zero => simp only [Function.iterate_zero, id_eq, Polynomial.hermite_zero, map_one, mul_one]
    | succ n ih => rw [pair_step, ih (derivative p), Function.iterate_succ_apply]
  have gauss_half : (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) = Real.sqrt (2 * Real.pi) := by
    convert integral_gaussian (1 / 2) using 1 <;> congr 1 <;> ring
  have horth (m n : ℕ) :
      (∫ x : ℝ, aeval x (Polynomial.hermite m) * aeval x (Polynomial.hermite n) *
        Real.exp (-(x ^ 2 / 2))) = if m = n then (n.factorial : ℝ) * Real.sqrt (2 * Real.pi) else 0 := by
    have hswap (m n : ℕ) :
        (∫ x : ℝ, aeval x (Polynomial.hermite m) * aeval x (Polynomial.hermite n) *
          Real.exp (-(x ^ 2 / 2))) =
        ∫ x : ℝ, aeval x (Polynomial.hermite n) * aeval x (Polynomial.hermite m) *
          Real.exp (-(x ^ 2 / 2)) := by congr 1; funext x; ring
    rcases lt_trichotomy m n with h | rfl | h
    · rw [if_neg h.ne, pair_iter, iter_h, Nat.descFactorial_eq_zero_iff_lt.mpr h]
      simp
    · rw [if_pos rfl, pair_iter]
      have hc : (fun x : ℝ => aeval x (derivative^[m] (Polynomial.hermite m)) *
          Real.exp (-(x ^ 2 / 2))) = fun x : ℝ => (m.factorial : ℝ) * Real.exp (-(x ^ 2 / 2)) := by
        funext x
        rw [iter_h, Nat.sub_self, Nat.descFactorial_self, Polynomial.hermite_zero]
        simp [nsmul_eq_mul]
      rw [hc, integral_const_mul, gauss_half]
    · rw [if_neg h.ne', hswap, pair_iter, iter_h, Nat.descFactorial_eq_zero_iff_lt.mpr h]
      simp
  let psi : ℕ → ℝ → ℝ := fun n x =>
    aeval (x * Real.sqrt 2) (Polynomial.hermite n) * Real.exp (-(x ^ 2 / 2)) /
      Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
  have hpsi (m n : ℕ) : (∫ x : ℝ, psi m x * psi n x) = if m = n then 1 else 0 := by
    have henv (x : ℝ) : Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) =
        Real.exp (-((x * Real.sqrt 2) ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hp (x : ℝ) : psi m x * psi n x =
        (aeval (x * Real.sqrt 2) (Polynomial.hermite m) *
          aeval (x * Real.sqrt 2) (Polynomial.hermite n) * Real.exp (-((x * Real.sqrt 2) ^ 2 / 2))) /
          (Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) *
            Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)) := by
      dsimp only [psi]
      rw [← henv]
      ring
    simp only [hp]
    rw [integral_div]
    rw [Measure.integral_comp_mul_right
      (fun u : ℝ => aeval u (Polynomial.hermite m) * aeval u (Polynomial.hermite n) *
        Real.exp (-(u ^ 2 / 2))) (Real.sqrt 2), horth, smul_eq_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2))]
    split_ifs with h
    · rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi,
        Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ) * Real.sqrt Real.pi)]
      have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have hpi : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
      field_simp
    · simp
  let ell : Fin d → ℝ := fun j => Real.sqrt (hbar / (mass j * frequency j))
  have hell (j : Fin d) : 0 < ell j := Real.sqrt_pos.2 (div_pos hhbar (mul_pos (hmass j) (hfrequency j)))
  let test : Fin d → ℕ → ℝ → ℝ := fun j n x => psi n (x / ell j) / Real.sqrt (ell j)
  have htest (j : Fin d) (m n : ℕ) : (∫ x : ℝ, test j m x * test j n x) = if m = n then 1 else 0 := by
    have hp (x : ℝ) : test j m x * test j n x = (psi m (x * (ell j)⁻¹) * psi n (x * (ell j)⁻¹)) / ell j := by
      dsimp only [test]
      rw [← mul_div_mul_comm, Real.mul_self_sqrt (hell j).le]
      simp only [div_eq_mul_inv]
    simp only [hp]
    rw [integral_div, Measure.integral_comp_mul_right (fun x : ℝ => psi m x * psi n x) ((ell j)⁻¹),
      inv_inv, abs_of_pos (hell j), smul_eq_mul, hpsi]
    split_ifs <;> simp [div_self (hell j).ne']
  have heq (a : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      physicalHermite d hbar mass frequency a x = ∏ j, ((test j (a j) (x j) : ℝ) : ℂ) := by
    unfold physicalHermite
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [test, psi, ell]
    congr 1
    have hp : Real.sqrt 2 * x j / Real.sqrt (hbar / (mass j * frequency j)) =
        (x j / Real.sqrt (hbar / (mass j * frequency j))) * Real.sqrt 2 := by ring
    rw [hp]
    simp only [div_div, neg_div]
    congr 1
    ring
  have hcov :
      (∫ x : Fin d → ℝ, physicalHermite d hbar mass frequency alpha (toLp 2 x) *
        physicalHermite d hbar mass frequency beta (toLp 2 x)) =
      ∫ x : EuclideanSpace ℝ (Fin d), physicalHermite d hbar mass frequency alpha x *
        physicalHermite d hbar mass frequency beta x := by
    convert (PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
      (fun x => physicalHermite d hbar mass frequency alpha x *
        physicalHermite d hbar mass frequency beta x) using 1
  rw [← hcov]
  simp only [heq, ← Finset.prod_mul_distrib, ← Complex.ofReal_mul]
  have hfub := integral_fintype_prod_eq_prod (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun j (x : ℝ) => ((test j (alpha j) x * test j (beta j) x : ℝ) : ℂ))
  have hfub' : (∫ x : Fin d → ℝ, ∏ j, ((test j (alpha j) (x j) * test j (beta j) (x j) : ℝ) : ℂ)) =
      ∏ j, ∫ x : ℝ, ((test j (alpha j) x * test j (beta j) x : ℝ) : ℂ) := by
    simpa only [volume_pi] using hfub
  rw [hfub']
  have hcast (j : Fin d) : (∫ x : ℝ, ((test j (alpha j) x * test j (beta j) x : ℝ) : ℂ)) =
      ((∫ x : ℝ, test j (alpha j) x * test j (beta j) x : ℝ) : ℂ) := by
    convert (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => test j (alpha j) x * test j (beta j) x)) using 1 <;> rfl
  simp only [hcast, htest, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  by_cases h : alpha = beta
  · subst beta
    simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, alpha j ≠ beta j := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
end D5.S3.Quantum.Analysis.Hermite.PhysicalProductOrthonormality
