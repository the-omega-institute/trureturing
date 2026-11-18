/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianEntireEvaluation
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianEntireEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire summability and evaluation of native Gaussian coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
The finite coefficient one-norm argument adapts the consumed polynomial
one-norm proof in UniformCoefficientBudget to complex multivariate polynomials.
That proof is adapted from Causalean, Copyright 2026 Jiyuan Tan, Apache-2.0,
https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/
Causalean/Mathlib/Analysis/Approximation/Chebyshev/PolynomialOneNorm.lean.
License and notice: docs/reports/interpolation-suppliers/Causalean-LICENSE.txt
and Causalean-NOTICE.txt. The adaptation uses finite multivariate supports,
complex norms and the native homogeneous Gaussian pieces.

No symmetry, positivity or norm bound is required of the finite complex
matrix. Evaluation uses ordinary bilinear quadratic coefficients, without
conjugation. This supplies an outer auxiliary Gaussian sum; affine factorial
Fock bounds, joint sewing summability and source identities remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation

open MvPolynomial FactorialFockQuadraticEstimate

universe u
variable {I : Type u}
local notation "P" => MvPolynomial I ℂ

private def coeffL1 (p : P) : ℝ := ∑ d ∈ p.support, ‖p.coeff d‖

private theorem coeff_summable (p : P) : Summable (fun d => ‖p.coeff d‖) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro d hd
  simp [notMem_support_iff.mp hd]

private theorem coeffL1_eq_tsum (p : P) :
    coeffL1 p = ∑' d, ‖p.coeff d‖ := by
  symm
  apply tsum_eq_sum
  intro d hd
  simp [notMem_support_iff.mp hd]

private theorem coeffL1_nonneg (p : P) : 0 ≤ coeffL1 p := by
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

private theorem coeffL1_add_le (p q : P) :
    coeffL1 (p + q) ≤ coeffL1 p + coeffL1 q := by
  simp_rw [coeffL1_eq_tsum]
  rw [← (coeff_summable p).tsum_add (coeff_summable q)]
  exact (coeff_summable (p + q)).tsum_le_tsum
    (fun d => by simpa using norm_add_le (p.coeff d) (q.coeff d))
    ((coeff_summable p).add (coeff_summable q))

private theorem coeffL1_sum_le {α : Type*} (s : Finset α) (f : α → P) :
    coeffL1 (∑ a ∈ s, f a) ≤ ∑ a ∈ s, coeffL1 (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (coeffL1_add_le _ _).trans (add_le_add le_rfl ih)

private theorem coeffL1_monomial (d : I →₀ ℕ) (c : ℂ) :
    coeffL1 (monomial d c) = ‖c‖ := by
  classical
  by_cases hc : c = 0
  · simp [hc, coeffL1]
  · simp [coeffL1, support_monomial, hc]

private theorem coeffL1_smul (c : ℂ) (p : P) :
    coeffL1 (c • p) = ‖c‖ * coeffL1 p := by
  simp_rw [coeffL1_eq_tsum, coeff_smul, smul_eq_mul, norm_mul]
  exact tsum_mul_left

private theorem coeffL1_mul_le (p q : P) :
    coeffL1 (p * q) ≤ coeffL1 p * coeffL1 q := by
  classical
  rw [MvPolynomial.mul_def]
  simp_rw [MvPolynomial.sum_def]
  calc
    _ ≤ ∑ a ∈ p.support, coeffL1
        (∑ b ∈ q.support, monomial (a + b) (p.coeff a * q.coeff b)) :=
      coeffL1_sum_le _ _
    _ ≤ ∑ a ∈ p.support, ∑ b ∈ q.support,
        coeffL1 (monomial (a + b) (p.coeff a * q.coeff b)) :=
      Finset.sum_le_sum (fun _ _ => coeffL1_sum_le _ _)
    _ = _ := by
      simp only [coeffL1_monomial, norm_mul]
      change (∑ a ∈ p.support, ∑ b ∈ q.support, ‖p.coeff a‖ * ‖q.coeff b‖) = _
      simp only [coeffL1, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

private theorem coeffL1_pow_le (p : P) (n : ℕ) :
    coeffL1 (p ^ n) ≤ coeffL1 p ^ n := by
  induction n with
  | zero => simp [coeffL1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coeffL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (coeffL1_nonneg p))

variable [Fintype I]

private theorem quadratic_coeffL1_le (E : Matrix I I ℂ) :
    coeffL1 (quadratic E) ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, ‖E i j‖ := by
  have hx (i : I) : coeffL1 (X i : P) = 1 := by
    simpa [MvPolynomial.X] using coeffL1_monomial (Finsupp.single i 1) (1 : ℂ)
  have hterm (i j : I) : coeffL1 (E i j • (X i * X j)) ≤ ‖E i j‖ := by
    rw [coeffL1_smul]
    simpa only [hx, mul_one] using
      mul_le_mul_of_nonneg_left (coeffL1_mul_le (X i : P) (X j)) (norm_nonneg (E i j))
  unfold quadratic
  rw [coeffL1_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (coeffL1_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (coeffL1_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))

private theorem piece_coeffL1_le (E : Matrix I I ℂ) (n : ℕ) :
    coeffL1 (gaussianPiece E n) ≤
      ((1 / 2 : ℝ) * ∑ i, ∑ j, ‖E i j‖) ^ n / n.factorial := by
  rw [gaussianPiece, coeffL1_smul, norm_inv, Complex.norm_natCast]
  rw [div_eq_mul_inv, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (coeffL1_pow_le _ _).trans
    (pow_le_pow_left₀ (coeffL1_nonneg _) (quadratic_coeffL1_le E) n)

private theorem piece_coeff_vanish (E : Matrix I I ℂ) (d : I →₀ ℕ) (n : ℕ)
    (hn : n ≠ d.degree / 2) : (gaussianPiece E n).coeff d = 0 := by
  classical
  apply (gaussianPiece_homogeneous E n).coeff_eq_zero
  omega

private theorem piece_sum (E : Matrix I I ℂ) (d : I →₀ ℕ) (N : ℕ)
    (hN : d.degree / 2 < N) :
    (∑ n ∈ Finset.range N, (gaussianPiece E n).coeff d) = gaussianCoefficient E d := by
  classical
  apply Finset.sum_eq_single (d.degree / 2)
  · intro n hn hne
    exact piece_coeff_vanish E d n hne
  · intro h
    exact (h (Finset.mem_range.mpr hN)).elim

private theorem finite_subsum_le (E : Matrix I I ℂ) (S : Finset (I →₀ ℕ)) :
    (∑ d ∈ S, ‖gaussianCoefficient E d‖) ≤
      Real.exp ((1 / 2 : ℝ) * ∑ i, ∑ j, ‖E i j‖) := by
  classical
  let N := S.sup (fun d => d.degree / 2) + 1
  have hN (d : I →₀ ℕ) (hd : d ∈ S) : d.degree / 2 < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun d => d.degree / 2) hd)
  calc
    _ ≤ ∑ d ∈ S, ∑ n ∈ Finset.range N, ‖(gaussianPiece E n).coeff d‖ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← piece_sum E d N (hN d hd)]
      exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ∑ d ∈ S, ‖(gaussianPiece E n).coeff d‖ :=
      Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.range N, coeffL1 (gaussianPiece E n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [coeffL1_eq_tsum]
      exact (coeff_summable _).sum_le_tsum S (fun d _ => norm_nonneg _)
    _ ≤ ∑ n ∈ Finset.range N,
        ((1 / 2 : ℝ) * ∑ i, ∑ j, ‖E i j‖) ^ n / n.factorial :=
      Finset.sum_le_sum (fun n _ => piece_coeffL1_le E n)
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by positivity) N

/-- Every native occupation coefficient is absolutely summable for an arbitrary
finite complex matrix, including an empty mode type. -/
theorem gaussianCoefficient_norm_summable (E : Matrix I I ℂ) :
    Summable (fun d => ‖gaussianCoefficient E d‖) := by
  exact summable_of_sum_le (fun d => norm_nonneg _) (finite_subsum_le E)

private theorem piece_tsum (E : Matrix I I ℂ) (d : I →₀ ℕ) :
    (∑' n, (gaussianPiece E n).coeff d) = gaussianCoefficient E d := by
  exact tsum_eq_single (d.degree / 2) (fun n hn => piece_coeff_vanish E d n hn)

private theorem piece_norm_tsum (E : Matrix I I ℂ) (d : I →₀ ℕ) :
    (∑' n, ‖(gaussianPiece E n).coeff d‖) = ‖gaussianCoefficient E d‖ := by
  exact tsum_eq_single (d.degree / 2) (fun n hn => by
    rw [piece_coeff_vanish E d n hn, norm_zero])

private theorem pieces_norm_summable (E : Matrix I I ℂ) :
    Summable (fun nd : ℕ × (I →₀ ℕ) => ‖(gaussianPiece E nd.1).coeff nd.2‖) := by
  classical
  suffices h : Summable (fun dn : (I →₀ ℕ) × ℕ =>
      ‖(gaussianPiece E dn.2).coeff dn.1‖) from h.prod_symm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro d
    apply summable_of_ne_finset_zero (s := {d.degree / 2})
    intro n hn
    rw [piece_coeff_vanish E d n (by simpa using hn), norm_zero]
  · simpa only [piece_norm_tsum] using gaussianCoefficient_norm_summable E

omit [Fintype I] in
private theorem polynomial_tsum_eval (p : P) :
    (∑' d, p.coeff d) = eval (fun _ => 1) p := by
  classical
  rw [tsum_eq_sum (s := p.support) (fun d hd => notMem_support_iff.mp hd), eval_eq]
  simp

private theorem piece_eval (E : Matrix I I ℂ) (n : ℕ) :
    eval (fun _ => 1) (gaussianPiece E n) =
      ((1 / 2 : ℂ) * ∑ i, ∑ j, E i j) ^ n / n.factorial := by
  simp only [gaussianPiece, quadratic, smul_eq_C_mul, map_mul, map_pow, eval_C,
    map_sum, eval_X, mul_one]
  simp only [div_eq_mul_inv]
  ring

set_option maxHeartbeats 1000000 in
-- Elaborate the nested occupation/degree sums with the native polynomial coefficients.
/-- The unrestricted sum of the actual native Gaussian coefficients evaluates
to exp(Q_E(1)); the transpose convention remains ordinary bilinear. -/
theorem gaussianCoefficient_tsum (E : Matrix I I ℂ) :
    (∑' d, gaussianCoefficient E d) =
      Complex.exp ((1 / 2 : ℂ) * ∑ i, ∑ j, E i j) := by
  have hjoint : Summable (fun nd : ℕ × (I →₀ ℕ) =>
      (gaussianPiece E nd.1).coeff nd.2) := (pieces_norm_summable E).of_norm
  calc
    _ = ∑' d, ∑' n, (gaussianPiece E n).coeff d :=
      tsum_congr (fun d => (piece_tsum E d).symm)
    _ = ∑' n, ∑' d, (gaussianPiece E n).coeff d := hjoint.tsum_comm
    _ = ∑' n, ((1 / 2 : ℂ) * ∑ i, ∑ j, E i j) ^ n / n.factorial := by
      simp_rw [polynomial_tsum_eval, piece_eval]
    _ = _ := by
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

end D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
