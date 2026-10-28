/- GID: D5/S3/Observer/Linear/HilbertMomentCoercivity
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/HilbertMomentCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.GramMatrix, mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: The concrete Hilbert moment matrix controls Hilbert-valued Taylor polynomials without a finite ambient dimension. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.HilbertMomentCoercivity

open MeasureTheory Finset Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

/-- The moment matrix of the monomials on the unit interval. -/
def hilbertMoment (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => 1 / ((i : ℕ) + (j : ℕ) + 1 : ℕ)

private theorem hilbertMoment_hermitian (N : ℕ) : (hilbertMoment N).IsHermitian := by
  ext i j
  simp [hilbertMoment, Nat.add_comm]

/-- The minimum of all eigenvalues of the moment matrix. -/
def hilbertEigenvalue (N : ℕ) : ℝ :=
  univ.inf' univ_nonempty (hilbertMoment_hermitian N).eigenvalues

private theorem polynomial_energy_eq {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (N : ℕ) (v : Fin (N + 1) → W) :
    (∫ s in (0 : ℝ)..1, ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • v i‖ ^ 2) =
      ∑ i, ∑ j, hilbertMoment N i j * (inner ℝ (v i) (v j)) := by
  have hp (s : ℝ) : ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • v i‖ ^ 2 =
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), s ^ ((i : ℕ) + (j : ℕ)) * (inner ℝ (v i) (v j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [pow_add, real_inner_comm (v j) (v i)]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun (i : Fin (N + 1)) _ =>
    (by fun_prop : Continuous (fun s : ℝ =>
      ∑ j : Fin (N + 1), s ^ ((i : ℕ) + (j : ℕ)) * (inner ℝ (v i) (v j)))).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun (j : Fin (N + 1)) _ =>
    (by fun_prop : Continuous (fun s : ℝ =>
      s ^ ((i : ℕ) + (j : ℕ)) * (inner ℝ (v i) (v j)))).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp [hilbertMoment, Nat.cast_add]

/-- Every finite Hilbert moment matrix is strictly positive definite. -/
theorem hilbertMoment_posDef (N : ℕ) : (hilbertMoment N).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hilbertMoment_hermitian N)
  intro x hx
  have he : x ⬝ᵥ (hilbertMoment N *ᵥ x) =
      ∫ s in (0 : ℝ)..1, ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • x i‖ ^ 2 := by
    rw [polynomial_energy_eq]
    simp only [dotProduct, mulVec, RCLike.inner_apply, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [starRingEnd_apply, star_trivial]
    ring
  simp only [star_trivial]
  rw [he]
  let p : Polynomial ℝ := ∑ i : Fin (N + 1), Polynomial.monomial (i : ℕ) (x i)
  have hp (s : ℝ) : p.eval s = ∑ i : Fin (N + 1), s ^ (i : ℕ) • x i := by
    simp [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial, smul_eq_mul, mul_comm]
  have hcont : Continuous (fun s : ℝ =>
      ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • x i‖ ^ 2) := by fun_prop
  have hn : 0 ≤ ∫ s in (0 : ℝ)..1,
      ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • x i‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)
  by_contra! hzero
  have hz : (∫ s in (0 : ℝ)..1,
      ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • x i‖ ^ 2) = 0 := le_antisymm hzero hn
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun s : ℝ =>
      sq_nonneg ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • x i‖))
    (hcont.intervalIntegrable _ _)).mp hz
  have hon := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
    hcont.continuousOn continuous_zero.continuousOn
  have hpzero : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioc_infinite (by norm_num : (0 : ℝ) < 1)).mono
    intro s hs
    change p.eval s = 0
    rw [hp]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hon hs))
  apply hx
  funext i
  have hi := congrArg (fun q : Polynomial ℝ => q.coeff (i : ℕ)) hpzero
  simpa only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_eq_val, sum_ite_eq', mem_univ, ite_true, Polynomial.coeff_zero, Pi.zero_apply] using hi

private theorem hilbertEigenvalue_pos (N : ℕ) : 0 < hilbertEigenvalue N := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i _
  exact (hilbertMoment_posDef N).eigenvalues_pos i

private theorem hilbertMoment_floor (N : ℕ) :
    (hilbertMoment N - algebraMap ℝ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
      (hilbertEigenvalue N)).PosSemidef := by
  apply Matrix.le_iff.mp
  apply (algebraMap_le_iff_le_spectrum (hilbertMoment_hermitian N)).mpr
  intro z hz
  obtain ⟨i, rfl⟩ := (hilbertMoment_hermitian N).spectrum_real_eq_range_eigenvalues ▸ hz
  exact inf'_le _ (mem_univ i)

/-- The least Hilbert-matrix eigenvalue gives the same coefficient-energy
floor in every real Hilbert output space. -/
theorem hilbert_polynomial_coercivity {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (N : ℕ) (v : Fin (N + 1) → W) :
    0 < hilbertEigenvalue N ∧
    hilbertEigenvalue N * (∑ i, ‖v i‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..1, ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • v i‖ ^ 2 := by
  classical
  refine ⟨hilbertEigenvalue_pos N, ?_⟩
  rw [polynomial_energy_eq]
  have hh := ((hilbertMoment_floor N).hadamard (Matrix.posSemidef_gram ℝ v)).dotProduct_mulVec_nonneg (fun _ => 1)
  have hd : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      (algebraMap ℝ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
        (hilbertEigenvalue N)) i j * inner ℝ (v i) (v j)) =
      hilbertEigenvalue N * (∑ i, ‖v i‖ ^ 2) := by
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, real_inner_self_eq_norm_sq,
      mul_sum, Algebra.algebraMap_self]
  simp only [star_trivial, dotProduct, mulVec, Pi.one_apply, one_mul, mul_one,
    hadamard_apply, Matrix.sub_apply, gram_apply] at hh
  simp_rw [sub_mul, sum_sub_distrib] at hh
  rw [hd] at hh
  linarith

/-- Factorial Taylor coefficients have the explicit short-window floor in
arbitrary real or complex Hilbert output spaces. -/
theorem taylor_polynomial_energy_floor {𝕜 W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (N : ℕ) (v : Fin (N + 1) → W) (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) :
    hilbertEigenvalue N * T ^ (2 * N + 1) / (N.factorial : ℝ) ^ 2 *
        (∑ i, ‖v i‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T,
        ‖∑ i : Fin (N + 1),
          (((t ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) : ℝ) : 𝕜) • v i‖ ^ 2 := by
  letI : InnerProductSpace ℝ W := InnerProductSpace.rclikeToReal 𝕜 W
  let w : Fin (N + 1) → W := fun i =>
    (T ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) • v i
  have hw (s : ℝ) :
      (∑ i : Fin (N + 1),
        ((((T * s) ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) : ℝ) : 𝕜) • v i) =
      ∑ i : Fin (N + 1), s ^ (i : ℕ) • w i := by
    apply sum_congr rfl
    intro i _
    change ((T * s) ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) • v i =
      s ^ (i : ℕ) • ((T ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) • v i)
    rw [smul_smul, mul_pow]
    congr 1
    ring
  have hcoef (i : Fin (N + 1)) : T ^ N / (N.factorial : ℝ) ≤
      T ^ (i : ℕ) / ((i : ℕ).factorial : ℝ) := by
    have hi : (i : ℕ) ≤ N := by omega
    have hfac : ((i : ℕ).factorial : ℝ) ≤ (N.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le hi)
    calc
      _ ≤ T ^ N / ((i : ℕ).factorial : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg hT.le _) (by positivity) hfac
      _ ≤ _ := div_le_div_of_nonneg_right
        (pow_le_pow_of_le_one hT.le hT1 hi) (by positivity)
  have hsum : (T ^ N / (N.factorial : ℝ)) ^ 2 * (∑ i, ‖v i‖ ^ 2) ≤
      ∑ i, ‖w i‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have hn : T ^ N / (N.factorial : ℝ) * ‖v i‖ ≤ ‖w i‖ := by
      calc
        _ ≤ (T ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) * ‖v i‖ := by
          exact mul_le_mul_of_nonneg_right (hcoef i) (norm_nonneg _)
        _ = _ := by
          dsimp [w]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [← pow_two, mul_pow] using
      (mul_self_le_mul_self (by positivity :
        0 ≤ T ^ N / (N.factorial : ℝ) * ‖v i‖) hn)
  have hb := (hilbert_polynomial_coercivity N w).2
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => ‖∑ i : Fin (N + 1),
      (((t ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) : ℝ) : 𝕜) • v i‖ ^ 2)
    T (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul, hw] at hchange
  rw [← hchange]
  have hpow : T ^ (2 * N + 1) = T * (T ^ N) ^ 2 := by
    rw [pow_succ, show 2 * N = N * 2 by omega, pow_mul]
    ring
  calc
    _ = T * (hilbertEigenvalue N *
        ((T ^ N / (N.factorial : ℝ)) ^ 2 * ∑ i, ‖v i‖ ^ 2)) := by rw [hpow]; ring
    _ ≤ T * (hilbertEigenvalue N * ∑ i, ‖w i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (hilbertEigenvalue_pos N).le) hT.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hT.le

end D5.S3.Observer.Linear.HilbertMomentCoercivity
