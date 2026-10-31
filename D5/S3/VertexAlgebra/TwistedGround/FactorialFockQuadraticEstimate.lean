/- GID: D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-degree Gaussian bounds in the factorial Fock metric. -/

import D5.S3.VertexAlgebra.FactorialFockMetric
import D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
The positive form is the existing factorial Fock form. A finite complex
symmetric matrix is controlled by its Euclidean operator norm. The CCR and
Euler identity give the creation recurrence in every degree, and the scalar
majorant gives summability. No Gaussian norm formula is a premise.

These estimates concern finite-mode polynomial Gaussian coefficients. Their
identification with an actual Corr/Wick source, transport to infinitely many
modes, and physical realization require separate theorems.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

open MvPolynomial
open FactorialFockMetric (weight)

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

local notation "P" => MvPolynomial I ℂ

/-- The squared norm of the EXISTING injective factorial Hilbert embedding. -/
def mass (p : P) : ℝ := (FactorialFockMetric.inner p p).re

private theorem mass_nonneg (p : P) : 0 ≤ mass p := by
  change 0 ≤ (Inner.inner ℂ (FactorialFockMetric.embedding I p)
    (FactorialFockMetric.embedding I p)).re
  exact inner_self_nonneg (𝕜 := ℂ)

private theorem inner_sum_left (f : I → P) (p : P) :
    FactorialFockMetric.inner (∑ i, f i) p =
      ∑ i, FactorialFockMetric.inner (f i) p := by
  simp only [FactorialFockMetric.inner, map_sum, sum_inner]

private theorem inner_sum_right (p : P) (f : I → P) :
    FactorialFockMetric.inner p (∑ i, f i) =
      ∑ i, FactorialFockMetric.inner p (f i) := by
  simp only [FactorialFockMetric.inner, map_sum, inner_sum]

private theorem inner_smul_first (c : ℂ) (p q : P) :
    FactorialFockMetric.inner (c • p) q = conj c * FactorialFockMetric.inner p q := by
  simp only [FactorialFockMetric.inner, map_smul, inner_smul_left]

private theorem inner_smul_second (c : ℂ) (p q : P) :
    FactorialFockMetric.inner p (c • q) = c * FactorialFockMetric.inner p q := by
  simp only [FactorialFockMetric.inner, map_smul, inner_smul_right]

private theorem inner_add_second (p q r : P) :
    FactorialFockMetric.inner p (q + r) =
      FactorialFockMetric.inner p q + FactorialFockMetric.inner p r := by
  simp only [FactorialFockMetric.inner, map_add, inner_add_right]

private theorem conjugate_inner (p q : P) :
    conj (FactorialFockMetric.inner p q) = FactorialFockMetric.inner q p := by
  exact inner_conj_symm _ _

private theorem re_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reCLM f s

private theorem inner_nsmul_first (n : ℕ) (p q : P) :
    FactorialFockMetric.inner (n • p) q = (n : ℂ) * FactorialFockMetric.inner p q := by
  induction n with
  | zero => simp [FactorialFockMetric.inner]
  | succ n ih =>
    rw [succ_nsmul, FactorialFockMetric.inner_add_first, ih]
    push_cast
    ring

/-- Finite coefficient computation of the actual factorial squared norm. -/
theorem mass_eq_sum (p : P) :
    mass p = ∑ d ∈ p.support, (weight d : ℝ) * ‖p.coeff d‖ ^ 2 := by
  classical
  have he : FactorialFockMetric.inner p p =
      ∑ d ∈ p.support, (weight d : ℂ) * conj (p.coeff d) * p.coeff d := by
    calc
      _ = FactorialFockMetric.inner
          (∑ d ∈ p.support, monomial d (p.coeff d)) p := by rw [← p.as_sum]
      _ = _ := by
        simp only [FactorialFockMetric.inner, map_sum, sum_inner]
        apply Finset.sum_congr rfl
        intro d hd
        exact FactorialFockMetric.inner_monomial_left d _ p
  unfold mass
  rw [he, re_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc, RCLike.conj_mul, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  congr 1
  exact RCLike.re_ofReal_pow (K := ℂ) ‖p.coeff d‖ 2

private theorem mass_sum_on (p : P) (s : Finset (I →₀ ℕ)) (hs : p.support ⊆ s) :
    mass p = ∑ d ∈ s, (weight d : ℝ) * ‖p.coeff d‖ ^ 2 := by
  classical
  rw [mass_eq_sum]
  apply Finset.sum_subset hs
  intro d hd hdp
  simp [MvPolynomial.notMem_support_iff.mp hdp]

private theorem finite_coeff_mass_le (p : P) (s : Finset (I →₀ ℕ)) :
    (∑ d ∈ s, (weight d : ℝ) * ‖p.coeff d‖ ^ 2) ≤ mass p := by
  classical
  rw [mass_sum_on p (s ∪ p.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun d _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Scalar operator norm control in the exact coefficient convention used below. -/
private theorem scalar_matrix_bound (A : Matrix I I ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (x : I → ℂ) :
    (∑ i, ‖∑ j, A i j * x j‖ ^ 2) ≤ q ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  let v : EuclideanSpace ℂ I := WithLp.toLp 2 x
  have hb : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ ≤ q * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg v))).2 hb
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  exact hs

private theorem conjugate_scalar_matrix_bound (A : Matrix I I ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (x : I → ℂ) :
    (∑ i, ‖∑ j, conj (A i j) * x j‖ ^ 2) ≤ q ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have hb := scalar_matrix_bound A hq hA (fun j => conj (x j))
  have he (i : I) : (∑ j, conj (A i j) * x j) =
      conj (∑ j, A i j * conj (x j)) := by simp
  simpa only [he, Complex.norm_conj] using hb

/-- Coefficientwise proof of tensor amplification. The scalar operator bound
is applied at EACH occupation, then summed with the genuine factorial weight. -/
private theorem polynomial_matrix_bound (B : Matrix I I ℂ) {r : ℝ}
    (hB : ∀ x : I → ℂ,
      (∑ i, ‖∑ j, B i j * x j‖ ^ 2) ≤ r * ∑ j, ‖x j‖ ^ 2)
    (p : I → P) :
    (∑ i, mass (∑ j, B i j • p j)) ≤ r * ∑ j, mass (p j) := by
  classical
  let s : Finset (I →₀ ℕ) := Finset.univ.biUnion (fun j => (p j).support)
  have hp (j : I) : (p j).support ⊆ s := by
    intro d hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hd⟩
  have hrow (i : I) : (∑ j, B i j • p j).support ⊆ s := by
    intro d hd
    by_contra hn
    have hz (j : I) : (p j).coeff d = 0 :=
      MvPolynomial.notMem_support_iff.mp (fun hm => hn (hp j hm))
    have hc : (∑ j, B i j • p j).coeff d = 0 := by
      simp only [coeff_sum, coeff_smul, smul_eq_mul, hz, mul_zero, Finset.sum_const_zero]
    exact (MvPolynomial.mem_support_iff.mp hd) hc
  have hmrow (i : I) : mass (∑ j, B i j • p j) =
      ∑ d ∈ s, (weight d : ℝ) * ‖∑ j, B i j * (p j).coeff d‖ ^ 2 := by
    rw [mass_sum_on _ s (hrow i)]
    simp only [coeff_sum, coeff_smul, smul_eq_mul]
  have hmp (j : I) : mass (p j) =
      ∑ d ∈ s, (weight d : ℝ) * ‖(p j).coeff d‖ ^ 2 := mass_sum_on _ s (hp j)
  simp_rw [hmrow, hmp]
  rw [Finset.sum_comm]
  calc
    _ = ∑ d ∈ s, (weight d : ℝ) * (∑ i, ‖∑ j, B i j * (p j).coeff d‖ ^ 2) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ d ∈ s, (weight d : ℝ) * (r * ∑ j, ‖(p j).coeff d‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hB (fun j => (p j).coeff d)) (Nat.cast_nonneg _)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro d hd
      ring

private theorem derivative_creation_right (j : I) (p q : P) :
    FactorialFockMetric.inner p (X j * q) =
      FactorialFockMetric.inner (pderiv j p) q := by
  have h := congrArg conj (FactorialFockMetric.mul_X_pderiv_pairing j q p)
  simpa only [conjugate_inner] using h

private theorem creation_pairing (j k : I) (p : P) :
    FactorialFockMetric.inner (X j * p) (X k * p) =
      (if j = k then FactorialFockMetric.inner p p else 0) +
        FactorialFockMetric.inner (pderiv k p) (pderiv j p) := by
  classical
  rw [FactorialFockMetric.mul_X_pderiv_pairing, pderiv_mul]
  rw [inner_add_second]
  rw [derivative_creation_right]
  by_cases h : j = k
  · subst k
    rw [pderiv_X_self, one_mul, if_pos rfl]
  · rw [pderiv_X_of_ne (Ne.symm h), zero_mul, if_neg h]
    simp only [FactorialFockMetric.inner, map_zero, inner_zero_right, zero_add]

/-- The exact CCR identity, with conjugation in the second derivative vector. -/
private theorem row_creation_mass (v : I → ℂ) (p : P) :
    mass (∑ j, v j • (X j * p)) =
      (∑ j, ‖v j‖ ^ 2) * mass p + mass (∑ j, conj (v j) • pderiv j p) := by
  classical
  have expansion (f : I → P) (c : I → ℂ) :
      FactorialFockMetric.inner (∑ j, c j • f j) (∑ k, c k • f k) =
        ∑ j, ∑ k, conj (c j) * c k * FactorialFockMetric.inner (f j) (f k) := by
    rw [inner_sum_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_sum_right]
    apply Finset.sum_congr rfl
    intro k hk
    rw [inner_smul_first, inner_smul_second]
    ring
  have he : FactorialFockMetric.inner (∑ j, v j • (X j * p))
        (∑ j, v j • (X j * p)) =
      (∑ j, (‖v j‖ ^ 2 : ℂ)) * FactorialFockMetric.inner p p +
        FactorialFockMetric.inner (∑ j, conj (v j) • pderiv j p)
          (∑ j, conj (v j) • pderiv j p) := by
    rw [expansion, expansion]
    have hp (j k : I) :
        conj (v j) * v k * FactorialFockMetric.inner (X j * p) (X k * p) =
          (if j = k then conj (v j) * v k * FactorialFockMetric.inner p p else 0) +
          conj (v j) * v k * FactorialFockMetric.inner (pderiv k p) (pderiv j p) := by
      rw [creation_pairing, mul_add, mul_ite, mul_zero]
    simp_rw [hp, Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, RCLike.conj_mul,
        Finset.sum_mul]
      rfl
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Complex.conj_conj]
      ring
  have hsum : (∑ j, (‖v j‖ ^ 2 : ℂ)) = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [hsum] at he
  have hreal := congrArg Complex.re he
  simpa only [mass, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hreal

/-- Matrix-weighted creation is controlled by HS mass and scalar
operator norm. The estimate holds for EVERY polynomial p and arbitrary degree. -/
theorem quadratic_creation_bound (A : Matrix I I ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (p : P) :
    (∑ i, mass ((∑ j, A i j • X j) * p)) ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * mass p +
        q ^ 2 * ∑ j, mass (pderiv j p) := by
  have he (i : I) : (∑ j, A i j • X j) * p =
      ∑ j, A i j • (X j * p) := by simp only [Finset.sum_mul, smul_mul_assoc]
  simp_rw [he, row_creation_mass]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  exact add_le_add_right
    (polynomial_matrix_bound (fun i j => conj (A i j))
      (conjugate_scalar_matrix_bound A hq hA) (fun j => pderiv j p)) _

/-- Euler plus creation/derivative adjointness gives the exact number operator. -/
theorem gradient_mass {p : P} {n : ℕ} (hp : p.IsHomogeneous n) :
    (∑ i, mass (pderiv i p)) = (n : ℝ) * mass p := by
  have he : (∑ i, FactorialFockMetric.inner (pderiv i p) (pderiv i p)) =
      (n : ℂ) * FactorialFockMetric.inner p p := by
    calc
      _ = ∑ i, FactorialFockMetric.inner (X i * pderiv i p) p := by
        simp only [FactorialFockMetric.mul_X_pderiv_pairing]
      _ = FactorialFockMetric.inner (∑ i, X i * pderiv i p) p :=
        (inner_sum_left _ _).symm
      _ = _ := by
        rw [hp.sum_X_mul_pderiv]
        rw [inner_nsmul_first]
  have h := congrArg Complex.re he
  simpa [mass, re_sum, Complex.mul_re] using h

/-- Quadratic with the essential factor 1/2; all mixed terms are present. -/
def quadratic (A : Matrix I I ℂ) : P :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, A i j • (X i * X j)

/-- Exact homogeneous component of exp(Q_A), not a defined Wick moment. -/
def gaussianPiece (A : Matrix I I ℂ) (n : ℕ) : P :=
  (n.factorial : ℂ)⁻¹ • quadratic A ^ n

private theorem quadratic_homogeneous (A : Matrix I I ℂ) :
    (quadratic A).IsHomogeneous 2 := by
  unfold quadratic
  rw [smul_eq_C_mul]
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i hi
  apply IsHomogeneous.sum
  intro j hj
  rw [smul_eq_C_mul]
  exact ((isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)).C_mul _

private theorem gaussianPiece_homogeneous (A : Matrix I I ℂ) (n : ℕ) :
    (gaussianPiece A n).IsHomogeneous (2 * n) := by
  unfold gaussianPiece
  rw [smul_eq_C_mul]
  exact ((quadratic_homogeneous A).pow n).C_mul _

private theorem quadratic_pderiv (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (i : I) :
    pderiv i (quadratic A) = ∑ j, A i j • X j := by
  classical
  have hcol : (∑ j, A j i • (X j : P)) = ∑ j, A i j • (X j : P) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  have hrow : (∑ j, ∑ k, if j = i then A j k • (X k : P) else 0) =
      ∑ j, A i j • (X j : P) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [quadratic, Derivation.map_smul, map_sum, pderiv_mul, pderiv_X,
    Pi.single_apply, smul_add, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, hcol, hrow]
  rw [← add_smul]
  norm_num

/-- The annihilation equation is proved directly from Q_A^n/n!, including n=0. -/
theorem gaussianPiece_pderiv (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (n : ℕ) (i : I) :
    pderiv i (gaussianPiece A (n + 1)) =
      (∑ j, A i j • X j) * gaussianPiece A n := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hc : ((n + 1).factorial : ℂ)⁻¹ * (n + 1 : ℂ) = (n.factorial : ℂ)⁻¹ := by
    rw [hf]
    field_simp [hn, hnp]
  simp only [gaussianPiece, Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel,
    quadratic_pderiv A hsym]
  simp only [smul_eq_C_mul]
  have hcast : ((n + 1 : ℕ) : P) = C (n + 1 : ℂ) := by simp
  rw [hcast]
  have hC : (C (((n + 1).factorial : ℂ)⁻¹) : P) * C (n + 1 : ℂ) =
      C ((n.factorial : ℂ)⁻¹) := by rw [← map_mul, hc]
  calc
    _ = (C (((n + 1).factorial : ℂ)⁻¹) * C (n + 1 : ℂ)) *
        (quadratic A ^ n * (∑ j, C (A i j) * X j)) := by ring
    _ = _ := by rw [hC]; ring

/-- The all-degree CCR recurrence. No Gaussian norm identity is assumed. -/
theorem degree_mass_recurrence (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (n : ℕ) :
    (n + 1 : ℝ) * mass (gaussianPiece A (n + 1)) ≤
      ((∑ i, ∑ j, ‖A i j‖ ^ 2) / 2 + q ^ 2 * n) * mass (gaussianPiece A n) := by
  have he := gradient_mass (gaussianPiece_homogeneous A (n + 1))
  simp_rw [gaussianPiece_pderiv A hsym] at he
  have hb := quadratic_creation_bound A hq hA (gaussianPiece A n)
  rw [he, gradient_mass (gaussianPiece_homogeneous A n)] at hb
  push_cast at hb
  nlinarith

private theorem gaussianPiece_mass_zero (A : Matrix I I ℂ) :
    mass (gaussianPiece A 0) = 1 := by
  classical
  simp only [gaussianPiece, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
  rw [mass_eq_sum]
  simp [weight]

/-- A genuine infinite sum over EVERY Gaussian particle degree. -/
theorem all_degree_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) :
    Summable (fun n => mass (gaussianPiece A n)) := by
  exact TwistedGround.GaussianDegreeMajorant.summable_of_creation_recurrence
    (fun n => mass (gaussianPiece A n)) (by positivity) (sq_nonneg q)
    (pow_lt_one₀ hq hq1 (by norm_num)) (fun n => mass_nonneg _)
    (gaussianPiece_mass_zero A) (degree_mass_recurrence A hsym hq hA)

/-- Uniform in BOTH dimension and particle cutoff, with the HS/op-norm constant. -/
theorem all_degree_partial_bound (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), mass (gaussianPiece A n)) ≤
      Real.exp ((∑ i, ∑ j, ‖A i j‖ ^ 2) / (2 * (1 - q ^ 2))) := by
  have hM : 0 ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) / 2 := by positivity
  have hr : q ^ 2 < 1 := pow_lt_one₀ hq hq1 (by norm_num)
  have hb := TwistedGround.GaussianDegreeMajorant.tsum_bound
    (fun n => mass (gaussianPiece A n)) hM (sq_nonneg q) hr
    (fun n => mass_nonneg _) (gaussianPiece_mass_zero A)
    (degree_mass_recurrence A hsym hq hA)
  have hs := all_degree_summable A hsym hq hq1 hA
  have hfinite := hs.sum_le_tsum (Finset.range (N + 1)) (fun n _ => mass_nonneg (gaussianPiece A n))
  apply hfinite.trans
  simpa only [div_div] using hb

/-- Mixed exponential coefficient selected at its forced homogeneous degree.
For odd occupations this is zero by homogeneity. It is NOT the source value. -/
def gaussianCoefficient (A : Matrix I I ℂ) (d : I →₀ ℕ) : ℂ :=
  (gaussianPiece A (d.degree / 2)).coeff d

/-- The constant coefficient is exactly the vacuum normalization, also for
the empty mode type; it is derived from Q^0/0!, not supplied as a norm premise. -/
theorem gaussianCoefficient_zero (A : Matrix I I ℂ) :
    gaussianCoefficient A 0 = 1 := by
  simp [gaussianCoefficient, gaussianPiece]

/-- Odd occupations vanish at every degree, including repeated mixed modes. -/
theorem gaussianCoefficient_odd (A : Matrix I I ℂ) (d : I →₀ ℕ)
    (hd : d.degree % 2 = 1) : gaussianCoefficient A d = 0 := by
  apply (gaussianPiece_homogeneous A (d.degree / 2)).coeff_eq_zero
  omega

/-- A mixed coefficient at degree 2n comes from exactly the nth Gaussian
piece. This is the grading used in the still-required Wick identification. -/
theorem gaussianCoefficient_even (A : Matrix I I ℂ) (d : I →₀ ℕ) (n : ℕ)
    (hd : d.degree = 2 * n) :
    gaussianCoefficient A d = (gaussianPiece A n).coeff d := by
  simp [gaussianCoefficient, hd, Nat.mul_div_right]

/-- Exact mixed coefficient recurrence extracted from the annihilation
equation. The factor d(i)+1 is NOT discarded: it produces the factorial
multiplicity in the missing comparison with labelled source Wick moments. -/
theorem gaussianPiece_coefficient_step (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (n : ℕ) (i : I) (d : I →₀ ℕ) :
    (gaussianPiece A (n + 1)).coeff (d + Finsupp.single i 1) * (d i + 1 : ℂ) =
      ∑ j, A i j * (X j * gaussianPiece A n).coeff d := by
  have he := congrArg (fun p : P => p.coeff d) (gaussianPiece_pderiv A hsym n i)
  simpa only [coeff_pderiv, Finset.sum_mul, smul_mul_assoc, coeff_sum,
    coeff_smul, smul_eq_mul] using he

/-- Every finite set of mixed coefficients, with no common particle cutoff
in the conclusion's constant. Repetitions have the EXACT occupation factorial. -/
theorem finite_occupation_bound (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (S : Finset (I →₀ ℕ)) :
    (∑ d ∈ S, (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2) ≤
      Real.exp ((∑ i, ∑ j, ‖A i j‖ ^ 2) / (2 * (1 - q ^ 2))) := by
  classical
  let N : ℕ := S.sup (fun d => d.degree)
  have hmem (d : I →₀ ℕ) (hd : d ∈ S) : d.degree / 2 ∈ Finset.range (N + 1) := by
    have hdeg : d.degree ≤ N := Finset.le_sup (f := fun d => d.degree) hd
    exact Finset.mem_range.mpr (by have := Nat.div_le_self d.degree 2; omega)
  calc
    _ ≤ ∑ d ∈ S, ∑ n ∈ Finset.range (N + 1),
        (weight d : ℝ) * ‖(gaussianPiece A n).coeff d‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      change (weight d : ℝ) * ‖(gaussianPiece A (d.degree / 2)).coeff d‖ ^ 2 ≤ _
      exact Finset.single_le_sum
        (fun n _ => mul_nonneg (Nat.cast_nonneg (weight d))
          (sq_nonneg ‖(gaussianPiece A n).coeff d‖)) (hmem d hd)
    _ = ∑ n ∈ Finset.range (N + 1), ∑ d ∈ S,
        (weight d : ℝ) * ‖(gaussianPiece A n).coeff d‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.range (N + 1), mass (gaussianPiece A n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact finite_coeff_mass_le _ S
    _ ≤ _ := all_degree_partial_bound A hsym hq hq1 hA N

/-- True factorial-l2 summability of the finite-matrix mixed Gaussian
coefficients over the INFINITE occupation type. Source/Wick identification is
a separate still-missing obligation, rather than a hypothesis of this theorem. -/
theorem occupation_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) :
    Summable (fun d => (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2) := by
  apply summable_of_sum_le
    (fun d => mul_nonneg (Nat.cast_nonneg (weight d)) (sq_nonneg ‖gaussianCoefficient A d‖))
  intro S
  exact finite_occupation_bound A hsym hq hq1 hA S



end D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
