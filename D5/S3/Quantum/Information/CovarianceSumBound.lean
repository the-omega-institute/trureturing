/- GID: D5/S3/Quantum/Information/CovarianceSumBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/CovarianceSumBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density-state covariance obeys Cauchy-Schwarz and a sparse half-width sum bound. -/

import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Information.CovarianceSumBound
open scoped ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem density_psd (ρ : DensityState n) :
    (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)

/-- Real expectation in a density state. -/
def expectation (ρ : DensityState n) (A : Matrix n n ℂ) : ℝ :=
  (trace (CStarMatrix.ofMatrix.symm ρ.1 * A)).re

/-- Symmetrized real covariance; no commutativity between A and B is required. -/
def covariance (ρ : DensityState n) (A B : Matrix n n ℂ) : ℝ :=
  (expectation ρ (A * B) + expectation ρ (B * A)) / 2 -
    expectation ρ A * expectation ρ B

/-- Variance of an observable in a density state. -/
def variance (ρ : DensityState n) (A : Matrix n n ℂ) : ℝ :=
  expectation ρ (A * A) - expectation ρ A ^ 2

private theorem expect_add (ρ : DensityState n) (A B : Matrix n n ℂ) :
    expectation ρ (A + B) = expectation ρ A + expectation ρ B := by
  simp [expectation, mul_add]

private theorem expect_sub (ρ : DensityState n) (A B : Matrix n n ℂ) :
    expectation ρ (A - B) = expectation ρ A - expectation ρ B := by
  simp [expectation, mul_sub]

private theorem expect_smul (ρ : DensityState n) (t : ℝ) (A : Matrix n n ℂ) :
    expectation ρ (t • A) = t * expectation ρ A := by
  simp [expectation, Complex.real_smul, Complex.mul_re]

private theorem expect_one (ρ : DensityState n) : expectation ρ 1 = 1 := by
  have h : trace (CStarMatrix.ofMatrix.symm ρ.1) = 1 := ρ.2.2
  simpa [expectation] using congrArg Complex.re h

theorem covariance_symm (ρ : DensityState n) (A B : Matrix n n ℂ) :
    covariance ρ A B = covariance ρ B A := by unfold covariance; ring

theorem covariance_add_right (ρ : DensityState n) (A B C : Matrix n n ℂ) :
    covariance ρ A (B + C) = covariance ρ A B + covariance ρ A C := by
  simp only [covariance, mul_add, add_mul, expect_add]
  ring

theorem covariance_self (ρ : DensityState n) (A : Matrix n n ℂ) :
    covariance ρ A A = variance ρ A := by unfold covariance variance; ring

private theorem expect_mul_symm (ρ : DensityState n) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    expectation ρ (A * B) = expectation ρ (B * A) := by
  have h := congrArg Complex.re (trace_conjTranspose
    (CStarMatrix.ofMatrix.symm ρ.1 * (A * B)))
  simp only [conjTranspose_mul, hA.eq, hB.eq, (density_psd ρ).1.eq,
    Complex.star_def, Complex.conj_re] at h
  rw [trace_mul_comm (B * A)] at h
  exact h.symm

private def centered (ρ : DensityState n) (A : Matrix n n ℂ) :=
  A - expectation ρ A • (1 : Matrix n n ℂ)

private theorem centered_hermitian (ρ : DensityState n) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (centered ρ A).IsHermitian :=
  hA.sub (isHermitian_one.smul (isSelfAdjoint_iff.mpr rfl))

private theorem centered_pair (ρ : DensityState n) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (trace (centered ρ B * CStarMatrix.ofMatrix.symm ρ.1 * (centered ρ A)ᴴ)).re =
      covariance ρ A B := by
  rw [(centered_hermitian ρ hA).eq, trace_mul_cycle]
  rw [trace_mul_comm]
  change expectation ρ (centered ρ A * centered ρ B) = _
  simp only [centered, sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one,
    expect_sub, expect_smul, expect_one, covariance]
  rw [expect_mul_symm ρ hA hB]
  ring

theorem variance_nonneg (ρ : DensityState n) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : 0 ≤ variance ρ A := by
  rw [← covariance_self, ← centered_pair ρ hA hA]
  exact (Complex.nonneg_iff.mp
    ((density_psd ρ).mul_mul_conjTranspose_same (centered ρ A)).trace_nonneg).1

theorem abs_covariance_le (ρ : DensityState n) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |covariance ρ A B| ≤ Real.sqrt (variance ρ A * variance ρ B) := by
  let M := CStarMatrix.ofMatrix.symm ρ.1
  let _ := M.toMatrixSeminormedAddCommGroup (density_psd ρ)
  let _ := M.toMatrixInnerProductSpace (density_psd ρ)
  have pair : (inner ℂ (centered ρ A) (centered ρ B)).re = covariance ρ A B :=
    centered_pair ρ hA hB
  have va : variance ρ A = ‖centered ρ A‖ ^ 2 := by
    rw [← covariance_self, ← centered_pair ρ hA hA]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (centered ρ A)
  have vb : variance ρ B = ‖centered ρ B‖ ^ 2 := by
    rw [← covariance_self, ← centered_pair ρ hB hB]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (centered ρ B)
  rw [va, vb, ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    ← pair]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)


private theorem expect_nonneg (ρ : DensityState n) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : 0 ≤ expectation ρ A := by
  let M := CStarMatrix.ofMatrix.symm ρ.1
  have hs : (CFC.sqrt M)ᴴ = CFC.sqrt M := by
    simpa only [star_eq_conjTranspose] using (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  have ht := (Complex.nonneg_iff.mp
    (hA.mul_mul_conjTranspose_same (CFC.sqrt M)).trace_nonneg).1
  rw [hs, trace_mul_cycle, CFC.sqrt_mul_sqrt_self M (density_psd ρ).nonneg] at ht
  exact ht

private theorem expect_mono (ρ : DensityState n) {A B : Matrix n n ℂ}
    (h : A ≤ B) : expectation ρ A ≤ expectation ρ B := by
  have hp := expect_nonneg ρ (sub_nonneg.mpr h).posSemidef
  rw [expect_sub] at hp
  linarith

open scoped Matrix.Norms.L2Operator in
/-- Popoviciu bound in a density state. Δ is the HALF width of [c−Δ,c+Δ]. -/
theorem variance_le_half_width_sq (ρ : DensityState n) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {c Δ : ℝ} (_hΔ : 0 ≤ Δ)
    (hspec : ∀ x ∈ spectrum ℝ A, x ∈ Set.Icc (c - Δ) (c + Δ)) :
    variance ρ A ≤ Δ ^ 2 := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hcfc : cfc (fun x : ℝ => (x - c) ^ 2) A ≤
      algebraMap ℝ (Matrix n n ℂ) (Δ ^ 2) := by
    apply (cfc_le_algebraMap_iff _ _ _ (ha := hsa)).mpr
    intro x hx
    have hi := hspec x hx
    nlinarith [sq_nonneg (x - c), mul_nonneg (sub_nonneg.mpr hi.1)
      (sub_nonneg.mpr hi.2)]
  have hop : (A - c • 1) * (A - c • 1) ≤ (Δ ^ 2) • (1 : Matrix n n ℂ) := by
    rw [cfc_pow _ 2 A (ha := hsa), cfc_sub (fun x : ℝ => x) (fun _ => c) A,
      cfc_id' ℝ A hsa, cfc_const c A hsa] at hcfc
    simpa only [Algebra.algebraMap_eq_smul_one, pow_two] using hcfc
  have he := expect_mono ρ hop
  simp only [sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one,
    expect_sub, expect_smul, expect_one] at he
  unfold variance
  nlinarith [sq_nonneg (expectation ρ A - c)]

/-- Sparse covariance sum from uniform variance bounds. Sparsity is an input. -/
theorem covariance_sum_le_of_variance {ι : Type*} (Q : Finset ι)
    (ρ : DensityState n) (R : ι → Matrix n n ℂ) (b : ℕ) (Δ : ℝ)
    (hR : ∀ x ∈ Q, (R x).IsHermitian)
    (hv : ∀ x ∈ Q, variance ρ (R x) ≤ Δ ^ 2)
    (hsparse : ∀ x ∈ Q, (Q.filter fun y => covariance ρ (R x) (R y) ≠ 0).card ≤ b) :
    ∑ x ∈ Q, ∑ y ∈ Q, |covariance ρ (R x) (R y)| ≤
      (Q.card : ℝ) * b * Δ ^ 2 := by
  classical
  have hentry (x) (hx : x ∈ Q) (y) (hy : y ∈ Q) :
      |covariance ρ (R x) (R y)| ≤ Δ ^ 2 := by
    apply (abs_covariance_le ρ (hR x hx) (hR y hy)).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [pow_two] using
      mul_le_mul (hv x hx) (hv y hy) (variance_nonneg ρ (hR y hy)) (sq_nonneg Δ)
  calc
    _ ≤ ∑ x ∈ Q, (b : ℝ) * Δ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      let S := Q.filter fun y => covariance ρ (R x) (R y) ≠ 0
      have heq : ∑ y ∈ Q, |covariance ρ (R x) (R y)| =
          ∑ y ∈ S, |covariance ρ (R x) (R y)| := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y hy hn
        have hz : covariance ρ (R x) (R y) = 0 := by
          simpa [S, hy] using hn
        simp [hz]
      rw [heq]
      calc
        _ ≤ ∑ _y ∈ S, Δ ^ 2 := Finset.sum_le_sum fun y hy =>
          hentry x hx y (Finset.mem_filter.mp hy).1
        _ = (S.card : ℝ) * Δ ^ 2 := by simp
        _ ≤ (b : ℝ) * Δ ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hsparse x hx) (sq_nonneg Δ)
    _ = _ := by simp; ring

open scoped Matrix.Norms.L2Operator in
/-- The density-state covariance sum bound, with interval HALF width Δ.
The row support bound is supplied by locality, which is not derived here. -/
theorem covariance_sum_le {ι : Type*} (Q : Finset ι)
    (ρ : DensityState n) (R : ι → Matrix n n ℂ) (b : ℕ) (Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hR : ∀ x ∈ Q, (R x).IsHermitian)
    (c : ι → ℝ)
    (hspec : ∀ x ∈ Q, ∀ t ∈ spectrum ℝ (R x), t ∈ Set.Icc (c x - Δ) (c x + Δ))
    (hsparse : ∀ x ∈ Q, (Q.filter fun y => covariance ρ (R x) (R y) ≠ 0).card ≤ b) :
    ∑ x ∈ Q, ∑ y ∈ Q, |covariance ρ (R x) (R y)| ≤
      (Q.card : ℝ) * b * Δ ^ 2 := by
  apply covariance_sum_le_of_variance Q ρ R b Δ hR _ hsparse
  intro x hx
  exact variance_le_half_width_sq ρ (hR x hx) hΔ (hspec x hx)

#print axioms covariance_sum_le
end D5.S3.Quantum.Information.CovarianceSumBound
