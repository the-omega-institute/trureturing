/- GID: D5/S3/Fourier/MatrixGaussianSourceDerivatives
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussianSourceDerivatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite mixed source extraction for positive matrix lattice Gaussians. -/

import D5.S3.Fourier.MatrixGaussianSourcePoisson
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Finite mixed coordinate derivatives, with genuine Gaussian majorants. -/

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section
variable {r : ℕ}

/-- An ordered finite list specifies successive complex coordinate derivatives.
The list may be empty, and no nonempty rank assumption is imposed. -/
def sourcePartial : List (Fin r) → ((Fin r → ℂ) → ℂ) → (Fin r → ℂ) → ℂ
  | [], f, z => f z
  | i :: is, f, z => deriv (fun t : ℂ => sourcePartial is f (z + t • Pi.single i 1)) 0

private def sourceMonomial (is : List (Fin r)) (a : Fin r → ℤ) : ℂ :=
  (is.map (fun i => (a i : ℂ))).prod

private lemma sourceMonomial_norm (is : List (Fin r)) (a : Fin r → ℤ) :
    ‖sourceMonomial is a‖ ≤ ‖(fun i => (a i : ℝ))‖ ^ is.length := by
  induction is with
  | nil => simp [sourceMonomial]
  | cons i is ih =>
    have hi : ‖(a i : ℂ)‖ ≤ ‖(fun i => (a i : ℝ))‖ := by
      simpa using norm_le_pi_norm (fun i => (a i : ℝ)) i
    simpa [sourceMonomial, pow_succ, mul_comm] using
      mul_le_mul hi ih (norm_nonneg _) (norm_nonneg _)

private lemma source_shift (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (a : Fin r → ℤ) (z : Fin r → ℂ) (i : Fin r) (t : ℂ) :
    latticeSourceMap A b a (z + t • Pi.single i 1) =
      latticeSourceMap A b a z * Complex.exp (t * (a i : ℂ)) := by
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc]
  simp only [Pi.single_apply]
  simp
  <;> ring

private lemma source_moment_deriv (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (is : List (Fin r)) (a : Fin r → ℤ) (z : Fin r → ℂ) (i : Fin r) :
    deriv (fun t : ℂ => sourceMonomial is a *
      latticeSourceMap A b a (z + t • Pi.single i 1)) 0 =
      sourceMonomial (i :: is) a * latticeSourceMap A b a z := by
  simp_rw [source_shift, ← mul_assoc]
  have hd := (((hasDerivAt_id (0 : ℂ)).mul_const (a i : ℂ)).cexp).const_mul
    (sourceMonomial is a * latticeSourceMap A b a z)
  simpa [sourceMonomial, mul_comm, mul_left_comm, mul_assoc] using hd.deriv

private lemma source_moment_bound (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (hb : 0 < b.re) (t : ℝ) (ht : 0 < t)
    (hq : ∀ x : Fin r → ℝ, t * (∑ i, x i^2) ≤ quadratic A x)
    (R : ℝ) (z : Fin r → ℂ) (hz : ∀ i, |(z i).re| ≤ R)
    (is : List (Fin r)) (a : Fin r → ℤ) :
    ‖sourceMonomial is a * latticeSourceMap A b a z‖ ≤
      ((is.length.factorial : ℝ) * Real.exp
        ((r : ℝ)*(R+1)^2/(2*(Real.pi*b.re*t)))) *
      ‖gaussianMap A (b/2) (fun i => (a i : ℝ))‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (sourceMonomial_norm is a) (norm_nonneg _)).trans
    (polynomial_source_gaussian_bound A b hb t ht hq R z hz is.length _)

private lemma deriv_tsum_source_moment (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (is : List (Fin r)) (z : Fin r → ℂ) (i : Fin r) :
    deriv (fun t : ℂ => ∑' a : Fin r → ℤ, sourceMonomial is a *
      latticeSourceMap A b a (z + t • Pi.single i 1)) 0 =
      ∑' a : Fin r → ℤ, sourceMonomial (i :: is) a * latticeSourceMap A b a z := by
  obtain ⟨s, hs, hq⟩ := exists_quadratic_lower_bound A hA
  let R : ℝ := ‖z‖+1
  let c : ℝ := (is.length.factorial : ℝ)*Real.exp
    ((r : ℝ)*(R+1)^2/(2*(Real.pi*b.re*s)))
  let u : (Fin r → ℤ) → ℝ := fun a => c * ‖gaussianMap A (b/2) (fun j => (a j : ℝ))‖
  have hu : Summable u := (summable_norm_gaussian A hA (b/2)
    (by simpa using half_pos hb)).mul_left c
  have hf (a : Fin r → ℤ) : DifferentiableOn ℂ
      (fun t : ℂ => sourceMonomial is a * latticeSourceMap A b a (z+t • Pi.single i 1))
      (Metric.ball (0 : ℂ) 1) := by
    simp_rw [source_shift]
    fun_prop
  have hbound (a : Fin r → ℤ) (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) 1) :
      ‖sourceMonomial is a * latticeSourceMap A b a (z+t • Pi.single i 1)‖ ≤ u a := by
    apply source_moment_bound A b hb s hs hq R (z+t • (Pi.single i 1 : Fin r → ℂ)) _ is a
    intro j
    have ht' : ‖t‖ ≤ 1 := (by simpa using ht : ‖t‖ < 1).le
    have hj : ‖(Pi.single i (1 : ℂ) : Fin r → ℂ) j‖ ≤ 1 := by
      by_cases h : j = i <;> simp [Pi.single_apply, h, Ne.symm]
    calc
      |((z+t • (Pi.single i 1 : Fin r → ℂ)) j).re| ≤ ‖(z+t • (Pi.single i 1 : Fin r → ℂ)) j‖ := Complex.abs_re_le_norm _
      _ ≤ ‖z j‖ + ‖t‖ * ‖(Pi.single i (1 : ℂ) : Fin r → ℂ) j‖ := by
        simpa only [Pi.add_apply, Pi.smul_apply, norm_smul] using
          norm_add_le (z j) (t • (Pi.single i (1 : ℂ) : Fin r → ℂ) j)
      _ ≤ ‖z‖ + 1 := add_le_add (norm_le_pi_norm z j)
        ((mul_le_mul_of_nonneg_left hj (norm_nonneg t)).trans (by simpa using ht'))
  have h := Complex.hasSum_deriv_of_summable_norm hu hf Metric.isOpen_ball hbound
    (show (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 by simp)
  simpa only [source_moment_deriv] using h.tsum_eq.symm

/-- Every finite mixed coordinate source derivative can be taken inside the
full lattice sum. Each derivative is the actual lattice monomial moment; the
proof uses summable polynomial Gaussian bounds and Mathlib's holomorphic
series differentiation, without an extraction or summability premise. -/
theorem sourcePartial_tsum (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (is : List (Fin r)) (z : Fin r → ℂ) :
    sourcePartial is (fun w => ∑' a : Fin r → ℤ, latticeSourceMap A b a w) z =
      ∑' a : Fin r → ℤ, (is.map (fun i => (a i : ℂ))).prod * latticeSourceMap A b a z := by
  induction is generalizing z with
  | nil => simp [sourcePartial]
  | cons i is ih =>
    simp only [sourcePartial]
    simp_rw [ih]
    exact deriv_tsum_source_moment A hA b hb is z i

#print axioms sourcePartial_tsum

end
end D5.S3.Fourier.MatrixGaussian
