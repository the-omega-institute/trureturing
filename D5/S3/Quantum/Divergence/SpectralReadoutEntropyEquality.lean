/- GID: D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SpectralReadoutEntropyEquality
   mirror-E: none(waiver:general-analytic-equality-criterion)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Jensen]
   utility: none
   digest: Spectral readout preserves Shannon entropy iff the readout matrix is diagonal. -/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.SpectralReadoutEntropyEquality

open Matrix
open D5.S3.Entropy.MaxEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem entropy_eq_iff_support (M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n) (x : n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    shannonEntropy (M *ᵥ x) = shannonEntropy x ↔
      ∀ i j, M i j ≠ 0 → x j = (M *ᵥ x) i := by
  let f : ℝ → ℝ := fun t => t * Real.log t
  have hrow (i : n) : f ((M *ᵥ x) i) ≤ ∑ j, M i j * f (x j) := by
    simpa only [f, Matrix.mulVec, dotProduct, smul_eq_mul] using
      Real.convexOn_mul_log.map_sum_le (t := Finset.univ) (w := M i) (p := x)
        (fun j _ => nonneg_of_mem_doublyStochastic hM)
        (sum_row_of_mem_doublyStochastic hM i) (fun j _ => hx j)
  have hsum : (∑ i, ∑ j, M i j * f (x j)) = ∑ j, f (x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hM j, one_mul]
  have heq (i : n) : f ((M *ᵥ x) i) = ∑ j, M i j * f (x j) ↔
      ∀ j, M i j ≠ 0 → x j = (M *ᵥ x) i := by
    simpa only [f, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mem_univ,
      forall_true_left] using
      Real.strictConvexOn_mul_log.map_sum_eq_iff' (t := Finset.univ) (w := M i) (p := x)
        (fun j _ => nonneg_of_mem_doublyStochastic hM)
        (sum_row_of_mem_doublyStochastic hM i) (fun j _ => hx j)
  have hentropy (y : n → ℝ) : shannonEntropy y = -(∑ i, f (y i)) := by
    simp [shannonEntropy, Real.negMulLog, f, Finset.sum_neg_distrib]
  rw [hentropy, hentropy, neg_inj, ← hsum,
    Finset.sum_eq_sum_iff_of_le (fun i _ => hrow i)]
  simp only [Finset.mem_univ, forall_true_left, heq]

private theorem readout_diagonal (U : Matrix n n ℂ) (x : n → ℝ) (i : n) :
    (U * Matrix.diagonal (fun j => (x j : ℂ)) * star U) i i =
      (((RHLinalg.normSqMatrix U *ᵥ x) i : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply,
    RHLinalg.normSqMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  calc
    U i j * (x j : ℂ) * star (U i j) =
        (U i j * star (U i j)) * (x j : ℂ) := by ring
    _ = _ := by simp [Complex.mul_conj']

/-- For any nonnegative spectrum and unitary change of basis, the entropy of the diagonal
readout equals the spectral Shannon entropy exactly when the conjugated matrix is diagonal.
No normalization, positive definiteness, or distinct-eigenvalue assumption is required. -/
theorem spectral_readout_entropy_eq_iff_isDiag (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (x : n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    shannonEntropy (fun i =>
      (U * Matrix.diagonal (fun j => (x j : ℂ)) * star U) i i |>.re) =
        shannonEntropy x ↔
      (U * Matrix.diagonal (fun j => (x j : ℂ)) * star U).IsDiag := by
  let M := RHLinalg.normSqMatrix U
  let p := M *ᵥ x
  let D := Matrix.diagonal (fun j => (x j : ℂ))
  let P := Matrix.diagonal (fun i => (p i : ℂ))
  have hstar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hustar : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hdiag (i : n) : (U * D * star U) i i = (p i : ℂ) := readout_diagonal U x i
  have hread : (fun i => (U * D * star U) i i |>.re) = p := by
    funext i
    rw [hdiag]
    rfl
  change shannonEntropy (fun i => (U * D * star U) i i |>.re) = _ ↔ _
  rw [hread, entropy_eq_iff_support M
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU) x hx]
  constructor
  · intro hs
    have hinter : U * D = P * U := by
      ext i j
      simp only [D, P, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : U i j = 0
      · simp [hij]
      · have hm : M i j ≠ 0 := by
          simpa [M, RHLinalg.normSqMatrix] using pow_ne_zero 2 (norm_ne_zero_iff.mpr hij)
        rw [hs i j hm]
        exact mul_comm _ _
    have ha : U * D * star U = P := by
      rw [hinter, Matrix.mul_assoc, hustar, Matrix.mul_one]
    rw [ha]
    exact Matrix.isDiag_diagonal _
  · intro ha
    have hap : U * D * star U = P := by
      rw [← ha.diagonal_diag]
      congr 1
      funext i
      exact hdiag i
    have hinter : U * D = P * U := by
      rw [← hap]
      simp only [Matrix.mul_assoc, hstar, Matrix.mul_one]
    intro i j hm
    have hij : U i j ≠ 0 := by
      intro hzero
      apply hm
      simp [M, RHLinalg.normSqMatrix, hzero]
    have he := congrArg (fun A : Matrix n n ℂ => A i j) hinter
    simp only [D, P, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have he' : (x j : ℂ) = (p i : ℂ) :=
      mul_left_cancel₀ hij (he.trans (mul_comm _ _))
    exact_mod_cast he'

#print axioms spectral_readout_entropy_eq_iff_isDiag

end D5.S3.Quantum.Divergence.SpectralReadoutEntropyEquality
