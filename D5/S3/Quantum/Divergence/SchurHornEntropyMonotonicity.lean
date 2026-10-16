/- GID: D5/S3/Quantum/Divergence/SchurHornEntropyMonotonicity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SchurHornEntropyMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Jensen]
   utility: none
   digest: Unitary spectral readout cannot decrease finite Shannon entropy. -/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.SchurHornEntropyMonotonicity

open Matrix
open D5.S3.Entropy.MaxEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A doubly stochastic matrix sends a nonnegative vector to one whose `x log x`
sum is no larger. This is the scalar Jensen step in the Schur--Horn bridge. -/
theorem sum_mul_log_mulVec_le_of_doublyStochastic
    (M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, (M *ᵥ x) i * Real.log ((M *ᵥ x) i) ≤
      ∑ i, x i * Real.log (x i) := by
  have hRow (i : n) :
      (M *ᵥ x) i * Real.log ((M *ᵥ x) i) ≤
        ∑ j, M i j * (x j * Real.log (x j)) := by
    simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using
      Real.convexOn_mul_log.map_sum_le
        (t := Finset.univ) (w := M i) (p := x)
        (fun j _ => nonneg_of_mem_doublyStochastic hM)
        (sum_row_of_mem_doublyStochastic hM i)
        (fun j _ => hx j)
  calc
    ∑ i, (M *ᵥ x) i * Real.log ((M *ᵥ x) i)
        ≤ ∑ i, ∑ j, M i j * (x j * Real.log (x j)) :=
      Finset.sum_le_sum fun i _ => hRow i
    _ = ∑ j, x j * Real.log (x j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hM j, one_mul]

/-- The diagonal of a unitary conjugate of a diagonal spectrum is the
`normSqMatrix` doubly stochastic readout of that spectrum. -/
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

/-- A unitary spectral readout cannot decrease Shannon entropy. -/
theorem spectral_readout_entropy_le (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (x : n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    shannonEntropy x ≤
      shannonEntropy (fun i =>
        (U * Matrix.diagonal (fun j => (x j : ℂ)) * star U) i i |>.re) := by
  let M := RHLinalg.normSqMatrix U
  have hconv := sum_mul_log_mulVec_le_of_doublyStochastic M
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU) x hx
  have hread :
      (fun i =>
        (U * Matrix.diagonal (fun j => (x j : ℂ)) * star U) i i |>.re) =
      M *ᵥ x := by
    funext i
    rw [readout_diagonal U x i]
    rfl
  rw [hread]
  have hentropy (y : n → ℝ) :
      shannonEntropy y = -(∑ i, y i * Real.log (y i)) := by
    simp [shannonEntropy, Real.negMulLog, Finset.sum_neg_distrib]
  rw [hentropy, hentropy]
  exact neg_le_neg hconv

#print axioms sum_mul_log_mulVec_le_of_doublyStochastic
#print axioms spectral_readout_entropy_le

end D5.S3.Quantum.Divergence.SchurHornEntropyMonotonicity
