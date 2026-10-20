/- GID: D5/S3/Quantum/Subentropy/EigenbasisBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/EigenbasisBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Local eigenbasis blocks preserve the opposite marginal and expose spectral weights. -/

import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
import Mathlib.Analysis.Matrix.Spectrum

/-! The blocks remain unnormalized positive matrices, including zero blocks. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.Subentropy.EigenbasisBlocks
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def localConjugate (U : Matrix A A ℂ)
    (M : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ)) * M * (U ⊗ₖ (1 : Matrix B B ℂ))

private theorem local_entries (U : Matrix A A ℂ)
    (M : Matrix (A × B) (A × B) ℂ) (x y : A) (b d : B) :
    localConjugate U M (x,b) (y,d) =
      ∑ a, ∑ c, star (U a x) * M (a,b) (c,d) * U c y := by
  unfold localConjugate
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]

private theorem local_right (U : Matrix A A ℂ)
    (M : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (localConjugate U M) =
      U.conjTranspose * partialTraceRight M * U := by
  rw [Matrix.mul_assoc]
  ext x y
  simp only [partialTraceRight, local_entries, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

private theorem local_left (U : Matrix A A ℂ) (hU : U * U.conjTranspose = 1)
    (M : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (localConjugate U M) = partialTraceLeft M := by
  ext b d
  let S : Matrix A A ℂ := fun a c => M (a,b) (c,d)
  have heq : partialTraceLeft (localConjugate U M) b d =
      (U.conjTranspose * S * U).trace := by
    change (∑ x, localConjugate U M (x,b) (x,d)) =
      ∑ x, ∑ c, (∑ a, star (U a x) * M (a,b) (c,d)) * U c x
    apply Finset.sum_congr rfl
    intro x _
    rw [local_entries, Finset.sum_comm]
    simp only [Finset.sum_mul, mul_assoc]
  rw [heq, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rfl

private theorem local_density (U : Matrix A A ℂ) (hU : U * U.conjTranspose = 1)
    (M : Matrix (A × B) (A × B) ℂ) (hM : M.PosSemidef) :
    (localConjugate U M).PosSemidef ∧ (localConjugate U M).trace = M.trace := by
  have hJ : (U ⊗ₖ (1 : Matrix B B ℂ)) *
      (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hU, Matrix.one_mul, Matrix.one_kronecker_one]
  constructor
  · simpa only [localConjugate, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] using
        hM.mul_mul_conjTranspose_same (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ))
  · rw [localConjugate, Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

/-- In the first marginal's eigenbasis, the diagonal blocks are positive, sum to
the second marginal, and have exactly the first marginal's spectral weights. -/
theorem eigenbasis_blocks (M : Matrix (A × B) (A × B) ℂ)
    (hM : M.PosSemidef) :
    let hR := (partialTraceRight_posSemidef hM).isHermitian
    let U : Matrix A A ℂ := hR.eigenvectorUnitary
    let K := localConjugate U M
    let Y := fun x : A => K.submatrix (fun b => (x,b)) (fun b => (x,b))
    K.PosSemidef ∧ K.trace = M.trace ∧
      (∀ x, (Y x).PosSemidef) ∧
      (∑ x, Y x) = partialTraceLeft M ∧
      (∀ x, (Y x).trace = (hR.eigenvalues x : ℂ)) ∧
      blockPinch K = (fun i j => if i.1 = j.1 then Y i.1 i.2 j.2 else 0) := by
  dsimp only
  let hR := (partialTraceRight_posSemidef hM).isHermitian
  let U : Matrix A A ℂ := hR.eigenvectorUnitary
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hR.eigenvectorUnitary
  have hK := local_density U hU M hM
  refine ⟨hK.1, hK.2, (fun x => hK.1.submatrix (fun b => (x,b))), ?_, ?_, ?_⟩
  · have heq : (∑ x : A, (localConjugate U M).submatrix
        (fun b => (x,b)) (fun b => (x,b))) = partialTraceLeft (localConjugate U M) := by
      ext b d
      simp only [Matrix.sum_apply, Matrix.submatrix_apply, partialTraceLeft]
    exact heq.trans (local_left U hU M)
  · have hd : U.conjTranspose * partialTraceRight M * U =
        Matrix.diagonal (fun x => (hR.eigenvalues x : ℂ)) := by
      simpa only [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
        Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
          hR.conjStarAlgAut_star_eigenvectorUnitary
    intro x
    have hx := congrArg (fun N : Matrix A A ℂ => N x x)
      ((local_right U M).trans hd)
    simpa only [Matrix.diagonal_apply_eq, partialTraceRight, Matrix.trace,
      Matrix.diag_apply, Matrix.submatrix_apply] using hx
  · ext i j
    by_cases hij : i.1 = j.1
    · simp only [blockPinch, hij, ite_true, Matrix.submatrix_apply]
      congr 1
      exact Prod.ext hij rfl
    · simp only [blockPinch, hij, ite_false]

end D5.S3.Quantum.Subentropy.EigenbasisBlocks
