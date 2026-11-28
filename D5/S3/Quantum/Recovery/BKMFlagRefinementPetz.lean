/- GID: D5/S3/Quantum/Recovery/BKMFlagRefinementPetz
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMFlagRefinementPetz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary testing and ordinary Petz under classical flag refinement. -/

import D5.S3.Quantum.Recovery.BKMFlagRefinement
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! # Binary testing and ordinary Petz under classical flag refinement -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)

namespace D5.S3.Quantum.Recovery.BKMFlagRefinement

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

omit [DecidableEq n] in
theorem traceNorm_joint (S : ι → Matrix n n ℂ) :
    traceNorm (joint S) = ∑ i, traceNorm (S i) := by
  classical
  let Q : ι → Matrix n n ℂ := fun i => (S i)ᴴ * S i
  have hQ (i : ι) : (Q i).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hgram : (joint S)ᴴ * joint S = joint Q := by
    simp only [joint, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    rfl
  simp only [Foundation.FiniteTraceDistance.traceNorm, hgram]
  rw [CFC.sqrt_eq_real_sqrt _ (hgram ▸ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg),
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero),
    cfc_joint _ Q (fun i => (hQ i).isHermitian), Matrix.trace_blockDiagonal, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [CFC.sqrt_eq_real_sqrt _ (hQ i).nonneg,
      cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

/-- The Umegaki trace expression with a faithful second argument.
Real.log at zero supplies the usual zero contribution from the kernel of S. -/
def relativeEntropyOfMatrices (S T : Matrix n n ℂ) : ℝ :=
  (S * (CFC.log S - CFC.log T)).trace.re

def partialTraceEntropyLoss (S T : ι → Matrix n n ℂ) : ℝ :=
  relativeEntropyOfMatrices (n := n × ι) (joint S) (joint T) -
    relativeEntropyOfMatrices (marginal S) (marginal T)

private theorem relativeEntropyOfMatrices_joint (S T : ι → Matrix n n ℂ)
    (hS : ∀ i, (S i).IsHermitian) (hT : ∀ i, (T i).IsHermitian) :
    relativeEntropyOfMatrices (joint S) (joint T) =
      ∑ i, relativeEntropyOfMatrices (S i) (T i) := by
  unfold relativeEntropyOfMatrices CFC.log
  rw [cfc_joint _ S hS, cfc_joint _ T hT]
  simp only [joint, ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal, Complex.re_sum]
  rfl

private theorem relativeEntropyOfMatrices_smul (S T : Matrix n n ℂ) (hS : S.IsHermitian)
    (hT : T.PosDef) {c : ℝ} (hc : 0 < c) :
    relativeEntropyOfMatrices (c • S) (c • T) = c * relativeEntropyOfMatrices S T := by
  let e : ℝ → ℝ := fun x => if x = 0 then 0 else 1
  have hE : S * cfc e S = S := by
    have h := cfc_mul (fun x : ℝ => x) e S continuous_id.continuousOn
      (S.finite_real_spectrum.continuousOn _)
    rw [cfc_id' ℝ S hS.isSelfAdjoint] at h
    rw [← h]
    calc
      cfc (fun x => x * e x) S = cfc (fun x : ℝ => x) S := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0 <;> simp [e, hx]
      _ = S := cfc_id' ℝ S hS.isSelfAdjoint
  have hF : cfc e T = 1 := by
    rw [← cfc_const_one ℝ T]
    apply cfc_congr
    intro x hx
    rw [hT.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    simp [e, (hT.eigenvalues_pos j).ne']
  have hInner : S * (CFC.log (c • S) - CFC.log (c • T)) =
      S * (CFC.log S - CFC.log T) := by
    unfold CFC.log
    rw [hS.log_smul_of_ne_zero hc.ne', hT.isHermitian.log_smul_of_ne_zero hc.ne']
    change S * (Real.log c • cfc e S + cfc Real.log S -
      (Real.log c • cfc e T + cfc Real.log T)) = _
    simp only [hF, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, hE, Matrix.mul_one]
    abel
  simp only [relativeEntropyOfMatrices, Matrix.smul_mul, hInner, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]

section Weighted

variable {J : ι → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

omit [DecidableEq n] in
private theorem refine_traceNorm (w : ∀ i, J i → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (S : ι → Matrix n n ℂ) :
    traceNorm (joint (refinedBlocks w S)) = traceNorm (joint S) := by
  classical
  rw [traceNorm_joint, traceNorm_joint, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j : J i, traceNorm (w i j • S i)) = traceNorm (S i)
  have h (j : J i) : traceNorm (w i j • S i) = w i j * traceNorm (S i) := by
    exact traceNorm_smul_nonneg (S i) (w i j) (hw i j)
  simp_rw [h]
  rw [← Finset.sum_mul, hs, one_mul]

omit [DecidableEq n] in
/-- The Helstrom weighted difference has exactly the same trace norm for every
prior. Together with the trace-one hypotheses this gives equal binary Bayes risk. -/
theorem refine_binary_testing (w : ∀ i, J i → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (S T : ι → Matrix n n ℂ) (prior : ℝ) :
    traceNorm (prior • joint (refinedBlocks w S) - (1 - prior) • joint (refinedBlocks w T)) =
      traceNorm (prior • joint S - (1 - prior) • joint T) := by
  rw [← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_sub,
    ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_sub]
  have he : (prior • refinedBlocks w S - (1 - prior) • refinedBlocks w T) =
      refinedBlocks w (prior • S - (1 - prior) • T) := by
    funext q
    change prior • (w q.1 q.2 • S q.1) - (1 - prior) • (w q.1 q.2 • T q.1) =
      w q.1 q.2 • (prior • S q.1 - (1 - prior) • T q.1)
    rw [smul_sub, smul_comm prior, smul_comm (1 - prior)]
  rw [he, refine_traceNorm w hw hs]

/-- Ordinary Petz for the physical channel `partialTraceRight` with a faithful
reference and marginal. Tensoring with the identity is the trace adjoint. For
positive definite reference blocks, a nonempty flag set ensures faithfulness
of the marginal. -/
def partialTracePetz (τ : Matrix (n × ι) (n × ι) ℂ) (X : Matrix n n ℂ) :
    Matrix (n × ι) (n × ι) ℂ :=
  let Q := mpow τ (1 / 2)
  let P := mpow (partialTraceRight τ) (-(1 / 2))
  Q * lift (ι := ι) (P * X * P) * Q

def petzBlocks (T : ι → Matrix n n ℂ) (X : Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  let Q := mpow (T i) (1 / 2)
  let P := mpow (marginal T) (-(1 / 2))
  Q * (P * X * P) * Q

theorem partialTracePetz_joint (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (X : Matrix n n ℂ) :
    partialTracePetz (joint T) X = joint (petzBlocks T X) := by
  simp only [partialTracePetz, mpow_joint T (fun i => (hT i).isHermitian),
    lift_eq_joint, joint, ← Matrix.blockDiagonal_mul]
  rfl

/-- Ordinary Petz intertwines with refinement for every retained input matrix. -/
theorem refine_ordinaryPetz (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1)
    (X : Matrix n n ℂ) :
    partialTracePetz (joint (refinedBlocks w T)) X =
      joint (refinedBlocks w (petzBlocks T X)) := by
  rw [partialTracePetz_joint _ (refinedBlocks_posDef w hw T hT)]
  apply congrArg joint
  funext q
  simp only [petzBlocks, marginal_refined w hs, refinedBlocks]
  rw [mpow_smul_of_nonneg (hT q.1).posSemidef.nonneg (hw q.1 q.2).le (by norm_num)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Real.rpow_add (hw q.1 q.2), show (1 / 2 : ℝ) + (1 / 2) = 1 by norm_num, Real.rpow_one]

/-- Equality of the actual trace-norm ordinary-Petz recovery error. -/
theorem refine_petz_error (S T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1) :
    traceNorm (joint (refinedBlocks w S) -
      partialTracePetz (joint (refinedBlocks w T)) (marginal (refinedBlocks w S))) =
    traceNorm (joint S - partialTracePetz (joint T) (marginal S)) := by
  rw [marginal_refined w hs, refine_ordinaryPetz T hT w hw hs, partialTracePetz_joint T hT,
    ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_sub]
  have he : refinedBlocks w S - refinedBlocks w (petzBlocks T (marginal S)) =
      refinedBlocks w (S - petzBlocks T (marginal S)) := by
    funext q
    exact (smul_sub _ _ _).symm
  rw [he, refine_traceNorm w (fun i j => (hw i j).le) hs]


/-- The joint relative entropy and the actual partial-trace loss are invariant.
The input S may have a kernel. -/
theorem refine_entropy_loss (S T : ι → Matrix n n ℂ)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ i, (T i).PosDef)
    (w : ∀ i, J i → ℝ) (hw : ∀ i j, 0 < w i j) (hs : ∀ i, ∑ j, w i j = 1) :
    relativeEntropyOfMatrices (joint (refinedBlocks w S)) (joint (refinedBlocks w T)) =
        relativeEntropyOfMatrices (joint S) (joint T) ∧
    partialTraceEntropyLoss (refinedBlocks w S) (refinedBlocks w T) =
        partialTraceEntropyLoss S T := by
  have hJoint :
      relativeEntropyOfMatrices (joint (refinedBlocks w S)) (joint (refinedBlocks w T)) =
        relativeEntropyOfMatrices (joint S) (joint T) := by
    rw [relativeEntropyOfMatrices_joint (refinedBlocks w S) (refinedBlocks w T)
      (fun q => ((hS q.1).smul (hw q.1 q.2).le).isHermitian)
      (fun q => ((hT q.1).smul (hw q.1 q.2)).isHermitian),
      relativeEntropyOfMatrices_joint S T (fun i => (hS i).isHermitian)
        (fun i => (hT i).isHermitian), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j : J i, relativeEntropyOfMatrices (w i j • S i) (w i j • T i)) = _
    simp_rw [relativeEntropyOfMatrices_smul _ _ (hS i).isHermitian (hT i) (hw i _)]
    rw [← Finset.sum_mul, hs, one_mul]
  exact ⟨hJoint, by simp only [partialTraceEntropyLoss, hJoint, marginal_refined w hs]⟩

end Weighted
end D5.S3.Quantum.Recovery.BKMFlagRefinement
