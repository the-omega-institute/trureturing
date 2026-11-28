/- GID: D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-flag Gibbs root fidelity is a normalized sum of block trace norms. -/

import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

/-! # Ordinary Petz and root fidelity for two flags over a qutrit -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm re_trace_eq_trace)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance (traceNorm_conjTranspose)
open D5.S3.Quantum.Recovery.BKMFlagRefinement
  (joint marginal lift marginal_eq_sum lift_eq_joint joint_posDef cfc_joint mpow_joint
    partialTracePetz petzBlocks partialTracePetz_joint traceNorm_joint)

namespace D5.S3.Quantum.Recovery.GibbsOverlap.PetzFlagPhysicalOverlap

local notation "Qutrit" => Matrix (Fin 3) (Fin 3) ℂ
abbrev Joint := Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ

def mixedQutrit : Qutrit := (1 / 3 : ℝ) • (1 : Qutrit)

def inputJoint (Q : Qutrit) : Joint :=
  joint (fun _ : Fin 2 => (1 / 2 : ℝ) • Q)

private def referenceBlocks (D : Fin 2 → Qutrit) (i : Fin 2) : Qutrit :=
  (1 / 3 : ℝ) • D i

def referenceJoint (D : Fin 2 → Qutrit) : Joint := joint (referenceBlocks D)

theorem input_marginal (Q : Qutrit) : partialTraceRight (inputJoint Q) = Q := by
  change marginal (fun _ : Fin 2 => (1 / 2 : ℝ) • Q) = Q
  rw [marginal_eq_sum, Fin.sum_univ_two, ← add_smul]
  norm_num

theorem reference_marginal (D : Fin 2 → Qutrit) (hsum : ∑ i, D i = 1) :
    partialTraceRight (referenceJoint D) = mixedQutrit := by
  change marginal (referenceBlocks D) = _
  rw [marginal_eq_sum]
  change (∑ i, (1 / 3 : ℝ) • D i) = (1 / 3 : ℝ) • (1 : Qutrit)
  rw [← Finset.smul_sum, hsum]

theorem input_faithful_density (Q : Qutrit) (hQ : Q.PosDef) (htr : Q.trace = 1) :
    (inputJoint Q).PosDef ∧ (inputJoint Q).trace = 1 := by
  refine ⟨joint_posDef _ (fun _ => hQ.smul (by norm_num : (0 : ℝ) < 1 / 2)), ?_⟩
  rw [← trace_partialTraceRight, input_marginal, htr]

private theorem referenceBlocks_posDef (D : Fin 2 → Qutrit)
    (hD : ∀ i, (D i).PosDef) (i : Fin 2) : (referenceBlocks D i).PosDef :=
  (hD i).smul (by norm_num : (0 : ℝ) < 1 / 3)

theorem reference_faithful_density (D : Fin 2 → Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    (referenceJoint D).PosDef ∧ (referenceJoint D).trace = 1 := by
  refine ⟨joint_posDef _ (referenceBlocks_posDef D hD), ?_⟩
  rw [← trace_partialTraceRight, reference_marginal D hsum]
  norm_num [mixedQutrit, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]

private theorem mpow_half {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : 0 ≤ A) : mpow A (1 / 2) = CFC.sqrt A := by
  rw [mpow, CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA]

private theorem sqrt_joint {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (T : ι → Matrix n n ℂ) (hT : ∀ i, (T i).PosDef) :
    CFC.sqrt (joint T) = joint (fun i => CFC.sqrt (T i)) := by
  rw [← mpow_half (joint_posDef T hT).posSemidef.nonneg,
    mpow_joint T (fun i => (hT i).isHermitian)]
  apply congrArg joint
  funext i
  exact mpow_half (hT i).posSemidef.nonneg

private theorem mpow_mixed (p : ℝ) :
    mpow mixedQutrit p = ((1 / 3 : ℝ) ^ p) • (1 : Qutrit) := by
  simp only [mixedQutrit, mpow, ← Algebra.algebraMap_eq_smul_one, cfc_algebraMap]

private def recoveredBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  CFC.sqrt (D i) * Q * CFC.sqrt (D i)

/-- Recovery by the ordinary Petz map applied to the actual partial trace of the input. -/
private theorem partialTracePetz_eq_joint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q)) =
      joint (recoveredBlocks D Q) := by
  rw [input_marginal, referenceJoint, partialTracePetz_joint _ (referenceBlocks_posDef D hD)]
  apply congrArg joint
  funext i
  have hm : marginal (referenceBlocks D) = mixedQutrit := reference_marginal D hsum
  have hc : (0 : ℝ) < 1 / 3 := by norm_num
  have hroot := mpow_smul_of_nonneg (hD i).posSemidef.nonneg hc.le
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change mpow ((1 / 3 : ℝ) • D i) (1 / 2) *
    (mpow (marginal (referenceBlocks D)) (-(1 / 2)) * Q *
      mpow (marginal (referenceBlocks D)) (-(1 / 2))) *
    mpow ((1 / 3 : ℝ) • D i) (1 / 2) = recoveredBlocks D Q i
  rw [hm, mpow_mixed, hroot, mpow_half (hD i).posSemidef.nonneg]
  let s : ℝ := (1 / 3 : ℝ) ^ (1 / 2 : ℝ)
  let t : ℝ := (1 / 3 : ℝ) ^ (-(1 / 2) : ℝ)
  let S : Qutrit := CFC.sqrt (D i)
  have hst : s * t = 1 := by
    dsimp only [s, t]
    rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero]
  have hts : t * s = 1 := (mul_comm t s).trans hst
  have hleft : (s • S) * (t • (1 : Qutrit)) = S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hst, one_smul]
  have hright : (t • (1 : Qutrit)) * (s • S) = S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hts, one_smul]
  change (s • S) * ((t • (1 : Qutrit)) * Q * (t • (1 : Qutrit))) * (s • S) =
    S * Q * S
  calc
    _ = ((s • S) * (t • (1 : Qutrit))) * Q * ((t • (1 : Qutrit)) * (s • S)) := by
      simp only [Matrix.mul_assoc]
    _ = S * Q * S := by rw [hleft, hright]

private theorem recoveredBlocks_posDef (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hQ : Q.PosDef) (i : Fin 2) :
    (recoveredBlocks D Q i).PosDef := by
  have hS := (hD i).isStrictlyPositive.sqrt.posDef
  have h := (hS.isUnit.posDef_star_right_conjugate_iff).mpr hQ
  simpa only [recoveredBlocks, hS.isHermitian.star_eq] using h

theorem recovered_faithful_density (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1)
    (hQ : Q.PosDef) (htr : Q.trace = 1) :
    let P := partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))
    P.PosDef ∧ P.trace = 1 := by
  dsimp only
  rw [partialTracePetz_eq_joint D Q hD hsum]
  refine ⟨joint_posDef _ (recoveredBlocks_posDef D Q hD hQ), ?_⟩
  have hblock (i : Fin 2) : (recoveredBlocks D Q i).trace = (Q * D i).trace := by
    rw [recoveredBlocks, Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self _ (hD i).posSemidef.nonneg, Matrix.trace_mul_comm (D i) Q]
  rw [Matrix.trace_blockDiagonal]
  simp_rw [hblock]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hsum, Matrix.mul_one, htr]

/-- The unnormalized conditional Gibbs operator of the physical partial trace. -/
def gibbsOperator (X T : Joint) : Joint :=
  NormedSpace.exp (CFC.log T +
    lift (CFC.log (partialTraceRight X) - CFC.log (partialTraceRight T)))

def normalizedGibbs (X T : Joint) : Joint :=
  (gibbsOperator X T).trace.re⁻¹ • gibbsOperator X T

def gibbsBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  NormedSpace.exp (CFC.log (D i) + CFC.log Q)

def partition (D : Fin 2 → Qutrit) (Q : Qutrit) : ℝ :=
  ∑ i, (gibbsBlocks D Q i).trace.re

private theorem blockHamiltonian_hermitian (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) :
    (CFC.log (D i) + CFC.log Q).IsHermitian :=
  IsSelfAdjoint.log.add IsSelfAdjoint.log

private theorem gibbsBlocks_posDef (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) :
    (gibbsBlocks D Q i).PosDef := by
  unfold gibbsBlocks
  have hnonneg := (blockHamiltonian_hermitian D Q i).isSelfAdjoint.exp_nonneg
  exact hnonneg.posSemidef.posDef_iff_isUnit.mpr (Matrix.isUnit_exp _)

private theorem partition_pos (D : Fin 2 → Qutrit) (Q : Qutrit) : 0 < partition D Q := by
  exact Finset.sum_pos (fun i _ => (Complex.pos_iff.mp (gibbsBlocks_posDef D Q i).trace_pos).1)
    Finset.univ_nonempty

private theorem log_mixed :
    CFC.log mixedQutrit = algebraMap ℝ Qutrit (Real.log (1 / 3)) := by
  rw [mixedQutrit, ← Algebra.algebraMap_eq_smul_one, CFC.log_algebraMap]

private theorem gibbsOperator_eq_joint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    gibbsOperator (inputJoint Q) (referenceJoint D) = joint (gibbsBlocks D Q) := by
  let H : Fin 2 → Qutrit := fun i => CFC.log (D i) + CFC.log Q
  have hH (i : Fin 2) : (H i).IsHermitian := blockHamiltonian_hermitian D Q i
  have hlog : CFC.log (referenceJoint D) =
      joint (fun i => CFC.log (referenceBlocks D i)) :=
    cfc_joint Real.log (referenceBlocks D) (fun i => (referenceBlocks_posDef D hD i).isHermitian)
  have hHamiltonian :
      CFC.log (referenceJoint D) + lift (CFC.log (partialTraceRight (inputJoint Q)) -
        CFC.log (partialTraceRight (referenceJoint D))) = joint H := by
    rw [input_marginal, reference_marginal D hsum, hlog, lift_eq_joint,
      ← Matrix.blockDiagonal_add]
    apply congrArg joint
    funext i
    change CFC.log ((1 / 3 : ℝ) • D i) +
      (CFC.log Q - CFC.log mixedQutrit) = CFC.log (D i) + CFC.log Q
    rw [CFC.log_smul' _ (by norm_num : (0 : ℝ) < 1 / 3) (hD i).isStrictlyPositive, log_mixed]
    abel
  have hJoint : (joint H).IsHermitian := Matrix.isHermitian_blockDiagonal_iff.mpr hH
  rw [gibbsOperator, hHamiltonian, ← CFC.real_exp_eq_normedSpace_exp hJoint.isSelfAdjoint,
    cfc_joint Real.exp H hH]
  apply congrArg joint
  funext i
  exact CFC.real_exp_eq_normedSpace_exp (hH i).isSelfAdjoint

theorem gibbsOperator_trace (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    (gibbsOperator (inputJoint Q) (referenceJoint D)).trace.re = partition D Q := by
  rw [gibbsOperator_eq_joint D Q hD hsum, Matrix.trace_blockDiagonal,
    Complex.re_sum, partition]

private theorem normalizedGibbs_eq_scaledJoint (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    normalizedGibbs (inputJoint Q) (referenceJoint D) =
      (partition D Q)⁻¹ • joint (gibbsBlocks D Q) := by
  rw [normalizedGibbs, gibbsOperator_trace D Q hD hsum, gibbsOperator_eq_joint D Q hD hsum]

theorem normalizedGibbs_faithful_density (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) :
    let G := normalizedGibbs (inputJoint Q) (referenceJoint D)
    G.PosDef ∧ G.trace = 1 := by
  dsimp only
  rw [normalizedGibbs_eq_scaledJoint D Q hD hsum]
  have hG := joint_posDef _ (gibbsBlocks_posDef D Q)
  have hZ := partition_pos D Q
  refine ⟨hG.smul (inv_pos.mpr hZ), ?_⟩
  have hre : (joint (gibbsBlocks D Q)).trace.re = partition D Q := by
    rw [Matrix.trace_blockDiagonal, Complex.re_sum, partition]
  have hcast : (↑(partition D Q) : ℂ) = (joint (gibbsBlocks D Q)).trace := by
    rw [← hre]
    exact re_trace_eq_trace hG.isHermitian
  rw [Matrix.trace_smul, ← hcast, Complex.real_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hZ.ne', Complex.ofReal_one]

def polarBlocks (D : Fin 2 → Qutrit) (Q : Qutrit) (i : Fin 2) : Qutrit :=
  CFC.sqrt (gibbsBlocks D Q i) * CFC.sqrt (D i) * CFC.sqrt Q

private theorem sqrt_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : 0 ≤ A) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • A) = Real.sqrt c • CFC.sqrt A := by
  rw [← mpow_half (smul_nonneg hc hA), mpow_smul_of_nonneg hA hc (by norm_num),
    mpow_half hA, Real.sqrt_eq_rpow]

private theorem recovered_eq_polar_gram (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hQ : Q.PosDef) (i : Fin 2) :
    CFC.sqrt (gibbsBlocks D Q i) * recoveredBlocks D Q i *
        CFC.sqrt (gibbsBlocks D Q i) =
      polarBlocks D Q i * (polarBlocks D Q i)ᴴ := by
  let R := CFC.sqrt (gibbsBlocks D Q i)
  let S := CFC.sqrt (D i)
  let T := CFC.sqrt Q
  have root_star (A : Qutrit) : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hGram : (R * S * T) * (R * S * T)ᴴ = R * (S * Q * S) * R := by
    simp only [Matrix.conjTranspose_mul, R, S, T, root_star, Matrix.mul_assoc]
    change R * (S * (T * (T * (S * R)))) = R * (S * (Q * (S * R)))
    rw [← Matrix.mul_assoc T T, CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg]
  exact hGram.symm

private theorem rootFidelity_physical (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) (hQ : Q.PosDef) :
    rootFidelity (normalizedGibbs (inputJoint Q) (referenceJoint D))
      (partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))) =
      (∑ i, traceNorm (polarBlocks D Q i)) / Real.sqrt (partition D Q) := by
  have hG := joint_posDef _ (gibbsBlocks_posDef D Q)
  have hZ := partition_pos D Q
  let B : Joint := joint (polarBlocks D Q)
  let s := Real.sqrt ((partition D Q)⁻¹)
  have hgram : (joint (fun i => CFC.sqrt (gibbsBlocks D Q i))) *
      joint (recoveredBlocks D Q) * joint (fun i => CFC.sqrt (gibbsBlocks D Q i)) =
      B * Bᴴ := by
    simp only [B, joint, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    exact congrArg Matrix.blockDiagonal (funext (recovered_eq_polar_gram D Q hQ))
  have hscaled : s • (s • (B * Bᴴ)) = (s • B) * (s • B)ᴴ := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
  rw [rootFidelity, normalizedGibbs_eq_scaledJoint D Q hD hsum,
    partialTracePetz_eq_joint D Q hD hsum,
    sqrt_smul hG.posSemidef.nonneg (inv_nonneg.mpr hZ.le),
    sqrt_joint _ (gibbsBlocks_posDef D Q)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hgram]
  change (CFC.sqrt (s • (s • (B * Bᴴ)))).trace.re = _
  rw [hscaled]
  have hnorm : (CFC.sqrt ((s • B) * (s • B)ᴴ)).trace.re = traceNorm (s • B) := by
    rw [← traceNorm_conjTranspose (s • B)]
    simp only [Foundation.FiniteTraceDistance.traceNorm, Matrix.conjTranspose_conjTranspose,
      RCLike.re_eq_complex_re]
  rw [hnorm, ← Complex.coe_smul,
    traceNorm_smul_nonneg _ _ (Real.sqrt_nonneg _), traceNorm_joint]
  rw [Real.sqrt_inv, div_eq_mul_inv, mul_comm]


/-- The strict sum-of-blocks deficit is exactly the strict root-fidelity failure. -/
theorem rootFidelity_lt_sqrt_partition_iff (D : Fin 2 → Qutrit) (Q : Qutrit)
    (hD : ∀ i, (D i).PosDef) (hsum : ∑ i, D i = 1) (hQ : Q.PosDef) :
    rootFidelity (normalizedGibbs (inputJoint Q) (referenceJoint D))
      (partialTracePetz (referenceJoint D) (partialTraceRight (inputJoint Q))) <
        Real.sqrt (partition D Q) ↔
      (∑ i, (traceNorm (polarBlocks D Q i) - (gibbsBlocks D Q i).trace.re)) < 0 := by
  have hZ := partition_pos D Q
  rw [rootFidelity_physical D Q hD hsum hQ, div_lt_iff₀ (Real.sqrt_pos.mpr hZ),
    ← pow_two (Real.sqrt (partition D Q)), Real.sq_sqrt hZ.le,
    Finset.sum_sub_distrib, sub_neg, partition]

end D5.S3.Quantum.Recovery.GibbsOverlap.PetzFlagPhysicalOverlap
