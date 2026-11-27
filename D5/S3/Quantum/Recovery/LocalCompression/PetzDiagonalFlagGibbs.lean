/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzDiagonalFlagGibbs
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzDiagonalFlagGibbs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical entropy splitting and ordinary Petz recovery for diagonal reference flags. -/

import D5.S3.Quantum.Recovery.QubitGibbsDeficit
import D5.S3.Quantum.Recovery.QubitActualResidualGeometry
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.ProcessReconstruction.PureDistance
import D5.S3.TotalVariation.Bhattacharyya

/-! # Gibbs loss and ordinary Petz recovery for diagonal reference flags -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder CStarAlgebra MatrixOrder InnerProductSpace
  Matrix Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary (fromLegacyDensityState)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMFlagRefinement
open D5.S3.Quantum.Recovery.QubitGibbsDeficit (conditionalLoss retainedMarginal)
open D5.S3.Quantum.Recovery.QubitResidualRounding (partialTraceRight_contract)
open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.TotalVariation.Bhattacharyya
open UnitaryReconstruction (euclidean_norm_one_of_dot traceNorm_pure_sub_le)

open private relativeEntropyOfMatrices_joint from D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
open private mat_log from D5.S3.Quantum.Recovery.QubitGibbsDeficit

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagGibbs

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

local notation "mat" => CStarMatrix.ofMatrix.symm

/-- A reference block in the common retained basis. -/
abbrev realDiagonal (s : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun j => (s j : ℂ))

/-- The diagonal entry of the normalized reference effect for flag `i`. -/
def effectWeight (s : ι → n → ℝ) (i : ι) (j : n) : ℝ :=
  s i j / ∑ k, s k j

private theorem marginal_diagonal (s : ι → n → ℝ) :
    marginal (fun i => realDiagonal (s i)) = realDiagonal (fun j => ∑ i, s i j) := by
  rw [marginal_eq_sum]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [realDiagonal, Matrix.sum_apply, Complex.ofReal_sum]
  · simp [realDiagonal, Matrix.sum_apply, Matrix.diagonal_apply, hjk]

private theorem effectWeight_sum (s : ι → n → ℝ)
    (hp : ∀ j, 0 < ∑ i, s i j) (j : n) :
    ∑ i, effectWeight s i j = 1 := by
  simp only [effectWeight, ← Finset.sum_div, div_self (hp j).ne']

private theorem diagonal_hermitian (s : n → ℝ) : (realDiagonal s).IsHermitian := by
  change (realDiagonal s)ᴴ = realDiagonal s
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  simp

private theorem sqrt_diagonal (s : n → ℝ) (hs : ∀ j, 0 ≤ s j) :
    CFC.sqrt (realDiagonal s) = realDiagonal (fun j => Real.sqrt (s j)) := by
  have hS : (realDiagonal s).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => Complex.nonneg_iff.mpr ⟨hs j, by simp⟩)
  rw [CFC.sqrt_eq_real_sqrt _ hS.nonneg,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]
  exact cfc_diagonal Real.sqrt s

/-- The partial-trace Petz formula gives the actual unrotated flag blocks, with
a faithful reference marginal and with zero entries allowed in each reference block. -/
theorem partialTracePetz_diagonal (s : ι → n → ℝ) (hs : ∀ i j, 0 ≤ s i j)
    (hp : ∀ j, 0 < ∑ i, s i j) (Q : Matrix n n ℂ) :
    partialTracePetz (joint (fun i => realDiagonal (s i))) Q =
      joint (fun i => CFC.sqrt (realDiagonal (effectWeight s i)) * Q *
        CFC.sqrt (realDiagonal (effectWeight s i))) := by
  let p : n → ℝ := fun j => ∑ i, s i j
  have hP : mpow (realDiagonal p) (-(1 / 2)) =
      realDiagonal (fun j => (Real.sqrt (p j))⁻¹) := by
    rw [mpow, cfc_diagonal]
    congr 1
    funext j
    rw [Real.rpow_neg (hp j).le, ← Real.sqrt_eq_rpow]
  have hS (i : ι) : mpow (realDiagonal (s i)) (1 / 2) =
      realDiagonal (fun j => Real.sqrt (s i j)) := by
    rw [mpow, cfc_diagonal]
    simp only [Real.sqrt_eq_rpow]
  have hfactor (i : ι) :
      realDiagonal (fun j => Real.sqrt (s i j)) *
          realDiagonal (fun j => (Real.sqrt (p j))⁻¹) =
        CFC.sqrt (realDiagonal (effectWeight s i)) := by
    rw [Matrix.diagonal_mul_diagonal, sqrt_diagonal _
      (fun j => div_nonneg (hs i j) (hp j).le)]
    congr 1
    funext j
    rw [effectWeight, Real.sqrt_div (hs i j), div_eq_mul_inv, Complex.ofReal_mul,
      Complex.ofReal_inv]
  have hcomm (i : ι) :
      Commute (realDiagonal (fun j => (Real.sqrt (p j))⁻¹))
        (realDiagonal (fun j => Real.sqrt (s i j))) := by
    show _ * _ = _ * _
    simp only [Matrix.diagonal_mul_diagonal, mul_comm]
  unfold partialTracePetz
  change mpow (joint (fun i => realDiagonal (s i))) (1 / 2) *
      lift (mpow (marginal (fun i => realDiagonal (s i))) (-(1 / 2)) * Q *
        mpow (marginal (fun i => realDiagonal (s i))) (-(1 / 2))) *
      mpow (joint (fun i => realDiagonal (s i))) (1 / 2) = _
  rw [mpow_joint _ (fun i => diagonal_hermitian (s i)), marginal_diagonal,
    hP, lift_eq_joint]
  simp only [hS, joint, ← Matrix.blockDiagonal_mul]
  congr 1
  funext i
  let A := realDiagonal (fun j => Real.sqrt (s i j))
  let B := realDiagonal (fun j => (Real.sqrt (p j))⁻¹)
  change A * (B * Q * B) * A = _
  calc
    _ = (A * B) * Q * (B * A) := by simp only [mul_assoc]
    _ = _ := by rw [(hcomm i).eq, hfactor i]

private theorem trace_mul_log_diagonal (X : Matrix n n ℂ) (a : n → ℝ) :
    (X * CFC.log (realDiagonal a)).trace.re = ∑ j, (X j j).re * Real.log (a j) := by
  change (X * cfc Real.log (realDiagonal a)).trace.re = _
  rw [cfc_diagonal]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The marginal logarithm cancels inside the physical trace-log loss. A zero
reference coordinate contributes zero when the corresponding alternative
diagonal entry vanishes. The alternative blocks need only be Hermitian. -/
theorem partialTraceEntropyLoss_diagonal (X : ι → Matrix n n ℂ)
    (s : ι → n → ℝ) (hX : ∀ i, (X i).IsHermitian) (hs : ∀ i j, 0 ≤ s i j)
    (hp : ∀ j, 0 < ∑ i, s i j)
    (hzero : ∀ i j, s i j = 0 → X i j j = 0) :
    partialTraceEntropyLoss X (fun i => realDiagonal (s i)) =
      ∑ i, (X i * (CFC.log (X i) - (CFC.log (marginal X) +
        CFC.log (realDiagonal (effectWeight s i))))).trace.re := by
  have hcross (i : ι) :
      (X i * CFC.log (realDiagonal (s i))).trace.re =
        (X i * CFC.log (realDiagonal (fun j => ∑ k, s k j))).trace.re +
        (X i * CFC.log (realDiagonal (effectWeight s i))).trace.re := by
    simp only [trace_mul_log_diagonal, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hpos : 0 < s i j
    · rw [effectWeight, Real.log_div hpos.ne' (hp j).ne']
      ring
    · have hz : s i j = 0 := le_antisymm (le_of_not_gt hpos) (hs i j)
      simp [hzero i j hz]
  have hsum (L : Matrix n n ℂ) :
      ((∑ i, X i) * L).trace.re = ∑ i, (X i * L).trace.re := by
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  unfold partialTraceEntropyLoss
  rw [relativeEntropyOfMatrices_joint X _ hX (fun i => diagonal_hermitian (s i)),
    marginal_diagonal, marginal_eq_sum X]
  simp only [relativeEntropyOfMatrices, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re, hcross, hsum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

private theorem finiteEntropy_matrix {m : Type*} [Fintype m] [DecidableEq m]
    (ρ τ : DensityState m) :
    finiteTraceLogRelativeEntropy ρ τ = relativeEntropyOfMatrices (mat ρ.1) (mat τ.1) := by
  unfold relativeEntropyOfMatrices
  change ((mat ρ.1) * (mat (CFC.log ρ.1) - mat (CFC.log τ.1))).trace.re = _
  rw [mat_log ρ, mat_log τ]

private theorem physicalLoss_eq_blockLoss
    (ρ τ : DensityState (Fin 2 × ι)) (X S : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : mat ρ.1 = joint X) (hτ : mat τ.1 = joint S) :
    conditionalLoss ρ τ = partialTraceEntropyLoss X S := by
  have hρm : mat (retainedMarginal ρ).1 = marginal X := by
    change partialTraceRight (mat ρ.1) = marginal X
    rw [hρ]
  have hτm : mat (retainedMarginal τ).1 = marginal S := by
    change partialTraceRight (mat τ.1) = marginal S
    rw [hτ]
  simp only [conditionalLoss, finiteEntropy_matrix, hρ, hτ, hρm, hτm,
    partialTraceEntropyLoss]

private theorem supported_diagonal_entry {m : Type*} [Fintype m] [DecidableEq m]
    {ρ τ : DensityState m} (hs : SupportContained ρ τ) (a : m)
    (hz : ∀ b, mat τ.1 b a = 0) : mat ρ.1 a a = 0 := by
  have hv : mat τ.1 *ᵥ Pi.single a 1 = 0 := by
    rw [Matrix.mulVec_single_one]
    exact funext hz
  have h := hs (show Pi.single a 1 ∈ matrixNullspace τ.1 from hv)
  change mat ρ.1 *ᵥ Pi.single a 1 = 0 at h
  rw [Matrix.mulVec_single_one] at h
  exact congrFun h a

private theorem supported_flag_diagonal_entry
    {ρ τ : DensityState (n × ι)} {X : ι → Matrix n n ℂ} {s : ι → n → ℝ}
    (hρ : mat ρ.1 = joint X) (hτ : mat τ.1 = joint (fun i => realDiagonal (s i)))
    (hSupport : SupportContained ρ τ) (i : ι) (j : n) (hz : s i j = 0) :
    X i j j = 0 := by
  have hzCol (b : n × ι) : mat τ.1 b (j, i) = 0 := by
    obtain ⟨k, l⟩ := b
    rw [hτ]
    by_cases hli : l = i
    · subst l
      simp [Matrix.blockDiagonal_apply_eq, Matrix.diagonal_apply, hz]
    · simp [Matrix.blockDiagonal_apply, hli]
  simpa only [hρ, Matrix.blockDiagonal_apply_eq] using
    supported_diagonal_entry hSupport (j, i) hzCol

/-- The Gibbs field on the actual joint space. -/
def gibbsField (s : ι → n → ℝ) (Q : Matrix n n ℂ) : CStarMatrix (n × ι) (n × ι) ℂ :=
  CStarMatrix.ofMatrix (joint (fun i => CFC.log Q + CFC.log (realDiagonal (effectWeight s i))))

theorem gibbsField_selfAdjoint (s : ι → n → ℝ) (Q : Matrix n n ℂ) :
    IsSelfAdjoint (gibbsField s Q) := by
  have h : (joint (fun i => CFC.log Q + CFC.log (realDiagonal (effectWeight s i)))).IsHermitian :=
    Matrix.isHermitian_blockDiagonal_iff.mpr
      (fun i => (IsSelfAdjoint.log (a := Q)).add
        (IsSelfAdjoint.log (a := realDiagonal (effectWeight s i))))
  exact h.isSelfAdjoint.map CStarMatrix.ofMatrixStarAlgEquiv

/-- The normalized Gibbs comparison on the physical qubit-flag state has
relative entropy equal to the actual partial-trace loss plus log partition.
Support inclusion allows zero reference coordinates. At singular inputs the
field uses the finite trace-log convention, with log zero set to zero. -/
theorem physical_gibbs_entropy_split [Nonempty ι]
    (ρ τ : DensityState (Fin 2 × ι)) (X : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ι → Fin 2 → ℝ)
    (hρ : mat ρ.1 = joint X) (hτ : mat τ.1 = joint (fun i => realDiagonal (s i)))
    (hX : ∀ i, (X i).IsHermitian) (hs : ∀ i j, 0 ≤ s i j)
    (hp : ∀ j, 0 < ∑ i, s i j) (hSupport : SupportContained ρ τ) :
    let H := gibbsField s (marginal X)
    let ω := fromLegacyDensityState (gibbsState H (gibbsField_selfAdjoint s (marginal X)))
    finiteTraceLogRelativeEntropy ρ ω = conditionalLoss ρ τ +
      Real.log (partitionFunction H) := by
  dsimp only
  let L : ι → Matrix (Fin 2) (Fin 2) ℂ := fun i =>
    CFC.log (marginal X) + CFC.log (realDiagonal (effectWeight s i))
  let H := gibbsField s (marginal X)
  let ω := fromLegacyDensityState (gibbsState H (gibbsField_selfAdjoint s (marginal X)))
  let z := Real.log (partitionFunction H)
  change finiteTraceLogRelativeEntropy ρ ω = conditionalLoss ρ τ + z
  have hlog : CFC.log (mat ω.1) = joint L - z • 1 := by
    rw [← mat_log]
    have hl := congrArg CStarMatrix.ofMatrix.symm
      (log_gibbs_state H (gibbsField_selfAdjoint s (marginal X)))
    change mat (CFC.log ω.1) = mat (H - z • 1) at hl
    exact hl
  have htrace : (joint X).trace = 1 := by
    rw [← hρ]
    exact ρ.trace_eq_one
  rw [physicalLoss_eq_blockLoss ρ τ X _ hρ hτ, partialTraceEntropyLoss_diagonal X s hX hs hp
      (supported_flag_diagonal_entry hρ hτ hSupport), finiteEntropy_matrix, hρ]
  change ((joint X) * (CFC.log (joint X) - CFC.log (mat ω.1))).trace.re =
    (∑ i, (X i * (CFC.log (X i) - L i)).trace.re) + z
  rw [hlog, show CFC.log (joint X) = joint (fun i => CFC.log (X i)) from
    cfc_joint Real.log X hX]
  rw [show joint (fun i => CFC.log (X i)) - (joint L - z • 1) =
      (joint (fun i => CFC.log (X i)) - joint L) + z • 1 by abel,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Complex.add_re,
    Matrix.trace_smul, htrace]
  simp only [← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul, joint,
    Matrix.trace_blockDiagonal, Complex.re_sum, Complex.smul_re, Complex.one_re,
    smul_eq_mul, mul_one]

private def outer {m : Type*} (v : m → ℂ) : Matrix m m ℂ :=
  vecMulVec v (star v)

private theorem conj_mul_self (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  simpa only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using Complex.conj_mul' z

private theorem mul_conj_self (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, conj_mul_self]

private theorem outer_idempotent (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    outer v * outer v = outer v := by
  simp only [outer, Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]

private theorem log_smul_outer (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (t : ℝ) :
    CFC.log (t • outer v) = Real.log t • outer v := by
  let P := outer v
  have hP : P.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  change cfc Real.log (t • P) = _
  rw [← cfc_comp_const_mul t Real.log P
    (hf := ((P.finite_real_spectrum).image _).continuousOn _) (ha := hP)]
  calc
    _ = cfc (fun r : ℝ => Real.log t * r) P := by
      apply cfc_congr
      intro r hr
      have hr' := (isIdempotentElem_iff_spectrum_subset ℝ P hP).mp
        (outer_idempotent v hv) hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr'
      rcases hr' with rfl | rfl <;> simp
    _ = _ := by
      rw [cfc_const_mul (Real.log t) (fun r : ℝ => r) P, cfc_id' ℝ P]

/-- Keeping a copy of the flag labels in an auxiliary register purifies the
direct sum of the outer products. -/
private def flagVector (a : ι → n → ℝ) (ψ : n → ℂ) (z : (n × ι) × ι) : ℂ :=
  if z.1.2 = z.2 then (a z.1.2 z.1.1 : ℂ) * ψ z.1.1 else 0

private theorem partialTrace_flagVector (a : ι → n → ℝ) (ψ : n → ℂ) :
    partialTraceRight (outer (flagVector a ψ)) =
      joint (fun i => outer (fun j => (a i j : ℂ) * ψ j)) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  change (∑ e, flagVector a ψ ((j, i), e) * star (flagVector a ψ ((k, l), e))) =
    joint (fun i => outer (fun j => (a i j : ℂ) * ψ j)) (j, i) (k, l)
  rw [Finset.sum_eq_single i]
  · by_cases hil : i = l
    · subst l
      simp [flagVector, outer, Matrix.blockDiagonal_apply_eq, Matrix.vecMulVec_apply]
    · simp [flagVector, Matrix.blockDiagonal_apply, hil, Ne.symm hil]
  · intro e _ he
    simp [flagVector, Ne.symm he]
  · simp

private theorem flagVector_pairing (a b : ι → n → ℝ) (ψ : n → ℂ) :
    star (flagVector a ψ) ⬝ᵥ flagVector b ψ =
      ((∑ j, ∑ i, a i j * b i j * Complex.normSq (ψ j) : ℝ) : ℂ) := by
  rw [dotProduct, Fintype.sum_prod_type, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [flagVector, if_pos rfl, Pi.star_apply, star_mul,
      Complex.star_def, Complex.conj_ofReal]
    change (star (ψ j) * (a i j : ℂ)) * ((b i j : ℂ) * ψ j) = _
    calc
      _ = (a i j : ℂ) * (b i j : ℂ) * (star (ψ j) * ψ j) := by ring
      _ = _ := by rw [conj_mul_self]
  · intro e _ he
    simp [flagVector, Ne.symm he]
  · simp

private theorem outer_flag_scale (a : ℝ) (ψ : n → ℂ) :
    outer (fun j => (a : ℂ) * ψ j) = a ^ 2 • outer ψ := by
  ext j k
  simp only [outer, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.smul_apply, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_pow]
  ring

private theorem outer_diagonal_action (a : n → ℝ) (ψ : n → ℂ) :
    realDiagonal a * outer ψ * realDiagonal a =
      outer (fun j => (a j : ℂ) * ψ j) := by
  ext j k
  simp only [outer, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem sqrt_diagonal_mulVec (a : n → ℝ) (ha : ∀ j, 0 ≤ a j) (ψ : n → ℂ) :
    CFC.sqrt (realDiagonal a) *ᵥ ψ = fun j => (Real.sqrt (a j) : ℂ) * ψ j := by
  rw [sqrt_diagonal a ha]
  funext j
  exact Matrix.mulVec_diagonal _ _ j

/-- Ordinary Petz returns the outer product of the square-root effect applied
to the retained vector in each flag. -/
theorem partialTracePetz_diagonal_outer (s : ι → n → ℝ) (hs : ∀ i j, 0 ≤ s i j)
    (hp : ∀ j, 0 < ∑ i, s i j) (ψ : n → ℂ) :
    partialTracePetz (joint (fun i => realDiagonal (s i))) (vecMulVec ψ (star ψ)) =
      joint (fun i =>
        let v := CFC.sqrt (realDiagonal (effectWeight s i)) *ᵥ ψ
        vecMulVec v (star v)) := by
  rw [partialTracePetz_diagonal s hs hp]
  congr 1
  funext i
  change CFC.sqrt (realDiagonal (effectWeight s i)) * outer ψ *
    CFC.sqrt (realDiagonal (effectWeight s i)) =
    outer (CFC.sqrt (realDiagonal (effectWeight s i)) *ᵥ ψ)
  have hd : ∀ j, 0 ≤ effectWeight s i j := fun j => div_nonneg (hs i j) (hp j).le
  rw [sqrt_diagonal_mulVec _ hd ψ, sqrt_diagonal _ hd]
  exact outer_diagonal_action (fun j => Real.sqrt (effectWeight s i j)) ψ

/-- The exact diagonal-reference pure-state bound on the physical joint matrix.
The reference marginal is faithful. Joint support inclusion permits zero
flag weights, zero retained populations and singular reference blocks. -/
theorem pure_retained_petz_traceNorm_sq_le
    (ρ τ : DensityState (Fin 2 × ι)) (ψ : Fin 2 → ℂ) (x : ι → ℝ) (s : ι → Fin 2 → ℝ)
    (hρ : mat ρ.1 = joint (fun i => x i • vecMulVec ψ (star ψ)))
    (hτ : mat τ.1 = joint (fun i => realDiagonal (s i)))
    (hψ : star ψ ⬝ᵥ ψ = 1) (hx : ∀ i, 0 ≤ x i) (hxsum : ∑ i, x i = 1)
    (hs : ∀ i j, 0 ≤ s i j) (hp : ∀ j, 0 < ∑ i, s i j)
    (hSupport : SupportContained ρ τ) :
    conditionalLoss ρ τ =
      (∑ i, x i * Real.log (x i)) -
        ∑ i, ∑ j, x i * Complex.normSq (ψ j) * Real.log (effectWeight s i j) ∧
    traceNorm (mat ρ.1 - partialTracePetz (mat τ.1)
      (partialTraceRight (mat ρ.1))) ^ 2 ≤
      4 * (1 - Real.exp (-conditionalLoss ρ τ)) := by
  classical
  let Q := outer ψ
  let d := effectWeight s
  let u : Fin 2 → ℝ := fun j => Complex.normSq (ψ j)
  let X : ι → Matrix (Fin 2) (Fin 2) ℂ := fun i => x i • Q
  have hρX : mat ρ.1 = joint X := hρ
  have hQ : Q.PosSemidef := Matrix.posSemidef_vecMulVec_self_star ψ
  have hQdiag (j : Fin 2) : Q j j = (u j : ℂ) := mul_conj_self (ψ j)
  have hQtrace : Q.trace = 1 := by
    rw [outer, Matrix.trace_vecMulVec, dotProduct_comm, hψ]
  have hu (j : Fin 2) : 0 ≤ u j := Complex.normSq_nonneg _
  have husum : ∑ j, u j = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, hQdiag, ← Complex.ofReal_sum] at hQtrace
    exact_mod_cast hQtrace
  have hd (i : ι) (j : Fin 2) : 0 ≤ d i j := div_nonneg (hs i j) (hp j).le
  have hdsum (j : Fin 2) : ∑ i, d i j = 1 := effectWeight_sum s hp j
  have hXm : marginal X = Q := by
    rw [marginal_eq_sum]
    simp only [X, ← Finset.sum_smul, hxsum, one_smul]
  have hxdiag (i : ι) (j : Fin 2) : X i j j = ((x i * u j : ℝ) : ℂ) := by
    simp only [X, Matrix.smul_apply, hQdiag, Complex.real_smul, Complex.ofReal_mul]
  have hzero (i : ι) (j : Fin 2) (h : s i j = 0) : X i j j = 0 :=
    supported_flag_diagonal_entry hρX hτ hSupport i j h
  have hlogQ : CFC.log Q = 0 := by
    simpa only [one_smul, Real.log_one, zero_smul] using log_smul_outer ψ hψ 1
  have hfirst (i : ι) : (X i * CFC.log (X i)).trace.re = x i * Real.log (x i) := by
    change ((x i • Q) * CFC.log (x i • Q)).trace.re = _
    rw [log_smul_outer ψ hψ, Matrix.smul_mul, Matrix.mul_smul, outer_idempotent ψ hψ,
      Matrix.trace_smul, Matrix.trace_smul, hQtrace]
    simp [Complex.smul_re]
  have hloss : conditionalLoss ρ τ =
      (∑ i, x i * Real.log (x i)) - ∑ i, ∑ j, x i * u j * Real.log (d i j) := by
    rw [physicalLoss_eq_blockLoss ρ τ X _ hρX hτ,
      partialTraceEntropyLoss_diagonal X s (fun i => (hQ.smul (hx i)).isHermitian) hs hp hzero,
      hXm, hlogQ]
    simp only [zero_add, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hfirst,
      trace_mul_log_diagonal, hxdiag, Complex.ofReal_re, Finset.sum_sub_distrib]
  refine ⟨hloss, ?_⟩
  let p : Fin 2 × ι → ℝ := fun ji => x ji.2 * u ji.1
  let q : Fin 2 × ι → ℝ := fun ji => d ji.2 ji.1 * u ji.1
  have hpLaw : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 := by
    refine ⟨fun a => mul_nonneg (hx a.2) (hu a.1), ?_⟩
    simp only [p, Fintype.sum_prod_type, ← Finset.sum_mul, hxsum, one_mul, husum]
  have hqLaw : (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1 := by
    refine ⟨fun a => mul_nonneg (hd a.2 a.1) (hu a.1), ?_⟩
    simp only [q, Fintype.sum_prod_type, ← Finset.sum_mul, hdsum, one_mul, husum]
  have hac (a : Fin 2 × ι) (ha : q a = 0) : p a = 0 := by
    rcases mul_eq_zero.mp ha with hd0 | hu0
    · have hs0 : s a.2 a.1 = 0 := (div_eq_zero_iff.mp hd0).resolve_right (hp a.1).ne'
      have hz := (hxdiag a.2 a.1).symm.trans (hzero a.2 a.1 hs0)
      exact_mod_cast hz
    · simp [p, hu0]
  have hKL : klDivergence p q = conditionalLoss ρ τ := by
    rw [hloss, klDivergence, Fintype.sum_prod_type, Finset.sum_comm]
    have hterm (i : ι) (j : Fin 2) :
        p (j, i) * Real.log (p (j, i) / q (j, i)) =
          x i * u j * (Real.log (x i) - Real.log (d i j)) := by
      by_cases hz : p (j, i) = 0
      · change x i * u j = 0 at hz
        simp [p, hz]
      · have hx0 : x i ≠ 0 := fun h => hz (by simp [p, h])
        have hd0 : d i j ≠ 0 := fun h => hz (hac (j, i) (by simp [q, h]))
        have hu0 : u j ≠ 0 := fun h => hz (by simp [p, h])
        change x i * u j * Real.log ((x i * u j) / (d i j * u j)) = _
        rw [mul_div_mul_right _ _ hu0, Real.log_div hx0 hd0]
    have hxlog (i : ι) :
        ∑ j, x i * u j * Real.log (x i) = x i * Real.log (x i) := by
      rw [show (∑ j, x i * u j * Real.log (x i)) =
          ∑ j, (x i * Real.log (x i)) * u j from
        Finset.sum_congr rfl (fun j _ => mul_right_comm _ _ _)]
      rw [← Finset.mul_sum, husum, mul_one]
    simp only [hterm, mul_sub, Finset.sum_sub_distrib, hxlog]
  let a : ι → Fin 2 → ℝ := fun i _ => Real.sqrt (x i)
  let b : ι → Fin 2 → ℝ := fun i j => Real.sqrt (d i j)
  let v := flagVector a ψ
  let w := flagVector b ψ
  have ha2 (i : ι) (j : Fin 2) : a i j * a i j = x i := Real.mul_self_sqrt (hx i)
  have hb2 (i : ι) (j : Fin 2) : b i j * b i j = d i j := Real.mul_self_sqrt (hd i j)
  have hv : star v ⬝ᵥ v = 1 := by
    change star (flagVector a ψ) ⬝ᵥ flagVector a ψ = 1
    rw [flagVector_pairing]
    simpa only [ha2, p, Fintype.sum_prod_type, Complex.ofReal_one] using
      congrArg (fun t : ℝ => (t : ℂ)) hpLaw.2
  have hw : star w ⬝ᵥ w = 1 := by
    change star (flagVector b ψ) ⬝ᵥ flagVector b ψ = 1
    rw [flagVector_pairing]
    simpa only [hb2, q, Fintype.sum_prod_type, Complex.ofReal_one] using
      congrArg (fun t : ℝ => (t : ℂ)) hqLaw.2
  have huv : star v ⬝ᵥ w = (bhattacharyya p q : ℂ) := by
    change star (flagVector a ψ) ⬝ᵥ flagVector b ψ = (bhattacharyya p q : ℂ)
    rw [flagVector_pairing, bhattacharyya, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    change Real.sqrt (x i) * Real.sqrt (d i j) * u j =
      Real.sqrt ((x i * u j) * (d i j * u j))
    rw [Real.sqrt_mul (mul_nonneg (hx i) (hu j)), Real.sqrt_mul (hx i).le,
      Real.sqrt_mul (hd i j)]
    rw [show Real.sqrt (x i) * Real.sqrt (u j) * (Real.sqrt (d i j) * Real.sqrt (u j)) =
      Real.sqrt (x i) * Real.sqrt (d i j) * (Real.sqrt (u j) * Real.sqrt (u j)) by ring,
      Real.mul_self_sqrt (hu j)]
  have hXv : partialTraceRight (outer v) = joint X := by
    change partialTraceRight (outer (flagVector a ψ)) = joint X
    rw [partialTrace_flagVector]
    congr 1
    funext i
    change outer (fun j : Fin 2 => (Real.sqrt (x i) : ℂ) * ψ j) = x i • Q
    rw [outer_flag_scale, Real.sq_sqrt (hx i)]
  have hPw : partialTraceRight (outer w) =
      partialTracePetz (mat τ.1) (partialTraceRight (mat ρ.1)) := by
    change partialTraceRight (outer (flagVector b ψ)) =
      partialTracePetz (mat τ.1) (partialTraceRight (mat ρ.1))
    rw [partialTrace_flagVector, hτ, hρX]
    change joint _ = partialTracePetz (joint (fun i => realDiagonal (s i))) (marginal X)
    rw [hXm]
    change joint _ = partialTracePetz (joint (fun i => realDiagonal (s i)))
      (vecMulVec ψ (star ψ))
    rw [partialTracePetz_diagonal_outer s hs hp ψ]
    congr 1
    funext i
    change outer (fun j => (b i j : ℂ) * ψ j) =
      outer (CFC.sqrt (realDiagonal (d i)) *ᵥ ψ)
    rw [sqrt_diagonal_mulVec _ (hd i) ψ]
  let V : EuclideanSpace ℂ ((Fin 2 × ι) × ι) := WithLp.toLp 2 v
  let W : EuclideanSpace ℂ ((Fin 2 × ι) × ι) := WithLp.toLp 2 w
  have hvn : ‖V‖ = 1 := euclidean_norm_one_of_dot v hv
  have hwn : ‖W‖ = 1 := euclidean_norm_one_of_dot w hw
  have hinner : ⟪V, W⟫_ℂ = (bhattacharyya p q : ℂ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact huv
  have hB0 : 0 ≤ bhattacharyya p q := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hnorm : ‖⟪V, W⟫_ℂ‖ = bhattacharyya p q := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
  have hbound : traceNorm (outer w - outer v) ≤
      2 * Real.sqrt (1 - bhattacharyya p q ^ 2) := by
    simpa only [outer, hnorm] using traceNorm_pure_sub_le W V hwn hvn
  have hpartial : partialTraceRight (outer v - outer w) =
      partialTraceRight (outer v) - partialTraceRight (outer w) := by
    ext j k
    simp only [partialTraceRight, Matrix.sub_apply, Finset.sum_sub_distrib]
  have hcontract := partialTraceRight_contract (outer v - outer w)
    ((Matrix.posSemidef_vecMulVec_self_star v).isHermitian.sub
      (Matrix.posSemidef_vecMulVec_self_star w).isHermitian)
  rw [hpartial, hXv, hPw, ← hρX, ← neg_sub (outer w) (outer v),
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg] at hcontract
  have hExp := exp_neg_kl_divergence_le_bhattacharyya_sq p q hpLaw hqLaw.1 hac
  rw [hKL] at hExp
  have harg : 0 ≤ 1 - bhattacharyya p q ^ 2 := by
    have hB := pow_le_pow_left₀ hB0 (bhattacharyya_le_one p q hpLaw hqLaw) 2
    norm_num at hB
    linarith
  calc
    _ ≤ (2 * Real.sqrt (1 - bhattacharyya p q ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (traceNorm_nonneg _) (hcontract.trans hbound) 2
    _ = 4 * (1 - bhattacharyya p q ^ 2) := by
      rw [mul_pow, Real.sq_sqrt harg]
      norm_num
    _ ≤ _ := by linarith

end D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagGibbs
